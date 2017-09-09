open Printf
open Utils

module I = Intermediate
module P = String_of_intermediate
module CCmp = Compile_composite
module Stk_S = Compile_stack_store


type contract = {
  code: string;
  storage_init: string option;
  make_storage: string -> string;
}

let _DEBUG_ =true
let debug_indent = ref 0

let dup n = "D"^String.make n 'U'^"P"
let rec peek = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "DIP { %s }; SWAP" (peek (n-1))
let rec poke = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "SWAP; DIP { %s }" (poke (n-1))

(* Compose code instructions together in a signle line, with semicolon separators. *)
let cc x = String.concat "; " (List.filter ((<>) "") x)

let rec compile_etype t =
  let c = compile_etype in
  match t with
  | I.TPrim(t, []) -> t
  | I.TPrim(t, args) -> sprintf "(%s %s)" t (sep_list " " c args)
  | I.TLambda(params, result) -> sprintf "(lambda %s %s)" (sep_list " " c params) (c result)
  | I.TProduct(_, lazy []) -> "unit"
  | I.TProduct(_, lazy fields) -> CCmp.product_type (List.map c fields)
  | I.TSum(Some("bool", []), _) -> "bool"
  | I.TSum(Some("list", [t']), _) -> sprintf "(list %s)" (c t')
  | I.TSum(Some("option", [t']), _) -> sprintf "(option %s)" (c t')
  | I.TSum(_, lazy fields) -> Compile_composite.sum_type (List.map c fields)

type stack_item_kind = SAnon | SVar
type stack_item = (stack_item_kind * string * I.etype)
type stack = stack_item list

let item_e expr etype = (SAnon, String_of_intermediate.string_of_untyped_expr expr, etype)
let item_s str  etype = (SAnon, str, etype)
let item_v name etype = (SVar, name, etype)

let rec get_level stk v = match stk with
  | [] -> None
  | (SVar, v', _) :: _ when v=v' -> Some 1
  | _ :: stk' -> match get_level stk' v with None -> None | Some n -> Some (n+1)

let rec compile_typed_expr (stk:stack) ((ie, it as et): I.typed_expr) : (stack * string) =
  if _DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_untyped_expr ie);
    (* print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_expr ie); *)
    incr debug_indent
  end;
  let stk, code = match ie with
  | I.ELit x -> (match it with I.TPrim(t_name, []) -> 
    (item_e ie it) :: stk, sprintf "PUSH %s %s" t_name x | _ -> unsound "litteral type")
  | I.EId name -> begin match get_level stk name with
    | Some n -> (item_v name it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (item_e ie it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | I.EColl(Ast.CList, list) -> compile_EColl_CList stk list it
  | I.EColl(Ast.CMap,  list) -> compile_EColl_CMap  stk list it
  | I.EColl(Ast.CSet,  list) -> compile_EColl_CSet  stk list it
  | I.ELambda(params, body) -> compile_ELambda stk params body it (get_closure stk et)
  | I.ELet(v, et0, et1) ->
    let stk, c0 = compile_typed_expr stk et0 in
    let stk = (item_v v (snd et0)) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_typed_expr stk et1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, c0^"# let "^v^" = ... in ...\n"^c1^"DIP { DROP } # remove "^v^"\n"
  | I.EApp(f, args) -> compile_EApp stk f args it
  | I.EProduct [] -> (item_e ie it) :: stk, "UNIT"
  | I.EProduct fields ->
    let stk', code = List.fold_left
      (fun (stk, code) field -> let stk, code' = compile_typed_expr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (item_e ie it)::stk, code^Compile_composite.product_make(List.length fields)
  | I.ESum(i, n, content) -> compile_ESum stk i n content it
  | I.EProductGet(et0, i, n) ->
    let _, code = compile_typed_expr stk et0 in
    (item_e ie it)::stk, code^Compile_composite.product_get i n
  | I.EProductSet(et0, i, n, et1) ->
    let stk', c0 = compile_typed_expr stk et0 in
    let stk', c1 = compile_typed_expr stk et1 in (* TODO sure that the stask can't be messsed up? *)
    (item_e ie it)::stk, c0^c1^Compile_composite.product_set i n
  | I.EStoreSet(i, et0, et1) -> compile_EStoreSet stk i et0 et1
  | I.ESumCase(test, cases) -> compile_ESumCase stk test cases it
  in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let string_of_stk_item (k, v, t) = v in
  let comment = sep_list ":" string_of_stk_item stk in
  let code = if last_char='\n' then code else code^"; # "^comment^"\n" in
  stk, code


and compile_primitive stk name args t_result =

  let simple_primitives = [
    "self-now", "NOW"; "fail", "FAIL";
    "contract-create", "CREATE_CONTRACT"; "contract-create-account", "CREATE_ACCOUNT"; "contract-get", "DEFAULT_ACCOUNT"; "contract-manager", "MANAGER";
    "self-amount", "AMOUNT"; "self-contract", "SELF"; "self-balance", "BALANCE"; "self-steps-to-quota", "STEPS_TO_QUOTA";
    "crypto-hash", "H";
    "set-mem", "MEM"; "set-update", "UPDATE";
    "map-mem", "MEM"; "map-get", "GET"; "map-update", "UPDATE"; "map-map", "MAP";
    "list-map", "MAP";
    "EQ", "CMPEQ"; "NEQ", "CMPNEQ"; "LT", "CMPLT"; "LE", "CMPLE"; "GE", "CMPGE"; "GT", "CMPGT";
  ] in

  let simple_operators = [
    "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"; "AND"; "OR"; "XOR"; "CONCAT"] in

  let c_args args = (* Compiles and stacks all arguments, discards resulting stack. *)
    let stk, code = List.fold_right
      (fun arg (stk, c) -> let stk, c' = compile_typed_expr stk arg in stk, c^c')
      args (stk, "") in
    code in
  (*
  let c_arg level arg =
    let rec f stk = function 0 -> stk | n -> f (None::stk) (n-1) in
    compile_typed_expr (f stk level) arg in
  *)
  (*
  if args <> [] then begin match t with
    | I.TLambda(params, _) -> if List.length params > List.length args then
      unsupported "currying/partially applied primitive"
    | _ -> unsound "Applying a parameterless primitive"
  end;
  *)
  try
    let prim = List.assoc name simple_primitives in
    c_args args^prim
  with Not_found -> if List.mem name simple_operators then
    c_args args^name
  else match name with
    | "self-source" -> begin match t_result with
      | I.TPrim("contract", [param; result]) -> 
        "SOURCE "^compile_etype param^" "^compile_etype result
      | _ -> unsupported ("Cannot guess the type of contract parameters, please annotate")
      end
    | "crypto-check" ->
      begin match args with
      | [key; signature; msg] ->
        c_args args ^"DIP { PAIR }; CHECK_SIGNATURE" (* key->sig->str / key->sig*str *)
      | [_;_] | [_] | [] -> unsupported "Partially applied CHECK"
      | _ -> unsound "too many check params"
      end
    | "set-empty" -> begin match t_result with
      | I.TPrim("set", [elt]) -> "SET_EMPTY "^compile_etype elt
      | _ -> unsound "set-empty type"
      end
    | "set-reduce" -> not_impl "set-reduce"
    | "map-empty" -> begin match t_result with
      | I.TPrim("map", [k; v]) -> "SET_EMPTY "^compile_etype k^" "^compile_etype v
      | _ -> unsound "map-empty type"
      end
    | "map-reduce" -> not_impl "map-reduce"
    | "list-reduce" -> not_impl "list-reduce"
    | _ -> not_impl ("Primitive "^name^" not implemented")

and compile_EColl_CList stk list t_list =
  let t_elt = match t_list with I.TSum((Some("list", [t_elt]), lazy _)) -> t_elt | _ -> assert false in
  let stk = (item_s "(list ...)"  t_list) :: stk in
  let rec f = function
    | [] -> sprintf "NIL %s;\n" (compile_etype t_elt)
    | a :: b -> 
       sprintf "%s%sCONS;\n" (f b) (snd @@ compile_typed_expr stk a) 
  in
  stk, f list

and compile_EColl_CMap stk list t_map = 
  let t_k, t_v = match t_map with I.TPrim("map", [t_k; t_v]) -> t_k, t_v | _ -> assert false in
  let stk = (item_s "(map ...)"  t_map) :: stk in
  let rec f = function
    | [] -> sprintf "EMPTY_MAP %s %s;\n" (compile_etype t_k) (compile_etype t_v)
    | [_] -> assert false
    | k :: v :: rest -> 
      sprintf "%s%sSOME;\n%sUPDATE;\n" (f rest) (snd @@ compile_typed_expr stk v) (snd @@ compile_typed_expr stk k)
  in stk, f list

and compile_EColl_CSet stk list t_set = 
  let t_elt = match t_set with I.TPrim("set", [t_elt]) -> t_elt | _ -> assert false in
  let stk = (item_s "(set ...)"  t_set) :: stk in
  let rec f = function
    | [] -> sprintf "EMPTY_SET %s;\n" (compile_etype t_elt)
    | a :: b -> 
      let _, c = compile_typed_expr stk a in
      sprintf "%sPUSH bool True;\n%sUPDATE;\n" (f b) c
  in stk, f list

(* return the closure of a term, i.e. the list of the variables, with their
 * type, defined outside of the term but used inside the term. *)
and get_closure (stk: stack) et =
  let g = Standard_ctx.globals in
  let free_vars = I.get_free_evars ~except:g et in
  let et_of_v v = match get_level stk v with
    | Some n -> let _, _, t = List.nth stk (n-1) in v, t
    | None -> assert false
  in
  List.map et_of_v free_vars

(* Closures are represented as a pair `(env, lambda)` where `env` is the
 * product of all the variables defined out of the function but used inside it.
 *
 * They are called with an argument of the form `(arg, env)`, which they must
 * destructure into a proper stack at the beginning of the function body, 
 * which is then used by the lambda's actual code.
 *
 * TODO: Tag closure-free lambdas, maybe while typechecking, and optimize
 *       both their encoding and their application.
 *)
and compile_ELambda stk params body it_lambda closure =
  (* TODO forbid access to storage fields. *)
  match params, body with
  | _::_::_, _ -> unsupported "nested (multi-parameter) lambdas"
  | [], _ -> unsound "I.ELambda without parameter?!"
  | [(v_param, t_param)], (e_body, t_body) ->
    (* Generate the product holding the closure env. *)
    let e_prod = I.EProduct(List.map (fun (v,t) -> I.EId v, t) closure) in
    let t_prod = I.TProduct(None, lazy (List.map snd closure)) in
    let stk, c_env_make = compile_typed_expr stk (e_prod, t_prod) in
    (* Lambda active code *)
    let stk_l = List.map (fun (v, t) -> item_v v t) closure in (* closed vars *)
    let stk_l = (item_v v_param t_param) :: stk_l in           (* argument *)
    let stk_l, c_lambda = compile_typed_expr stk_l body in
    (* Env splitting code *)
    let n = List.length closure in
    let c_env_split = Compile_composite.product_split n in
    (* Env clean-up code *)
    let rec drops = (* drop env vars and argument *)
      let rec f = function 1 -> "DROP" | n -> "DROP; "^f (n-1) in f (n+1) in
    (* Function body with closure management code around *)
    let c_body = sprintf 
      "DUP; CAR; # arg\nDIP { CDR; %s }; # open closure\n%sDIP { %s } # Remove arg+closure\n" 
      c_env_split c_lambda drops in

    let t_param = I.TProduct(None, lazy [t_param; t_prod]) in
    let code = sprintf 
      "%s # Closure env; \nLAMBDA %s %s { %s }; # Closure code\nPAIR; # Closure"
      c_env_make (compile_etype t_param) (compile_etype t_body) c_body in

    List.tl stk, code  

and compile_closure_application stk f args t_result =
  (* The closure is encodede as a `(f, env)` pair, which must be split
   * and recombined to call `f` with `(arg, env)` as its argument. *)
  let arg = match args with [arg] -> arg | _ ->unsupported "Closures with more than 1 param" in
  let stk0 = stk in
  let stk, c_closure = compile_typed_expr stk f in
  let stk, c_arg     = compile_typed_expr stk arg in
  let code = sprintf "%sDUP; CAR; SWAP; CDR # env:f\n%s PAIR; # (arg,env):f\nEXEC"
    c_closure c_arg in
  (item_s "call" t_result) :: stk0, code

and compile_EApp stk f args t_result = match f with
  | I.ELambda([(params, body)], et0), t_lambda -> not_impl "apply literal lambda"
  | (I.EId "contract-call", _) -> begin match args with
    | [contract; contract_arg; amount] -> compile_contract_call stk contract contract_arg amount t_result
    | _ -> unsupported "partial application of contract-call"
    end
  | (I.EId(name), t_f) -> begin match get_level stk name with
    | None -> (item_e (I.EApp(f, args)) t_result)::stk, compile_primitive stk name args t_result
    | Some n -> compile_closure_application stk f args t_result 
    end
  | _ -> compile_closure_application stk f args t_result

and compile_contract_call stk contract contract_arg amount t_result =
  (* in Michelson: param : tez : contract param result : storage : [] -> result : storage : [] *)
  (* in Lamtez: \/ param result: contract -> param -> tez -> result *)

  let stack_storage_type = (* All of the stack, except the final user storage *)
    let stack_type = List.map (fun (_, _, it) -> it) stk in
    let rec f = function [_] -> [] | t::x -> t::f x | [] -> assert false in
    f stack_type in

  let stk', c0 = compile_typed_expr stk contract in
  let stk', c1 = compile_typed_expr stk' amount in
  let stk', c2 = compile_typed_expr stk' contract_arg in

  let n_stack_saving = string_of_int (Stk_S.add stack_storage_type) in

  (item_s "contract-call" t_result)::stk,
  c0^c1^c2^
  "DIIIP {\n"^
   "SAVE_STACK "^n_stack_saving^";\n"^
  "PAIR; # pack user store / stack store \n"^
  "}\n"^
  "TRANSFER_TOKENS;\n"^
  "DIP { # Restore saved stack\n"^
  "DUP; CDR; SWAP; CAR; # split user store / stack store\n"^
  "RESTORE_STACK "^n_stack_saving^";\n"^
  "}"

and compile_ESum stk i n content it =
  match it with
  | I.TSum(Some(sum_type_name, sum_type_args), lazy types) ->
    begin match sum_type_name, sum_type_args, i, n with
    | "bool",   [],   0, 2 -> (item_s "False" it) :: stk, "PUSH bool False"
    | "bool",   [],   1, 2 -> (item_s "True" it)  :: stk, "PUSH bool True"
    | "option", [t'], 0, 2 -> (item_s "None" it)  :: stk, "NONE "^compile_etype t'
    | "list",   [t'], 0, 2 -> (item_s "Nil" it)   :: stk, "NIL "^compile_etype t'
    | "option", [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (item_s "Some" it)::List.tl stk, code^"SOME"
    | "list",   [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (item_s "Cons" it)::List.tl stk, code^"DUP; CDR; SWAP; CAR; CONS"
    | _ ->
      let types = List.map compile_etype types in
      let stk, code = compile_typed_expr stk content in
      (item_s (sprintf "sum<%d|%d>" i n) it) ::List.tl stk, code^Compile_composite.sum_make i types
    end
  | _ -> unsound "Not a sum type"

and compile_EProductSet stk e_product i n e_field it =
  let n = match it with I.TProduct(_, lazy fields) -> List.length fields | _ -> assert false in
  let stk, c0 = compile_typed_expr stk e_product in
  let stk, c1 = compile_typed_expr stk e_field in
  (* Perform field update *)
  let c2 = sprintf "%s # update field <%d|%d>\n" (Compile_composite.product_set i n) i n in
  (* field removed from stack *)
  let stk = List.tl stk in
  stk, c0^c1^c2

and compile_EStoreSet stk i e_field e_rest =
  let stk, c0 = compile_typed_expr stk e_field in
  (* Current depth of user store *)
  let store_level = match get_level stk "@" with Some n -> n-1 | None -> assert false in
  (* Number of fields in user store *)
  let n = let _, _, t_store = List.nth stk store_level in
          match t_store with I.TProduct(_, lazy fields) -> List.length fields | _ -> assert false in
  (* Perform field update *)
  let c1 = sprintf "%s # PEEK %d user store\n" (peek store_level) store_level^
           sprintf "SWAP; # Get updated value on top\n"^
           sprintf "%s # update store field <%d|%d>\n" (Compile_composite.product_set i n) i n^
           sprintf "%s # POKE %d user store back\n" (poke (store_level-1)) (store_level-1) in
  (* field removed from stack *)
  let stk = List.tl stk in

  let stk, c2 = compile_typed_expr stk e_rest in
  stk, c0^c1^c2

and compile_ESumCase stk test cases it =
  let stk, code = compile_typed_expr stk test in
  let stk = List.tl stk in (* cases are executed with the test removed from stack. *)
  let sum_type_name = match snd test with I.TSum(Some (name, _), _) -> name | _ -> unsound "Not a sum type" in
  (* Michelson refuses the  `DIP { DROP }` fragments after a `FAIL`: `FAIL` must be last in its sequence.
   * This function only generates the `DIP { DROP }` if the body isn't a `FAIL`. *)
  let remove_unless_fail body var_name = match body with
  | I.EId("fail"), _ -> "" (* TODO check variable capture. *)
  | _ -> sprintf "DIP { DROP } # Remove %s\n" var_name
  in
  match sum_type_name, cases with
  | "bool", [(_, _, if_false); (v, _, if_true)] ->
    let _, if_false = compile_typed_expr stk if_false in
    let _, if_true = compile_typed_expr (stk) if_true in
    (item_s "if" it)::stk, sprintf "%sIF { %s}\n{ %s}" code if_true if_false (* TODO make sure unit-bound variables in cases aren't used *)
  | "list", [(_, _, if_nil); (v, t_v, if_cons)] ->
    let _, if_cons_code = compile_typed_expr ((item_s "CONS" it)::stk) if_cons in
    let _, if_nil_code = compile_typed_expr stk if_nil in
    (item_s "if_cons" it) :: stk, 
    sprintf "%sIF_CONS { PAIR; # %s\n %s%s}\n{ %s}"
    code v if_cons_code if_nil_code (remove_unless_fail if_cons "cons")
  | "option", [(_, _, if_none); (v, t_v, if_some)] ->
    let _, if_some_code = compile_typed_expr ((item_v v t_v)::stk) if_some in
    let _, if_none_code = compile_typed_expr stk if_none in
    (item_s "if_none" it)::stk, 
    sprintf "%sIF_NONE { %s}\n{ # %s\n%s%s}" code if_none_code v if_some_code
    (remove_unless_fail if_some v)
  | _ -> (* User-defined sum type *)
    let f i (v, t_v, ie)  =
      let code = snd (compile_typed_expr ((item_v v t_v)::stk) ie) in
      sprintf "# | <%d>(%s):\n%s%s" i v code (remove_unless_fail ie v) in
    (item_s (sprintf "sum<%d>" (List.length cases)) it)::stk, code ^ Compile_composite.sum_case (List.mapi f cases)

let patch_stack_store_operations code =
  let re = Str.regexp "\n *\\(SAVE\\|RESTORE\\)_STACK +\\([0-9]+\\) *;? *\n" in
  let save_stack i =
    let _, all_prods = Stk_S.get_all() in
    let this_prod, this_stack = Stk_S.get i in
    "# Store stack "^String_of_intermediate.string_of_etype this_prod^":\n"^    
    Compile_composite.product_make (List.length this_stack)^
    " # pack "^string_of_int (List.length this_stack)^" elements as a product\n"^
    Compile_composite.sum_make i (List.map compile_etype all_prods)^
    " # Package in sum case\n"
    
  and restore_stack i =
    let _, all_prods = Stk_S.get_all() in
    let this_prod, this_stack = Stk_S.get i in
    let n_sum = List.length all_prods in
    let n_prod = List.length this_stack in
    "# Restore stack "^String_of_intermediate.string_of_etype this_prod^":\n"^
    Compile_composite.sum_get i n_sum^
    " # Extract from storage\n"^
    Compile_composite.product_split n_prod^
    " # split in "^string_of_int n_prod^" elements\n"
    
  in let subst m =
    "\n"^
    ( match Str.matched_group 1 m, int_of_string (Str.matched_group 2 m) with
    | "SAVE", n -> save_stack n
    | "RESTORE", n -> restore_stack n
    | _ -> assert false
    )
  in Str.global_substitute re subst code

let rec compile_data et = 
  (* print_endline("Data = "^String_of_intermediate.string_of_typed_expr et); *)
  match (fst et) with
  | I.ELit x -> x
  | I.EColl(Ast.CList, elts) -> compile_data_list elts
  | I.EColl(Ast.CSet,  elts) -> compile_data_set  elts
  | I.EColl(Ast.CMap,  elts) -> compile_data_map elts
  | I.EProduct [] -> "Unit"
  | I.EProduct elts -> compile_data_product elts
  | I.ESum(i, n, content) -> compile_data_sum i n content (snd et)
  | I.ELambda _ -> not_impl "lambda in data"
  | I.EId _ -> unsound "No variables in data"
  | I.ELet _ | I.EApp _ | I.EProductGet _ | I.EProductSet _ 
  | I.EStoreSet _ | I.ESumCase _ -> unsound "Not allowed in data"

and compile_data_list = function
  | [] -> "Nil"
  | a :: b -> sprintf "(Cons %s %s)" (compile_data a) (compile_data_list b)

and compile_data_set elts =
  "(Set "^sep_list " " compile_data elts^")"

and compile_data_map elts =
  let rec pairs = function [] -> [] 
    | [_] -> unsound "odd number of elements in map"
    | a::b::c -> sprintf "(Item %s %s)" (compile_data a) (compile_data b) :: pairs c in
  sprintf "(Map %s)" (String.concat " " (pairs elts))

and compile_data_product elts =
  Compile_composite.product_data (List.map compile_data elts)

and compile_data_sum i n e t_sum = match i, t_sum with
  | 0, I.TSum(Some("bool", []), _) -> "False"
  | 1, I.TSum(Some("bool", []), _) -> "True"
  | 0, I.TSum(Some("option", [_]), _) -> "None"
  | 1, I.TSum(Some("option", [_]), _) -> "(Some "^compile_data e^")"
  (* TODO lists built with Cons/Nil *)
  | _ -> Compile_composite.sum_data i n (compile_data e)

let compile_contract i_contract = 
  match i_contract.I.code with
  | I.ELambda(_::_::_, _), _ -> not_impl "contracts returning a function"
  | I.ELambda([(v_param, t_param)], (e_body, t_body as body)), t_lambda ->
    Stk_S.reset();

    let stk = [(item_v v_param t_param); (item_v "@" i_contract.I.storage_type)] in
    let stk, code = compile_typed_expr stk body in

    (* TODO simplify storage if there is no contract-call *)
    let t_compiler_store, saved_stacks = Stk_S.get_all() in
    let t_stores = I.TProduct(None, lazy [t_compiler_store; i_contract.I.storage_type]) in

    (* Piece everything together*)
    let code =
      sprintf "parameter %s;\n" (compile_etype t_param) ^
      sprintf "# %s\n" (String_of_intermediate.string_of_etype t_stores)^
      sprintf "storage %s;\n" (compile_etype t_stores) ^
      sprintf "return %s;\n" (compile_etype t_body) ^
      sprintf "code { DUP; CDR; SWAP; CAR; # split %s/stores\n" v_param ^
      sprintf "DIP { CDR }; # remove stack store\n"^
      sprintf "%s" code ^
      sprintf "DIP { DROP }; # remove %s\n" v_param ^
      sprintf "DIP {\nUNIT;\nSAVE_STACK 0;\nPAIR;\n}; # group user/compiler stores\n"^
      sprintf "PAIR; # group result and store\n" ^
      sprintf "}\n"
    in

    let storage_init = match i_contract.I.storage_init with None -> None | Some et_user_store ->
      (* Actual storage is the product of stack saving store and user-defined store. *)
      let et_unit = I.EProduct[], I.TProduct(Some("unit", []), lazy []) in
      let et_compiler_store = I.ESum(0, List.length saved_stacks, et_unit), t_compiler_store in
      let et_stores = I.EProduct[et_compiler_store; et_user_store], t_stores in
      Some (compile_data et_stores) in
    
    let n = List.length saved_stacks in
    let make_storage user_storage =
      sprintf "(Pair %s %s)\n" (CCmp.sum_data 0 n "Unit") user_storage
    in

    let code = patch_stack_store_operations code in
    let code = Code_format.indent '{' '}' code in
    {code; storage_init; make_storage}

  | _ -> unsound "Bad contract type"

