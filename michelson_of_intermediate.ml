open Printf
open Utils

module I = Intermediate
module P = String_of_intermediate
module MoC = Michelson_of_composite
module Stk_S = Saved_stack_store


type contract = {
  code: string;
  storage_init: string option;
  make_storage: string -> string;
}

let _DEBUG_ = ref false
let debug_indent = ref 0

(* Compose code instructions together in a signle line, with semicolon separators. *)
let cc x = String.concat "; " (List.filter ((<>) "") x)

let dup n = "D"^String.make n 'U'^"P"
let rec peek = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "DIP { %s }; SWAP" @@ peek (n-1)
let rec poke = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "SWAP; DIP { %s }" @@ poke (n-1)
let rec drop = function 0 -> "" | 1 -> "DROP" | n -> sprintf "DROP; %s" @@ drop (n-1)

let rec compile_etype t =
  let c = compile_etype in
  match t with
  | I.TPrim(t, []) -> t
  | I.TPrim(t, args) -> sprintf "(%s %s)" t (sep_list " " c args)
  | I.TLambda(params, result) -> sprintf "(lambda %s %s)" (sep_list " " c params) (c result)
  | I.TProduct(_, lazy []) -> "unit"
  | I.TProduct(_, lazy fields) -> MoC.product_type (List.map c fields)
  | I.TSum(Some("bool", []), _) -> "bool"
  | I.TSum(Some("list", [t']), _) -> sprintf "(list %s)" (c t')
  | I.TSum(Some("option", [t']), _) -> sprintf "(option %s)" (c t')
  | I.TSum(_, lazy fields) -> MoC.sum_type (List.map c fields)

(* Content of the stack:
 *
 * * `SAnon(hint, t)` is an unnamed element of type t(most likely a function 
 *   argument). `hint` is a short description of the element, to be put in
 *   generated Michelson comments.
 * * `SVar(id, Some expr, etype)` is a variable with the given `id` as name,
 *   value `expr` and type `etype`.
 * * `SVar(id, None, etype)` is a variable with the given `id` as name,
 *   type `etype` and whose value is not known at compilation time.
 *
 * The first element of the list is the top of the stack, the last one is
 * the bottom. 
 *)
type stack_item = SAnon of (string * I.etype) | SVar of (I.evar * I.expr option * I.etype)
type stack = stack_item list

let item_e expr etype = SAnon(String_of_intermediate.string_of_untyped_expr expr, etype)
let item_s str  etype = SAnon(str, etype)
let item_v name ?expr etype= SVar(name, expr, etype)

let rec get_level stk v = match stk with
  | [] -> None
  | SVar(v', _, _) :: _ when v=v' -> Some 1
  | _ :: stk' -> match get_level stk' v with None -> None | Some n -> Some (n+1)

let rec compile_typed_expr (stk:stack) ((ie, it): I.typed_expr) : (stack * string) =
  if !_DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_untyped_expr ie);
    (* print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_expr ie); *)
    incr debug_indent
  end;
  let stk, code = match ie with
  | I.ELit value -> 
    let type_name = match it with I.TPrim(t, _) -> t | _ -> unsound "litteral" in
    item_e ie it :: stk, sprintf "PUSH %s %s" type_name value
  | I.EId name -> begin match get_level stk name with
    | Some n -> (item_v name it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (item_e ie it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | I.EColl(Ast.CList, list) -> compile_EColl_CList stk list it
  | I.EColl(Ast.CMap,  list) -> compile_EColl_CMap  stk list it
  | I.EColl(Ast.CSet,  list) -> compile_EColl_CSet  stk list it
  | I.ELambda(typed_param_ids, et_body) -> begin match it with
    | I.TLambda _ -> compile_lambda stk typed_param_ids et_body it
    | I.TPrim("closure", t_env :: t_result :: _) ->
      compile_closure stk typed_param_ids et_body
    | _ -> unsound "lambda type"
    end
  | I.ELet(v, et0, et1) ->
    let stk, c0 = compile_typed_expr stk et0 in
    let stk = item_v v ~expr:(fst et0) (snd et0) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_typed_expr stk et1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, sprintf "%s# let %s = %s\n%sDIP{ DROP } # remove %s\n"
      c0 v (String_of_intermediate.string_of_untyped_expr @@ fst et0) c1 v
  | I.EApp(f, args) -> compile_EApp stk f args it
  | I.EProduct [] -> (item_e ie it) :: stk, "UNIT"
  | I.EProduct fields ->
    let stk', code = List.fold_left
      (fun (stk, code) field -> let stk, code' = compile_typed_expr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (item_e ie it)::stk, code^MoC.product_make(List.length fields)
  | I.ESum(i, n, content) -> compile_ESum stk i n content it
  | I.EProductGet(et0, i, n) ->
    let _, code = compile_typed_expr stk et0 in
    (item_e ie it)::stk, code^MoC.product_get i n
  | I.EProductSet(et0, i, n, et1) ->
    let stk', c0 = compile_typed_expr stk et0 in
    let stk', c1 = compile_typed_expr stk et1 in (* TODO sure that the stask can't be messsed up? *)
    (item_e ie it)::stk, c0^c1^MoC.product_set i n
  | I.EStoreSet(i, et0, et1) -> compile_EStoreSet stk i et0 et1
  | I.ESumCase(test, cases) -> compile_ESumCase stk test cases it
  in
  if !_DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let string_of_stk_item = function SAnon(txt, _) | SVar(txt, _, _) -> txt in
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

  let c_args args = (* Compiles and stacks all arguments, without keeping the stack. *)
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
    | "set-reduce" -> not_impl "set-reduce"
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

and compile_lambda stk typed_param_ids typed_body it =
  (* TODO: unbundle multiple params from a tuple. *)
  if List.length typed_param_ids != 1 then not_impl "Multi-param lambdas";
  let param_id, param_type = List.hd typed_param_ids in
  let inner_stk = [item_v param_id param_type] in
  let _, code = compile_typed_expr inner_stk typed_body in
  let cleanup = "DIP { DROP }; # remove "^param_id^"\n" in
  (item_s "lambda" it)::stk, 
  sprintf "LAMBDA %s %s { %s%s }"
    (compile_etype @@ param_type) (compile_etype @@ snd typed_body) code cleanup

(* return the closure environment of a term, i.e. the list of the variables,
 * with their type, defined outside of the term but used inside the term. *)
and get_closure_env (stk: stack) ?(except=[]) et =
  let except = except @ Standard_ctx.globals in
  let free_vars = I.get_free_evars ~except et in
  (* Retrieve var type from var name in stack *)
  (* TODO beta-reducing closed variables whose value is known would allow to
   * turn some closures into combinatorial functions. *)
  let et_of_v v = match get_level stk v with
    | None -> assert false
    | Some n -> match List.nth stk (n-1) with
      | SVar(id, e, t) -> id, t
      | _ -> assert false
  in
  List.map et_of_v free_vars

and compile_closure stk typed_param_ids (e_body, t_body as body) =
  if List.length typed_param_ids<>1 then not_impl "multi-param closures";
  let v_param, t_param = List.hd typed_param_ids in

  let closure = get_closure_env stk ~except:[v_param] body in

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
  let c_env_split = MoC.product_split n in

  (* Env clean-up code *)
  let rec drops = (* drop env vars and argument *)
    let rec f = function 1 -> "DROP" | n -> "DROP; "^f (n-1) in f (n+1) in

  (* Function body with closure management code around *)
  let c_body = sprintf 
    "DUP; CAR; # arg\nDIP { CDR; %s }; # open closure\n%sDIP { %s } # Remove arg+closure\n" 
    c_env_split c_lambda drops in

  let t_param_pair = I.TProduct(None, lazy [t_param; t_prod]) in
  let code = sprintf 
    "%s # Closure env; \nLAMBDA %s %s { %s }; # Closure code\nPAIR; # Closure"
    c_env_make (compile_etype t_param_pair) (compile_etype t_body) c_body in

    List.tl stk, code  

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


and compile_closure_application stk f args t_result =
  (* The closure is encodede as a `(f, env)` pair, which must be split
   * and recombined to call `f` with `(arg, env)` as its argument. *)

  (* TODO: need to erase the environment from closure type: 
   * `type closure a b = (∃e): ((a×e)->b) × e`
   * Can't be expressed in simply-typed lambda calculus, but they can be wrapped
   * in a big, contract-wide sum type.
   *)
  let arg = match args with [arg] -> arg | _ ->unsupported "Closures with more than 1 param" in
  let stk0 = stk in
  let stk, c_closure = compile_typed_expr stk f in
  let stk, c_arg     = compile_typed_expr stk arg in
  let code = sprintf "%sDUP; CAR; SWAP; CDR # env:f\n%s PAIR; # (arg,env):f\nEXEC"
    c_closure c_arg in
  (item_s "call" t_result) :: stk0, code

and compile_lambda_application stk f args t_result =
  (* TODO in case of multi-param, bundle them in a tuple. *)
  let arg = match args with [arg] -> arg | _ -> not_impl "Multi-param lambdas" in
  let stk0 = stk in
  let stk, c_func = compile_typed_expr stk f in
  let stk, c_arg  = compile_typed_expr stk arg in
  (item_s "call" t_result) :: stk0, c_func^c_arg^"EXEC"

and get_lambda stk et : ((I.evar * I.etype) list * I.typed_expr) option =
  match et with
  | I.ELambda(params, body), _ ->
    Some(params, body)
  | I.EId id, _ -> not_impl "retrieve static var content from stack"
  | _ -> None

and compile_list_rev_map stk param_id param_type body list =
let a_type_name = compile_etype param_type in
let b_type_name = compile_etype (snd body) in
let stk_func_body, stk_list_a = 
    let hd_a = item_v param_id param_type
    and tl_a = item_s "tl_a" (I.TPrim("list", [param_type]))
    and list_b = item_s "list_b" (I.TPrim("list", [snd body])) in      
    hd_a :: tl_a :: list_b :: stk,
    list_b :: stk in
  let _, code_body = compile_typed_expr stk_func_body body in
  let _, code_list_a = compile_typed_expr stk_list_a list in
  let stk = item_s "list_b" (I.TPrim("list", [snd body])) :: List.tl stk in
  let code = 
    "# reverse list map # list_a:...\n"^
    sprintf "NIL %s; # list_b:...\n" b_type_name^
    code_list_a^
    "PUSH bool True; # True:list_a:list_b:...\n" ^
    "LOOP { # list_a:list_b:...\n"^
    "IF_CONS { # hd_a:tl_a:list_b:...\n"^
    code_body^
    "DIP { DROP; SWAP }; # hd_b:list_b:tl_a:...\n"^
    "CONS; # list_b:tl_a:...\n"^
    "SWAP; # tl_a:list_b:...\n"^
    "PUSH bool True; # True:tl_a:list_b:...\n"^
    sprintf "}\n{ NIL %s; PUSH bool False };\n}\nDROP; # Remove list_a" a_type_name in
  stk, code
  
and compile_rev_list stk elt_type =
  let elt_type = compile_etype elt_type in
  "# Reverse list\n"^
  sprintf "DIP{ NIL %s }; PUSH bool True;\n" elt_type^
  "LOOP { IF_CONS { SWAP; DIP{ CONS }; PUSH bool True;\n}\n"^
  sprintf "{ NIL %s; PUSH bool False; }\n}\nDROP; # List reversed\n" elt_type

and compile_list_map stk param_id param_type body list =
  let stk, code = compile_list_rev_map stk param_id param_type body list in
  stk, code^"\n"^compile_rev_list stk (snd body)

and compile_EApp stk f args t_result = 
  match f with
  | I.ELambda([(params, body)], et0), t_lambda -> not_impl "apply literal lambda"
  | I.EId "contract-call", _ -> begin match args with
    | [contract; contract_arg; amount] -> compile_contract_call stk contract contract_arg amount t_result
    | _ -> unsupported "partial application of contract-call"
    end
  | I.EId "list-map", _ ->
    let [list; func] = args in
    begin match get_lambda stk func with
    | Some([param_id, param_type], body) ->
      print_endline "get_lambda returned ";
      compile_list_map stk param_id param_type body list
    | Some _ -> unsound "list-map" (* TODO could happen when making a list of functions? *)
    | None -> not_impl "list-map of unknown function"
    end
  | I.EId(name), t_f -> begin match get_level stk name with
    | None -> (item_e (I.EApp(f, args)) t_result)::stk, compile_primitive stk name args t_result
    | Some _ -> 
      match t_f with
      | I.TLambda _ -> compile_lambda_application stk f args t_result
      | I.TPrim("closure", _) -> compile_closure_application stk f args t_result
      | _ -> unsound "Applying non-function/closure" 
    end
  | _ -> compile_closure_application stk f args t_result

and compile_contract_call stk contract contract_arg amount t_result =
  (* in Michelson: param : tez : contract param result : storage : [] -> result : storage : [] *)
  (* in Lamtez: \/ param result: contract -> param -> tez -> result *)

  let stack_storage_type = (* All of the stack, except the final user storage *)
    let t_of_s = function SAnon(_, t)|SVar(_, _, t) -> t in
    let stack_type = List.map t_of_s stk in
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
      (item_s (sprintf "sum<%d|%d>" i n) it) ::List.tl stk, code^MoC.sum_make i types
    end
  | _ -> unsound "Not a sum type"

and compile_EProductSet stk e_product i n e_field it =
  let n = match it with I.TProduct(_, lazy fields) -> List.length fields | _ -> assert false in
  let stk, c0 = compile_typed_expr stk e_product in
  let stk, c1 = compile_typed_expr stk e_field in
  (* Perform field update *)
  let c2 = sprintf "%s # update field <%d|%d>\n" (MoC.product_set i n) i n in
  (* field removed from stack *)
  let stk = List.tl stk in
  stk, c0^c1^c2

and compile_EStoreSet stk i e_field e_rest =
  let stk, c0 = compile_typed_expr stk e_field in
  (* Current depth of user store *)
  let store_level = match get_level stk "@" with Some n -> n-1 | None -> assert false in
  (* Number of fields in user store *)
  let n = 
    match List.nth stk store_level with SVar(_, _, t) | SAnon(_, t) -> 
      match t with
      | I.TProduct(_, lazy fields) -> List.length fields 
      | _ -> assert false in
  (* Perform field update *)
  let c1 = sprintf "%s # PEEK %d user store\n" (peek store_level) store_level^
           sprintf "SWAP; # Get updated value on top\n"^
           sprintf "%s # update store field <%d|%d>\n" (MoC.product_set i n) i n^
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
    (item_s (sprintf "sum<%d>" (List.length cases)) it)::stk, code ^ MoC.sum_case (List.mapi f cases)

let patch_stack_store_operations code =
  let re = Str.regexp "\n *\\(SAVE\\|RESTORE\\)_STACK +\\([0-9]+\\) *;? *\n" in
  let save_stack i =
    let _, all_prods = Stk_S.get_all() in
    let this_prod, this_stack = Stk_S.get i in
    "# Store stack "^String_of_intermediate.string_of_etype this_prod^":\n"^    
    MoC.product_make (List.length this_stack)^
    " # pack "^string_of_int (List.length this_stack)^" elements as a product\n"^
    MoC.sum_make i (List.map compile_etype all_prods)^
    " # Package in sum case\n"
    
  and restore_stack i =
    let _, all_prods = Stk_S.get_all() in
    let this_prod, this_stack = Stk_S.get i in
    let n_sum = List.length all_prods in
    let n_prod = List.length this_stack in
    "# Restore stack "^String_of_intermediate.string_of_etype this_prod^":\n"^
    MoC.sum_get i n_sum^
    " # Extract from storage\n"^
    MoC.product_split n_prod^
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
  MoC.product_data (List.map compile_data elts)

and compile_data_sum i n e t_sum = match i, t_sum with
  | 0, I.TSum(Some("bool", []), _) -> "False"
  | 1, I.TSum(Some("bool", []), _) -> "True"
  | 0, I.TSum(Some("option", [_]), _) -> "None"
  | 1, I.TSum(Some("option", [_]), _) -> "(Some "^compile_data e^")"
  (* TODO lists built with Cons/Nil *)
  | _ -> MoC.sum_data i n (compile_data e)

let compile_contract i_contract = 
  match i_contract.I.code with
  | I.ELambda(_::_::_, _), _ -> not_impl "contracts returning a function"
  | I.ELambda([(v_param, t_param)], (e_body, t_body as body)), t_lambda ->
    Stk_S.reset();

    let stk = [(item_v v_param t_param); (item_v "@" i_contract.I.storage_type)] in
    let stk, code = compile_typed_expr stk body in

    (* TODO simplify storage if there is no contract-call *)
    let t_compiler_store, saved_stacks = Stk_S.get_all() in
    let need_stack_store = List.length saved_stacks > 1 in
    let t_stores = 
      if not need_stack_store then i_contract.I.storage_type
      else I.TProduct(None, lazy [t_compiler_store; i_contract.I.storage_type]) in

    (* Piece everything together *)
    let code =
      sprintf "parameter %s;\n" (compile_etype t_param) ^
      sprintf "storage %s;\n" (compile_etype t_stores) ^
      sprintf "return %s;\n" (compile_etype t_body) ^
      sprintf "code { DUP; CDR; SWAP; CAR; # split %s/store\n" v_param ^
      (if need_stack_store then "DIP { CDR }; # remove stack store\n" else "")^
      sprintf "%s" code ^
      sprintf "DIP { DROP }; # remove %s\n" v_param ^
      (if need_stack_store then "DIP {\nUNIT;\nSAVE_STACK 0;\nPAIR;\n}; # group user*stack stores\n" else "")^
      sprintf "PAIR; # group result and store\n" ^
      sprintf "}\n"
    in

    let storage_init = match i_contract.I.storage_init, need_stack_store with
    | None, _ -> None (* No init data *)
    | Some et_user_store, false -> Some (compile_data et_user_store) (* No stack store *)
    | Some et_user_store, true ->
      (* Storage is the product of stack saving store and user-defined store. *)
      let et_unit = I.EProduct[], I.TProduct(Some("unit", []), lazy []) in
      let et_compiler_store = I.ESum(0, List.length saved_stacks, et_unit), t_compiler_store in
      let et_stores = I.EProduct[et_compiler_store; et_user_store], t_stores in
      Some (compile_data et_stores)
    in
    
    let n = List.length saved_stacks in
    let make_storage = if need_stack_store then
      (fun user_storage -> sprintf "(Pair %s %s)\n" (MoC.sum_data 0 n "Unit") user_storage)
      else (fun x  -> x)
    in

    let code = patch_stack_store_operations code in
    let code = Code_format.indent '{' '}' code in
    {code; storage_init; make_storage}

  | _ -> unsound "Bad contract type"

