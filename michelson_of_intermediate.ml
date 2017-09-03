open Printf
open Utils
module I = Intermediate
module P = String_of_intermediate
module Stk_S = Compile_stack_store

let _DEBUG_ =true
let debug_indent = ref 0

type stack = (I.evar option * I.etype) list

let dup n = "D"^String.make n 'U'^"P"
let rec peek = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "DIP { %s }; SWAP" (peek (n-1))
let rec poke = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "SWAP; DIP { %s }" (poke (n-1))

(* Compose code instructions together in a signle line, with semicolon separators. *)
let cc x = String.concat "; " (List.filter ((<>) "") x)


let rec get_level stk v = match stk with
  | [] -> None
  | (Some v', _) :: _ when v=v' -> Some 1
  | _ :: stk' -> match get_level stk' v with None -> None | Some n -> Some (n+1)

let rec compile_etype t =
  let c = compile_etype in
  match t with
  | I.TPrim(t, []) -> t
  | I.TPrim(t, args) -> sprintf "(%s %s)" t (sep_list " " c args)
  | I.TLambda(params, result) -> sprintf "(lambda %s %s)" (sep_list " " c params) (c result)
  | I.TProduct(_, lazy []) -> "unit"
  | I.TProduct(_, lazy fields) -> Compile_composite.product_type (List.map c fields)
  | I.TSum(Some("bool", []), _) -> "bool"
  | I.TSum(Some("list", [t']), _) -> sprintf "(list %s)" (c t')
  | I.TSum(Some("option", [t']), _) -> sprintf "(option %s)" (c t')
  | I.TSum(_, lazy fields) -> Compile_composite.sum_type (List.map c fields)

let rec compile_typed_expr (stk:stack) ((ie, it): I.typed_expr) : (stack * string) =
  if _DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_untyped_expr ie);
    (* print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_expr ie); *)
    incr debug_indent
  end;
  let stk, code = match ie with
  | I.ELit x -> (match it with I.TPrim(t_name, []) -> (None, it)::stk, sprintf "PUSH %s %s" t_name x | _ -> unsound "litteral type")
  | I.EId name -> begin match get_level stk name with
    | Some n -> (Some name, it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (None, it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | I.EColl(Ast.CList, list) -> compile_EColl_CList stk list it
  | I.EColl(Ast.CMap,  list) -> compile_EColl_CMap  stk list it
  | I.EColl(Ast.CSet,  list) -> compile_EColl_CSet  stk list it
  | I.ELambda(params, body) -> compile_ELambda stk params body it
  | I.ELet(v, ie0, ie1) ->
    let stk, c0 = compile_typed_expr stk ie0 in
    let stk = (Some v, snd ie0) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_typed_expr stk ie1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, c0^"# let "^v^" = ... in ...\n"^c1^"DIP { DROP } # remove "^v^"\n"
  | I.EApp(f, args) -> compile_EApp stk f args it
  | I.EProduct [] -> (None, I.TProduct(Some("unit", []), lazy []))::stk, "UNIT"
  | I.EProduct fields ->
    let stk', code = List.fold_left
      (fun (stk, code) field -> let stk, code' = compile_typed_expr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (None, it)::stk, code^Compile_composite.product_make(List.length fields)
  | I.ESum(i, n, content) -> compile_ESum stk i n content it
  | I.EProductGet(ie, i, n) ->
    let _, code = compile_typed_expr stk ie in
    (None, it)::stk, code^Compile_composite.product_get i n
  | I.EProductSet(e0, i, n, e1) ->
    let stk', c0 = compile_typed_expr stk e0 in
    let stk', c1 = compile_typed_expr stk e1 in (* TODO sure that the stask can't be messsed up? *)
    (None, it)::stk, c0^c1^Compile_composite.product_set i n
  | I.EStoreSet(i, e0, e1) -> compile_EStoreSet stk i e0 e1
  | I.ESumCase(test, cases) -> compile_ESumCase stk test cases it
  in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let string_of_stk_item (v, t) = (match v with None -> "" | Some x -> x^": ")^compile_etype t in
  let comment = sep_list ", " string_of_stk_item (List.tl stk) in
  let code = if last_char='\n' then code else code^"; # "^P.string_of_untyped_expr ie^", "^comment^"\n" in
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
    "EQ", "CMPEQ"; "LT", "CMPLT"; "LE", "CMPLE"; "GE", "CMPGE"; "GT", "CMPGT";
  ] in

  let simple_operators = [
    "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"; "AND"; "OR"; "XOR"; "CONCAT"] in

  let c_args args = (* Compiles and stacks all arguments, discards resulting stack. *)
    let stk, code = List.fold_left
      (fun (stk, c) arg -> let stk, c' = compile_typed_expr stk arg in stk, c^c')
      (stk, "") args in
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
      | I.TPrim("contract", [param; result]) -> "SOURCE "^compile_etype param^" "^compile_etype result
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
  let t_elt = match t_list with I.TPrim("list", [t_elt]) -> t_elt | _ -> assert false in
  let stk = (None, t_list) :: stk in
  let rec f = function
    | [] -> ["NIL "^compile_etype t_elt]
    | a :: b -> 
      let _, c = compile_typed_expr stk a in
      "CONS" :: c :: f b
  in
  stk, cc (List.rev (f list))

and compile_EColl_CMap stk list t_map = 
  let t_k, t_v = match t_map with I.TPrim("list", [t_k; t_v]) -> t_k, t_v | _ -> assert false in
  not_impl "EColl_CMap"

and compile_EColl_CSet stk list t_set = 
  let t_elt = match t_set with I.TPrim("set", [t_elt]) -> t_elt | _ -> assert false in
  not_impl "EColl_CSet"

and compile_ELambda stk params body it_lambda =
  match params, body with
  | [(v_param, t_param)], (e_body, t_body) ->
    (* TODO check that there's no free variable. *)
    let stk, code = compile_typed_expr [Some v_param, t_param] body in
    (None, it_lambda)::List.tl stk, sprintf "LAMBDA %s %s { %s }"
      (compile_etype t_param) (compile_etype t_body) code
  | _::_, _ -> unsupported "nested (multi-parameter) lambdas"
  | [], _ -> unsound "I.ELambda without parameter?!"


and compile_EApp stk f args t_result = match f with
  | I.ELambda([(params, body)], et0), t_lambda -> not_impl "apply literal lambda"
  | (I.EId "contract-call", _) -> begin match args with
    | [contract; contract_arg; amount] -> compile_contract_call stk contract contract_arg amount t_result
    | _ -> unsupported "partial application of contract-call"
    end
  | (I.EId(name), t_f) -> begin match get_level stk name with
    | Some n -> not_impl "user-defined lambda" (* user-defined lambda *)
    | None -> (None, t_result)::stk, compile_primitive stk name args t_result
    end
  | _ -> unsound "Applying a non-function"

and compile_contract_call stk contract contract_arg amount t_result =
  (* in Michelson: param : tez : contract param result : storage : [] -> result : storage : [] *)
  (* in Lamtez: \/ param result: contract -> param -> tez -> result *)

  let stack_storage_type = (* All of the stack, except the final user storage *)
    let stack_type = List.map snd stk in
    let rec f = function [_] -> [] | t::x -> t::f x | [] -> assert false in
    f stack_type in

  let stk', c0 = compile_typed_expr stk contract in
  let stk', c1 = compile_typed_expr stk' amount in
  let stk', c2 = compile_typed_expr stk' contract_arg in

  let n_stack_saving = string_of_int (Stk_S.add stack_storage_type) in

  (None, t_result)::stk,
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
    | "bool",   [],   0, 2 -> (None, it) :: stk, "PUSH bool False"
    | "bool",   [],   1, 2 -> (None, it) :: stk, "PUSH bool True"
    | "option", [t'], 0, 2 -> (None, it) :: stk, "NONE "^compile_etype t'
    | "list",   [t'], 0, 2 -> (None, it) :: stk, "NIL "^compile_etype t'
    | "option", [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (None, it)::List.tl stk, code^"SOME"
    | "list",   [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (None, it)::List.tl stk, code^"DUP; CAR; SWAP; CDR; CONS"
    | _ ->
      let types = List.map compile_etype types in
      let stk, code = compile_typed_expr stk content in
      (None, it) ::List.tl stk, code^Compile_composite.sum_make i types
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
  let n = let _, t_store = List.nth stk store_level in
          match t_store with I.TProduct(_, lazy fields) -> List.length fields | _ -> assert false in
  (* Perform field update *)
  let c1 = sprintf "%s # PEEK %d user store\n" (peek store_level) store_level^
           sprintf "SWAP\n"^
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
  match sum_type_name, cases with
  | "bool", [(_, _, if_false); (v, _, if_true)] ->
    let _, if_false = compile_typed_expr stk if_false in
    let _, if_true = compile_typed_expr (stk) if_true in
    (None, it)::stk, sprintf "%sIF { %s}\n{ %s}" code if_true if_false (* TODO make sure unit-bouns variables in cases aren't used *)
  | "list", [(_, _, if_nil); (v, t_v, if_cons)] ->
    let _, if_cons = compile_typed_expr ((Some v, t_v)::stk) if_cons in
    let _, if_nil = compile_typed_expr stk if_nil in
    (None, it)::stk, sprintf "%sIF_CONS { PAIR; # %s\n %sDIP { DROP }# remove cons\n}\n{ %s}" code v if_cons if_nil
  | "option", [(_, _, if_none); (v, t_v, if_some)] ->
    let _, if_some = compile_typed_expr ((Some v, t_v)::stk) if_some in
    let _, if_none = compile_typed_expr stk if_none in
    (None, it)::stk, sprintf "%sIF_NONE { %s}\n{ # %s\n %sDIP { DROP } # remove %s\n}" code if_none v if_some v
  | _ ->
    let f i (v, t_v, ie)  =
      sprintf "# | <%d>(%s):\n%sDIP { DROP }; # remove %s\n"
        i v (snd (compile_typed_expr ((Some v, t_v)::stk) ie)) v in
    (None, it)::stk, code ^ Compile_composite.sum_case (List.mapi f cases)

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
  | _ -> Compile_composite.sum_data i n (compile_data e)

let compile_contract i_contract = 
  match i_contract.I.code with
  | I.ELambda([(v_param, t_param)], (e_body, t_body as body)), t_lambda ->
    Stk_S.reset();

    let stk = [(Some v_param, t_param); (Some "@", i_contract.I.storage_type)] in
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

    let init_data = match i_contract.I.storage_init with None -> None | Some et_user_store ->
      (* Actual storage is the product of stack saving store and user-defined store. *)
      let et_unit = I.EProduct[], I.TProduct(Some("unit", []), lazy []) in
      let et_compiler_store = I.ESum(0, List.length saved_stacks, et_unit), t_compiler_store in
      let et_stores = I.EProduct[et_compiler_store; et_user_store], t_stores in
      Some (compile_data et_stores) in

    let code = patch_stack_store_operations code in
    let code = Code_format.indent '{' '}' code in
    code, init_data

  | _ -> unsound "Bad contract type"

