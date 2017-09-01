open Printf
open Utils
module I = Intermediate
module P = String_of_intermediate

let _DEBUG_ =true
let debug_indent = ref 0

type stack = (I.evar option * I.etype) list

let dup n = "D"^String.make n 'U'^"P"
let rec peek = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "DIP { %s }; SWAP" (peek (n-1))
let rec poke = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "SWAP; DIP { %s }" (poke (n-1))

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
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_expr ie);
    incr debug_indent
  end;
  let stk, code = match ie with
  | I.ELit x -> (match it with I.TPrim(t_name, []) -> (None, it)::stk, sprintf "PUSH %s %s" t_name x | _ -> unsound "litteral type")
  | I.EId name -> begin match get_level stk name with
    | Some n -> (Some name, it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (None, it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | I.ELambda(params, body) -> compile_ELambda stk params body it
  | I.ELetIn(v, ie0, ie1) ->
    let stk, c0 = compile_typed_expr stk ie0 in
    let stk = (Some v, snd ie0) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_typed_expr stk ie1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, c0^"# let "^v^" = ... in ...\n"^c1^"DIP { DROP } # remove "^v^"\n"
  | I.EApp(f, args) -> compile_EApp stk f args it
  | I.EProduct fields ->
    let stk', code = List.fold_left
      (fun (stk, code) field -> let stk, code' = compile_typed_expr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (None, it)::stk, code^Compile_composite.tuple(List.length fields)
  | I.ESum(i, n, content) -> compile_ESum stk i n content it
  | I.EProductGet(ie, i, n) ->
    let _, code = compile_typed_expr stk ie in
    (None, it)::stk, code^Compile_composite.product_get i n
  | I.EProductSet(e0, i, n, e1) ->
    let stk', c0 = compile_typed_expr stk e0 in
    let stk', c1 = compile_typed_expr stk e1 in (* TODO sure that the stask can't be messsed up? *)
    (None, it)::stk, c0^c1^Compile_composite.product_set i n
  | I.EStoreSet(i, e0, e1) -> not_impl "store set"
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
    "now", "NOW"; "unit", "UNIT"; "fail", "FAIL";
    "contract-create", "CREATE_CONTRACT"; "contract-create-account", "CREATE_ACCOUNT"; "contract-get", "DEFAULT_ACCOUNT"; "contract-manager", "MANAGER";
    "self-amount", "AMOUNT"; "self-contract", "SELF"; "self-balance", "BALANCE"; "self-steps-to-quota", "STEPS_TO_QUOTA";
    "crypto-hash", "H";
    "set-mem", "MEM"; "set-update", "UPDATE";
    "map-mem", "MEM"; "map-get", "GET"; "map-update", "UPDATE"; "map-map", "MAP";
    "list-map", "MAP";
    "EQ", "CMPEQ"; "LT", "CMPLT"; "LE", "CMPLE"; "GE", "CMPGE"; "GT", "CMPGT"; "CONCAT", "CONCAT"
  ] in

  let simple_operators = [
    "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"; "AND"; "OR"; "XOR"] in

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
    | [contract; amount; contract_arg] -> compile_contract_call stk contract amount contract_arg t_result
    | _ -> unsupported "partial application of contract-call"
    end
  | (I.EId(name), t_f) -> begin match get_level stk name with
    | Some n -> not_impl "user-defined lambda" (* user-defined lambda *)
    | None -> (None, t_result)::stk, compile_primitive stk name args t_result
    end
  | _ -> unsound "Applying a non-function"

and compile_contract_call stk contract amount contract_arg t_result =
      (* in Michelson: \/ param result storage:  param -> tez -> contract param result -> storage -> result*storage *)
      (* in Lamtez: \/ param result: contract -> param -> tez -> result *)
      let stack_storage_type =
        let stack_type = List.map snd stk in
        let rec f = function [_] -> [] | t::x -> t::f x | [] -> assert false in
        I.TProduct(None, lazy (f stack_type)) in
      let stk' =
        let rec f = function [x] -> [x] | _::x -> f x | [] -> assert false in
        f stk in
      let stk', c0 = compile_typed_expr stk' contract in
      let stk', c1 = compile_typed_expr stk' amount in
      let stk', c2 = compile_typed_expr stk' contract_arg in

      let store_stack = sprintf "2TUPLE %d; 2SUM %d/%d; PRODUCT_SET %d/%d" (List.length stk - 1) (-1) (-1) (-1) (-1) in
      let restore_stack= sprintf "GET_PRODUCT %d/%d; GET_SUM %d/%d; EXPAND_PRODUCT %d" (-1) (-1) (-1) (-1) (List.length stk - 1) in
      (None, t_result)::stk,
      c0^c1^c2^
      "DIIIP { "^store_stack^"} # Save the stack into storage\n"^
      "TRANSFER_TOKENS;\n"^
      "DIP { "^restore_stack^"}"

and compile_EProductSet stk e0 i n e1 = not_impl("product set")

and compile_EStoreSet stk e0 i n e1 e2 = not_impl("store set")

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
      (None, it) ::List.tl stk, code^Compile_composite.sum i n types
    end
  | _ -> unsound "Not a sum type"


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


let compile_contract it_store = function
  | I.ELambda([(param, it_param)], (e_body, t_body as body)), t_lambda ->
    let stk, code = compile_typed_expr [(Some param, it_param); (Some "@", it_store)] body in
    let code = sprintf "DUP; CDR; SWAP; CAR # store/%s split\n%sDIP { %s } # remove %s\nPAIR; # group result and store\n"
      param code (sep_list "; " (fun _ -> "DROP") (List.tl (List.tl (stk)))) param in
    let code = sprintf "parameter %s;\nstorage %s;\nreturn %s;\ncode { %s}\n"
                (compile_etype it_param) (compile_etype it_store) (compile_etype t_body) code in
    let code = Code_format.indent '{' '}' code in
    code
  | _ -> unsound "Bad contract type"
