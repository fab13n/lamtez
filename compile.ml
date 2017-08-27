open Utils
open Interm_of_lamtez

let _DEBUG_ =true
let debug_indent = ref 0

type mExpr =
| MEPrim of string list * mExpr list
| MESeq of mExpr list

type stack = ieVar option list

let s = Printf.sprintf
let slist sep f list = match list with
| [] -> "" 
| x::y -> List.fold_left (fun acc x -> acc^sep^f x) (f x) y

let dup n =
  "D"^String.make n 'U'^"P"

let simple_primitives = [
  "now", "NOW"; "unit", "UNIT"; "fail", "FAIL";
  "contract-create", "CREATE_CONTRACT"; "contract-create-account", "CREATE_ACCOUNT"; "contract-get", "DEFAULT_ACCOUNT"; "contract-manager", "MANAGER";
  "self-amount", "AMOUNT"; "self-contract", "SELF"; "self-balance", "BALANCE"; "self-steps-to-quota", "STEPS_TO_QUOTA"; "self-source", "SOURCE";
  "crypto-hash", "H";
  "set-mem", "MEM"; "set-update", "UPDATE"; 
  "map-mem", "MEM"; "map-get", "GET"; "map-update", "UPDATE"; "map-map", "MAP";
  "list-map", "MAP";
]

let simple_operators = [
  "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"]

let rec get_level stk v = match stk with
| [] -> None
| Some v' :: _ when v=v' -> Some 1
| _ :: stk' -> match get_level stk' v with None -> None | Some n -> Some (n+1)

let rec compile_iType t =
  let c = compile_iType in 
  match t with
  | ITPrim(t, []) -> t
  | ITPrim(t, args) -> s "(%s %s)" t (slist " " c args) 
  | ITLambda(params, result) -> s "(lambda %s %s)" (slist " " c params) (c result)
  | ITProduct(_, lazy []) -> "unit"
  | ITProduct(_, lazy fields) -> Compile_composite.product_type (List.map c fields)
  | ITSum(Some("list", [t']), _) -> s "(list %s)" (c t')
  | ITSum(Some("option", [t']), _) -> s "(option %s)" (c t')
  | ITSum(_, lazy fields) -> Compile_composite.sum_type (List.map c fields)

let rec compile_iTypedExpr (stk:stack) ((e, t): iTypedExpr) : (stack * string) = 
  let c = compile_iTypedExpr stk in
  if _DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^string_of_iExpr e);
    incr debug_indent
  end;
  let stk, code = match e, t with
  | IELit x, ITPrim(t, []) -> None::stk, s "PUSH %s %s" t x
  | IELit _, _ -> unsound "litteral type"
  | IEId name, _ -> 
    begin match get_level stk name with
    | Some n -> None::stk, dup n (* Bound variable *)
    | None -> None::stk, compile_primitive stk name [] t (* Free variable, must be a primitive. *)
    end
  | IELambda([param, tparam], (_, tbody as body)), _ ->
    let ctx, code = compile_iTypedExpr [Some param] body in
      None::stk, s "LAMBDA %s %s { %s }" 
        (compile_iType tparam) (compile_iType tbody) code
  | IELambda(vars, body), _ -> unsupported "nested lambdas"
  | IELetIn(v, e0, e1), _ ->
    let stk, c0 = compile_iTypedExpr stk e0 in
    let stk, c1 = compile_iTypedExpr (Some v :: stk) e1 in
    stk, c0^"; "^c1
  | IEApp((IELambda(params, body), tl), args), _ -> not_impl "apply lambda"
  | IEApp((IEId "contract-call", _), [param; amount; contract; storage]), _ ->
    (* param -> tez -> contract param result -> storage -> result*storage *)
    let code =
      snd(compile_iTypedExpr stk param) ^"; "^
      snd(compile_iTypedExpr (None::stk) amount) ^"; "^
      snd(compile_iTypedExpr (None::None::stk) contract) ^"; "^
      snd(compile_iTypedExpr (None::None::None::stk) storage) ^"; "^
      "DIIIIP { "^List.fold_left (fun acc _ -> acc^"DROP; ") "" stk^"}; "^
      "TRANSFER_TOKENS; PAIR" in
    [None], code (* Now the stack only contains the result and updated storage *)
  | IEApp((IEId(name), tl), args), _ -> begin match get_level stk name with
    | Some n -> not_impl "user-defined lambda" (* user-defined lambda *)
    | None -> None::stk, compile_primitive stk name args t
    end
  | IEApp(f, args), _ -> 
    (* actual, user-defined lambda. M only supports single-param lambdas.
     * I need to turn those back into curried lambda calls. *)
    not_impl "apply(lambda, _)"
  | IEProduct(fields), _ -> 
    None::stk, Compile_composite.product (List.map (fun f -> snd (c f)) fields)
  | IESum(0, 2, content), ITSum(Some("option", [t']), _) ->
    None::stk, "NONE "^compile_iType t'
  | IESum(1, 2, content), ITSum(Some("option", [t']), _) ->
    let stk, code = compile_iTypedExpr stk content in stk, code^"; SOME"
  | IESum(0, 2, content), ITSum(Some("list", [t']), _) ->
    None::stk, "NIL "^compile_iType t'
  | IESum(1, 2, content), ITSum(Some("list", [t']), _) ->
    let stk, code = compile_iTypedExpr stk content in
    stk, code^"; DUP; CAR; SWAP; CDR; CONS"
  | IESum(i, n, content), _ ->
    let _, code = c content in None::stk, code^"; "^Compile_composite.sum i n
  | IEProductGet(e, i, n), _ ->
    let _, code = c e in None::stk, code^"; "^Compile_composite.product_get i n
  | IESumCase(e, cases), _ ->
      begin match t, cases with
      | ITSum(Some("list", [t']), _), [(_, _, if_nil); (v, _, if_cons)] ->
        let _, if_cons = compile_iTypedExpr (Some v::stk) if_cons in
        let _, if_nil = compile_iTypedExpr (stk) if_nil in
        None::stk, s "IF_CONS { PAIR; %s } { %s }" if_cons if_nil
      | ITSum(Some("option", [t']), _), [(_, _, if_none); (v, _, if_some)] ->
        let _, if_some = compile_iTypedExpr (Some v::stk) if_some in
        let _, if_none = compile_iTypedExpr (stk) if_none in
        None::stk, s "IF_SOME { %s } { %s }" if_some if_none
      | _ ->
        let f  (v, t, e)  = snd (compile_iTypedExpr (Some v::stk) e) in
        None::stk,  Compile_composite.sum_case (List.map f cases)
      end
  in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^code)
  end;
  stk, code

and compile_primitive stk name args t = 
  let c_args args = (* Compiles and stacks all arguments, discards resulting stack. *)
    let stk, code = List.fold_left 
      (fun (stk, c) arg -> let stk, c' = compile_iTypedExpr stk arg in stk, c^c'^"; ")
      (stk, "") args in
    code in
  (*  
  let c_arg level arg =
    let rec f stk = function 0 -> stk | n -> f (None::stk) (n-1) in
    compile_iTypedExpr (f stk level) arg in
  *) 
  (*  
  if args != [] then begin match t with
    | ITLambda(params, _) -> if List.length params > List.length args then
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
    | "contract-call" -> not_impl "TRANSFER_TOKEN"
    | "crypto-check" ->
      begin match args with
      | [key; signature; msg] ->
        c_args args ^"PAIR; CHECK" (* key->sig->str / key->sig*str *)
      | [_;_] | [_] | [] -> unsupported "Partially applied CHECK"
      | _ -> unsound "too many check params"
      end
    | "set-empty" -> begin match t with
      | ITPrim("set", [elt]) -> "SET_EMPTY "^compile_iType elt
      | _ -> unsound "set-empty type"
      end
    | "set-reduce" -> not_impl "set-reduce"
    | "map-empty" -> begin match t with
      | ITPrim("map", [k; v]) -> "SET_EMPTY "^compile_iType k^" "^compile_iType v
      | _ -> unsound "map-empty type"
      end
    | "map-reduce" -> not_impl "map-reduce"
    | "list-reduce" -> not_impl "list-reduce"
    | _ -> not_impl ("Primitive "^name^" not implemented")

let compile_contract = function
| IELambda(
  [param, tparam; storage, tstorage], 
  (body, (ITProduct(None, lazy [tresult; tstorage'])) as typed_body)), _
  when tstorage=tstorage' ->
  let stk, code = compile_iTypedExpr [Some storage; Some param] typed_body in
  let code = s "CAR; SWAP; CDR; %s; DIP { %s }" 
    code (sep_list "; " (fun _ -> "DROP") (List.tl stk)) in
  s "parameter %s;\nstorage %s;\nreturn %s;\ncode {\n  %s\n}"
  (compile_iType tparam) (compile_iType tstorage) (compile_iType tresult) code
| _ -> unsound "Bad contract type"
