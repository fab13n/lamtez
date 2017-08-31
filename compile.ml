open Printf
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

let rec peek = function
| 0 -> "" | 1 -> "SWAP"
| n -> sprintf "DIP { %s }; SWAP" (peek (n-1))

let rec poke = function
| 0 -> "" | 1 -> "SWAP"
| n -> sprintf "SWAP; DIP { %s }" (poke (n-1))

let simple_primitives = [
  "now", "NOW"; "unit", "UNIT"; "fail", "FAIL";
  "contract-create", "CREATE_CONTRACT"; "contract-create-account", "CREATE_ACCOUNT"; "contract-get", "DEFAULT_ACCOUNT"; "contract-manager", "MANAGER";
  "self-amount", "AMOUNT"; "self-contract", "SELF"; "self-balance", "BALANCE"; "self-steps-to-quota", "STEPS_TO_QUOTA";
  "crypto-hash", "H";
  "set-mem", "MEM"; "set-update", "UPDATE"; 
  "map-mem", "MEM"; "map-get", "GET"; "map-update", "UPDATE"; "map-map", "MAP";
  "list-map", "MAP";
  "EQ", "CMPEQ"; "LT", "CMPLT"; "LE", "CMPLE"; "GE", "CMPGE"; "GT", "CMPGT"
]

let simple_operators = [
  "ADD"; "SUB"; "MUL"; "EDIV"; "LSR"; "LSL"; "NOT"; "NEG"; "ABS"; "AND"; "OR"; "XOR"]

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
  let c = compile_iTypedExpr in
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
    (* TODO check that there's no free variable. *)
    let ctx, code = c [Some param] body in
      None::stk, s "LAMBDA %s %s { %s }" 
        (compile_iType tparam) (compile_iType tbody) code
  | IELambda(vars, body), _ -> unsupported "nested (multi-parameter) lambdas"
  | IELetIn(v, e0, e1), _ ->
    let stk, c0 = c stk e0 in
    let stk, c1 = c (Some v :: List.tl stk) e1 in
    stk, c0^"# := "^v^"\n"^c1^"DIP { DROP } # remove "^v^"\n"
  | IEApp((IELambda(params, body), tl), args), _ -> not_impl "apply lambda"
  | IEApp((IEId "contract-call", _), [contract_arg; amount; contract; storage]), _ ->
    (* param -> tez -> contract param result -> storage -> result*storage *)
    let stk', c0 = c stk contract_arg in
    let stk', c1 = c stk' amount in
    let stk', c2 = c stk' contract in
    let stk', c3 = c stk' storage in
    [None],
    c0^c1^c2^c3^  
    "DIIIIP { "^sep_list "; " (fun _ -> "DROP") stk^"} # Clean rest of stack \n"^
    "TRANSFER_TOKENS; PAIR"
  | IEApp((IEId(name), tl), args), _ -> begin match get_level stk name with
    | Some n -> not_impl "user-defined lambda" (* user-defined lambda *)
    | None -> None::stk, compile_primitive stk name args t
    end
  | IEApp(f, args), _ -> 
    (* actual, user-defined lambda. M only supports single-param lambdas.
     * I need to turn those back into curried lambda calls. *)
    not_impl "apply(lambda, _)"
  | IEProduct(fields), _ ->
    let stk', code = List.fold_left 
      (fun (stk, code) field -> let stk, code' = compile_iTypedExpr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    None::stk, code^Compile_composite.tuple(List.length fields)
  | IESum(0, 2, content), ITSum(Some("bool", []), _) -> None::stk, "PUSH bool False"
  | IESum(1, 2, content), ITSum(Some("bool", []), _) -> None::stk, "PUSH bool True"
  | IESum(0, 2, content), ITSum(Some("option", [t']), _) ->
    None::stk, "NONE "^compile_iType t'
  | IESum(1, 2, content), ITSum(Some("option", [t']), _) ->
    let stk, code = compile_iTypedExpr stk content in stk, code^"SOME"
  | IESum(0, 2, content), ITSum(Some("list", [t']), _) ->
    None::stk, "NIL "^compile_iType t'
  | IESum(1, 2, content), ITSum(Some("list", [t']), _) ->
    let stk, code = compile_iTypedExpr stk content in
    stk, code^"DUP; CAR; SWAP; CDR; CONS"
  | IESum(i, n, content), _ ->
    let _, code = c stk content in 
    None::stk, code^Compile_composite.sum i n
  | IEProductGet(e, i, n), _ ->
    let _, code = c stk e in 
    None::stk, code^Compile_composite.product_get i n
  | IEProductSet(e0, i, n, e1), _ ->
    let stk', c0 = c stk e0 in
    let stk', c1 = c stk e1 in
    None::stk, c0^c1^Compile_composite.product_set i n
  | IESumCase((e_test, t_test) as test, cases), _ ->
     let stk, code = compile_iTypedExpr stk test in
     let stk = List.tl stk in (* cases are executed with the test removed from stack. *)
      begin match t_test, cases with
      | ITSum(Some("bool", []), _), [(_, _, if_false); (v, _, if_true)] ->
        let _, if_false = compile_iTypedExpr stk if_false in
        let _, if_true = compile_iTypedExpr (stk) if_true in
        None::stk, s "%sIF { %s} { %s}" code if_true if_false (* TODO make sure variables aren't used *)
      | ITSum(Some("list", [t']), _), [(_, _, if_nil); (v, _, if_cons)] ->
        let _, if_cons = compile_iTypedExpr (Some v::stk) if_cons in
        let _, if_nil = compile_iTypedExpr (stk) if_nil in
        None::stk, s "%sIF_CONS { PAIR; # %s\n %sDIP { DROP }# remove cons\n} { %s}" code v if_cons if_nil
      | ITSum(Some("option", [t']), _), [(_, _, if_none); (v, _, if_some)] ->
        let _, if_some = compile_iTypedExpr (Some v::stk) if_some in
        let _, if_none = compile_iTypedExpr (stk) if_none in
        None::stk, s "%sIF_NONE { %s} { # %s\n %sDIP { DROP } # remove %s\n}" code if_none v if_some v
      | _ ->
        let f  (v, t, e)  = snd (compile_iTypedExpr (Some v::stk) e)^"DIP { DROP } # remove "^v^"\n" in
        None::stk, code ^ Compile_composite.sum_case (List.map f cases)
      end
  in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let stk_comment = " : "^String.concat " : " (List.map (function None -> "." | Some x -> x) (List.tl stk)) in
  let code = if last_char='\n' then code else code^"; # "^string_of_untyped_iExpr e^stk_comment^"\n" in
  stk, code


and compile_primitive stk name args t = 
  let c_args args = (* Compiles and stacks all arguments, discards resulting stack. *)
    let stk, code = List.fold_left 
      (fun (stk, c) arg -> let stk, c' = compile_iTypedExpr stk arg in stk, c^c')
      (stk, "") args in
    code in
  (*  
  let c_arg level arg =
    let rec f stk = function 0 -> stk | n -> f (None::stk) (n-1) in
    compile_iTypedExpr (f stk level) arg in
  *) 
  (*  
  if args <> [] then begin match t with
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
    | "self-source" -> begin match t with
      | ITPrim("contract", [param; result]) -> "SOURCE "^compile_iType param^" "^compile_iType result
      | _ -> unsupported ("Cannot guess the type of contract parameters, please annotate")
      end
    | "crypto-check" ->
      begin match args with
      | [key; signature; msg] ->
        c_args args ^"DIP { PAIR }; CHECK_SIGNATURE" (* key->sig->str / key->sig*str *)
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
  let code = s "DUP; CAR; SWAP; CDR # %s/%s split\n%sDIP { %s } # stack cleanup\n"
    param storage code (sep_list "; " (fun _ -> "DROP") (List.tl stk)) in
  let code = s "parameter %s;\nstorage %s;\nreturn %s;\ncode { %s}\n"
               (compile_iType tparam) (compile_iType tstorage) (compile_iType tresult) code in
  let code = Code_format.indent code in
  code
| _ -> unsound "Bad contract type"
