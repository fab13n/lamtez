open Printf
open Utils
open Interm_of_lamtez

let _DEBUG_ =true
let debug_indent = ref 0

type mExpr =
| MEPrim of string list * mExpr list
| MESeq of mExpr list

type stack = (ieVar option * iType) list

let dup n = "D"^String.make n 'U'^"P"
let rec peek = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "DIP { %s }; SWAP" (peek (n-1))
let rec poke = function 0 -> "" | 1 -> "SWAP" | n -> sprintf "SWAP; DIP { %s }" (poke (n-1))

let rec get_level stk v = match stk with
| [] -> None
| (Some v', _) :: _ when v=v' -> Some 1
| _ :: stk' -> match get_level stk' v with None -> None | Some n -> Some (n+1)



let rec compile_iType t =
  let c = compile_iType in 
  match t with
  | ITPrim(t, []) -> t
  | ITPrim(t, args) -> sprintf "(%s %s)" t (sep_list " " c args) 
  | ITLambda(params, result) -> sprintf "(lambda %s %s)" (sep_list " " c params) (c result)
  | ITProduct(_, lazy []) -> "unit"
  | ITProduct(_, lazy fields) -> Compile_composite.product_type (List.map c fields)
  | ITSum(Some("bool", []), _) -> "bool"
  | ITSum(Some("list", [t']), _) -> sprintf "(list %s)" (c t')
  | ITSum(Some("option", [t']), _) -> sprintf "(option %s)" (c t')
  | ITSum(_, lazy fields) -> Compile_composite.sum_type (List.map c fields)



let rec compile_iTypedExpr (stk:stack) ((ie, it): iTypedExpr) : (stack * string) = 
  if _DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^string_of_iExpr ie);
    incr debug_indent
  end;
  let stk, code = match ie with
  | IELit x -> (match it with ITPrim(t_name, []) -> (None, it)::stk, sprintf "PUSH %s %s" t_name x | _ -> unsound "litteral type")
  | IEId name -> begin match get_level stk name with
    | Some n -> (Some name, it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (None, it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | IELambda(params, body) -> compile_IELambda stk params body it
  | IELetIn(v, ie0, ie1) ->
    let stk, c0 = compile_iTypedExpr stk ie0 in
    let stk = (Some v, snd ie0) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_iTypedExpr stk ie1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, c0^"# let "^v^" = ... in ...\n"^c1^"DIP { DROP } # remove "^v^"\n"
  | IEApp(f, args) -> compile_IEApp stk f args it
  | IEProduct fields ->
    let stk', code = List.fold_left 
      (fun (stk, code) field -> let stk, code' = compile_iTypedExpr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (None, it)::stk, code^Compile_composite.tuple(List.length fields)
  | IESum(i, n, content) -> compile_IESum stk i n content it
  | IEProductGet(ie, i, n) -> 
    let _, code = compile_iTypedExpr stk ie in 
    (None, it)::stk, code^Compile_composite.product_get i n
  | IEProductSet(e0, i, n, e1) ->
    let stk', c0 = compile_iTypedExpr stk e0 in 
    let stk', c1 = compile_iTypedExpr stk e1 in (* TODO sure that the stask can't be messsed up? *)
    (None, it)::stk, c0^c1^Compile_composite.product_set i n
  | IESumCase(test, cases) -> compile_IESumCase stk test cases it
  in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let string_of_stk_item (v, t) = (match v with None -> "" | Some x -> x^": ")^compile_iType t in
  let comment = sep_list ", " string_of_stk_item (List.tl stk) in
  let code = if last_char='\n' then code else code^"; # "^string_of_untyped_iExpr ie^", "^comment^"\n" in
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
    | "self-source" -> begin match t_result with
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
    | "set-empty" -> begin match t_result with
      | ITPrim("set", [elt]) -> "SET_EMPTY "^compile_iType elt
      | _ -> unsound "set-empty type"
      end
    | "set-reduce" -> not_impl "set-reduce"
    | "map-empty" -> begin match t_result with
      | ITPrim("map", [k; v]) -> "SET_EMPTY "^compile_iType k^" "^compile_iType v
      | _ -> unsound "map-empty type"
      end
    | "map-reduce" -> not_impl "map-reduce"
    | "list-reduce" -> not_impl "list-reduce"
    | _ -> not_impl ("Primitive "^name^" not implemented")


and compile_IELambda stk params body it_lambda =
  match params, body with
  | [(v_param, t_param)], (e_body, t_body) ->
    (* TODO check that there's no free variable. *)
    let stk, code = compile_iTypedExpr [Some v_param, t_param] body in
    (None, it_lambda)::List.tl stk, sprintf "LAMBDA %s %s { %s }" 
      (compile_iType t_param) (compile_iType t_body) code
  | _::_, _ -> unsupported "nested (multi-parameter) lambdas"
  | [], _ -> unsound "IELambda without parameter?!"


and compile_IEApp stk f args t_result = match f with
  | IELambda([(params, body)], et0), t_lambda -> not_impl "apply literal lambda"
  | (IEId "contract-call", _) -> begin match args with
    | [contract_arg; amount; contract; storage] ->
      (* param -> tez -> contract param result -> storage -> result*storage *)
      let stk', c0 = compile_iTypedExpr stk contract_arg in
      let stk', c1 = compile_iTypedExpr stk' amount in
      let stk', c2 = compile_iTypedExpr stk' contract in
      let stk', c3 = compile_iTypedExpr stk' storage in
      [None, t_result],
      c0^c1^c2^c3^  
      "DIIIIP { "^sep_list "; " (fun _ -> "DROP") stk^"} # Clean rest of stack \n"^
      "TRANSFER_TOKENS; PAIR"
    | _ -> unsupported "partial application of contract-call"
    end
  | (IEId(name), t_f) -> begin match get_level stk name with
    | Some n -> not_impl "user-defined lambda" (* user-defined lambda *)
    | None -> (None, t_result)::stk, compile_primitive stk name args t_result
    end
  | _ -> unsound "Applying a non-function"


and compile_IESum stk i n content it =
  let ct = compile_iType in
  match it with 
  | ITSum(Some(sum_type_name, sum_type_args), lazy types) -> 
    begin match sum_type_name, sum_type_args, i, n with
    | "bool",   [],   0, 2 -> (None, it) :: stk, "PUSH bool False"
    | "bool",   [],   1, 2 -> (None, it) :: stk, "PUSH bool True"
    | "option", [t'], 0, 2 -> (None, it) :: stk, "NONE "^compile_iType t'
    | "list",   [t'], 0, 2 -> (None, it) :: stk, "NIL "^compile_iType t'
    | "option", [t'], 1, 2 -> 
      let stk, code = compile_iTypedExpr stk content in (None, it)::List.tl stk, code^"SOME"
    | "list",   [t'], 1, 2 -> 
      let stk, code = compile_iTypedExpr stk content in (None, it)::List.tl stk, code^"DUP; CAR; SWAP; CDR; CONS"
    | _ ->
      let types = List.map compile_iType types in
      let stk, code = compile_iTypedExpr stk content in
      (None, it) ::List.tl stk, code^Compile_composite.sum i n types
    end
  | _ -> unsound "Not a sum type"


and compile_IESumCase stk test cases it =
  let stk, code = compile_iTypedExpr stk test in
  let stk = List.tl stk in (* cases are executed with the test removed from stack. *)
  let sum_type_name = match snd test with ITSum(Some (name, _), _) -> name | _ -> unsound "Not a sum type" in
  match sum_type_name, cases with
  | "bool", [(_, _, if_false); (v, _, if_true)] ->
    let _, if_false = compile_iTypedExpr stk if_false in
    let _, if_true = compile_iTypedExpr (stk) if_true in
    (None, it)::stk, sprintf "%sIF { %s}\n{ %s}" code if_true if_false (* TODO make sure unit-bouns variables in cases aren't used *)
  | "list", [(_, _, if_nil); (v, t_v, if_cons)] ->
    let _, if_cons = compile_iTypedExpr ((Some v, t_v)::stk) if_cons in
    let _, if_nil = compile_iTypedExpr stk if_nil in
    (None, it)::stk, sprintf "%sIF_CONS { PAIR; # %s\n %sDIP { DROP }# remove cons\n}\n{ %s}" code v if_cons if_nil
  | "option", [(_, _, if_none); (v, t_v, if_some)] ->
    let _, if_some = compile_iTypedExpr ((Some v, t_v)::stk) if_some in
    let _, if_none = compile_iTypedExpr stk if_none in
    (None, it)::stk, sprintf "%sIF_NONE { %s}\n{ # %s\n %sDIP { DROP } # remove %s\n}" code if_none v if_some v
  | _ ->
    let f i (v, t_v, ie)  =
      sprintf "# | <%d>(%s):\n%sDIP { DROP }; # remove %s\n"
        i v (snd (compile_iTypedExpr ((Some v, t_v)::stk) ie)) v in
    (None, it)::stk, code ^ Compile_composite.sum_case (List.mapi f cases)



let compile_contract = function
  | IELambda(
    [(param, t_param); (storage, t_storage)], 
    (e_body, (ITProduct(None, lazy [t_result; t_storage'])) as body)), _
    when t_storage=t_storage' ->
    let stk, code = compile_iTypedExpr [(Some storage, t_storage); (Some param, t_param)] body in
    let code = sprintf "DUP; CAR; SWAP; CDR # %s/%s split\n%sDIP { %s } # remove %s and %s\n"
      param storage code (sep_list "; " (fun _ -> "DROP") (List.tl stk)) param storage in
    let code = sprintf "parameter %s;\nstorage %s;\nreturn %s;\ncode { %s}\n"
                (compile_iType t_param) (compile_iType t_storage) (compile_iType t_result) code in
    let code = Code_format.indent '{' '}' code in
    code
  | _ -> unsound "Bad contract type"
