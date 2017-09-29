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
  | I.TLambda(prm, res, true) -> sprintf "(lambda %s %s)" (c prm) (c res)
  | I.TLambda(prm, res, false) -> not_impl "compile closure type"
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
module Stk: sig
    type item
    type t = item list
    val of_expr:           I.expr -> I.etype -> item
    val of_type:           string -> I.etype -> item
    val of_var:            string -> ?expr: I.expr -> I.etype -> item
    val string_of_item:    item -> string
    val type_of_item:      item -> I.etype
    val get_level:         t -> string -> int option
    val type_of_var:       t -> string -> I.etype option
    val typed_expr_of_var: t -> string -> I.typed_expr option
  end = struct
    type item_kind = Anon | Var
    type item = item_kind * string * I.expr option * I.etype
    type t = item list
    let of_expr expr etype       = Anon, String_of_intermediate.string_of_untyped_expr expr, Some expr, etype
    let of_type hint etype       = Anon, hint, None, etype
    let of_var  name ?expr etype = Var, name, expr, etype
    let string_of_item (_, s, _, _) = s
    let type_of_item(_, _, _, t) = t
    let rec get_level stk name = match stk with
      | [] -> None
      | (Var, level_name, _, _) :: _ when level_name=name -> Some 1
      | _ :: stk' -> 
        match get_level stk' name with
        | None -> None 
        | Some n -> Some (n+1)
    let rec get_item stk name = 
      let pred = function (Var, name', _, _) when name'=name -> true | _ -> false in
      try Some(List.find pred stk) with Not_found -> None
    let type_of_var stk v = match get_item stk v with Some(Var, name, _, t) -> Some t | _ -> None
    let rec typed_expr_of_var stk v = match get_item stk v with
      | Some(Var, name, Some I.EId v', _) -> typed_expr_of_var stk v' (* TODO Can this recursive case happen? *)
      | Some(Var, name, Some e, t) -> Some(e, t)
      | _ -> None
end

let rec compile_typed_expr (stk:Stk.t) ((ie, it): I.typed_expr) : (Stk.t * string) =
  if !_DEBUG_ then begin
    print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^
      P.string_of_untyped_expr ie^" with "^sep_list ":" Stk.string_of_item stk);
    (* print_endline (String.make (2 * !debug_indent) ' '^"Compiling "^P.string_of_expr ie); *)
    incr debug_indent
  end;
  let stk, code = match ie with
  | I.ELit value -> 
    let type_name = match it with I.TPrim(t, _) -> t | _ -> unsound "litteral" in
    Stk.of_expr ie it :: stk, sprintf "PUSH %s %s" type_name value
  | I.EId name -> begin match Stk.get_level stk name with
    | Some n -> (Stk.of_var name it)::stk, dup n (* Bound variable; remember its name on stack too (might help making shorter DUU*Ps). *)
    | None -> (Stk.of_expr ie it)::stk, compile_primitive stk name [] it (* Free variable, must be a primitive. *)
    end
  | I.EColl(Ast.CList, list) -> compile_EColl_CList stk list it
  | I.EColl(Ast.CMap,  list) -> compile_EColl_CMap  stk list it
  | I.EColl(Ast.CSet,  list) -> compile_EColl_CSet  stk list it
  | I.ELambda(v_prm, t_prm, [], res)  -> compile_ELambda_combinator stk v_prm t_prm res it
  | I.ELambda(v_prm, t_prm, env, res) -> compile_ELambda_closure stk v_prm t_prm env res it
  | I.ELet(v, et0, et1) -> compile_ELet stk v et0 et1
  | I.EApp(f, args) -> compile_EApp stk f args it
  | I.EProduct [] -> (Stk.of_expr ie it) :: stk, "UNIT"
  | I.EProduct fields ->
    let stk', code = List.fold_left
      (fun (stk, code) field -> let stk, code' = compile_typed_expr stk field in stk, code^code')
      (stk, "") (List.rev fields) in
    (Stk.of_expr ie it)::stk, code^MoC.product_make(List.length fields)
  | I.ESum(i, n, content) -> compile_ESum stk i n content it
  | I.EProductGet(et0, i, n) ->
    let _, code = compile_typed_expr stk et0 in
    (Stk.of_expr ie it)::stk, code^MoC.product_get i n
  | I.EProductSet(et0, i, n, et1) ->
    let stk', c0 = compile_typed_expr stk et0 in
    let stk', c1 = compile_typed_expr stk et1 in (* TODO sure that the stask can't be messsed up? *)
    (Stk.of_expr ie it)::stk, c0^c1^MoC.product_set i n
  | I.EStoreSet(i, et0, et1) -> compile_EStoreSet stk i et0 et1
  | I.ESumCase(test, cases) -> compile_ESumCase stk test cases it
  in
  if !_DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: "^Code_format.single_line code)
  end;
  let last_char = String.get code (String.length code -1)  in
  let comment = sep_list ":" Stk.string_of_item stk in
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

and compile_ELet stk v et0 et1 =
    let stk, c0 = compile_typed_expr stk et0 in
    let stk = Stk.of_var v ~expr:(fst et0) (snd et0) :: List.tl stk in (* name the value just computed *)
    let stk, c1 = compile_typed_expr stk et1 in
    let stk = match stk with r :: v :: stk -> r :: stk | _ -> unsound "stack too shallow" in
    stk, sprintf "%s# let %s = %s\n%sDIP{ DROP } # remove %s\n"
      c0 v (String_of_intermediate.string_of_untyped_expr @@ fst et0) c1 v

and compile_EColl_CList stk list t_list =
  let t_elt = match t_list with I.TSum((Some("list", [t_elt]), lazy _)) -> t_elt | _ -> assert false in
  let stk = (Stk.of_type "(list ...)"  t_list) :: stk in
  let rec f = function
    | [] -> sprintf "NIL %s;\n" (compile_etype t_elt)
    | a :: b -> 
       sprintf "%s%sCONS;\n" (f b) (snd @@ compile_typed_expr stk a) 
  in
  stk, f list

and compile_EColl_CMap stk list t_map = 
  let t_k, t_v = match t_map with I.TPrim("map", [t_k; t_v]) -> t_k, t_v | _ -> assert false in
  let stk = (Stk.of_type "(map ...)"  t_map) :: stk in
  let rec f = function
    | [] -> sprintf "EMPTY_MAP %s %s;\n" (compile_etype t_k) (compile_etype t_v)
    | [_] -> assert false
    | k :: v :: rest -> 
      sprintf "%s%sSOME;\n%sUPDATE;\n" (f rest) (snd @@ compile_typed_expr stk v) (snd @@ compile_typed_expr stk k)
  in stk, f list

and compile_EColl_CSet stk list t_set = 
  let t_elt = match t_set with I.TPrim("set", [t_elt]) -> t_elt | _ -> assert false in
  let stk = (Stk.of_type "(set ...)"  t_set) :: stk in
  let rec f = function
    | [] -> sprintf "EMPTY_SET %s;\n" (compile_etype t_elt)
    | a :: b -> 
      let _, c = compile_typed_expr stk a in
      sprintf "%sPUSH bool True;\n%sUPDATE;\n" (f b) c
  in stk, f list

and compile_ELambda_combinator stk v_prm t_prm res it =
  let inner_stk = [Stk.of_var v_prm t_prm] in
  let _, code = compile_typed_expr inner_stk res in
  let cleanup = "DIP { DROP }; # remove "^v_prm^"\n" in
  (Stk.of_type "lambda" it)::stk, 
  sprintf "LAMBDA %s %s { %s%s }"
    (compile_etype t_prm) (compile_etype (snd res)) code cleanup

(* 
(* return the closure environment of a term, i.e. the list of the variables,
 * with their type, defined outside of the term but used inside the term. *)
and get_closure_env (stk: Stk.t) ?(except=[]) et =
  let except = except @ Standard_ctx.globals in
  let free_vars = I.get_free_evars ~except et in
  (* Retrieve var type from var name in stack *)
  (* TODO beta-reducing closed variables whose value is known would allow to
   * turn some closures into combinatorial functions. *)
  let et_of_v v = match Stk.get_level stk v with
    | None -> assert false
    | Some n -> match List.nth stk (n-1) with
      | SVar(id, e, t) -> id, t
      | _ -> assert false
  in
  List.map et_of_v free_vars *)

(* Closures are compiled as `(env, lambda)`; since closure applications recombine
 * the environment and argument as `(arg, env)`, the lambda body must unwrap
 * them before running the user code.
 *)  
and compile_ELambda_closure stk v_prm t_prm env res it =

  print_endline("Entering cELc: "^sep_list ":" Stk.string_of_item stk);

  (* Generate the product holding the closure env. *)
  let e_prod = I.EProduct(List.map (fun (v,t) -> I.EId v, t) env) in
  let t_prod = I.TProduct(None, lazy (List.map snd env)) in
  let stk, c_env_make = compile_typed_expr stk (e_prod, t_prod) in

  (* Lambda active code *)
  print_endline("Compile closure with env vars "^sep_list ", " fst env);
  let stk_l = List.map (fun (v, t) -> Stk.of_var v t) env in (* push env vars *)
  let stk_l = (Stk.of_var v_prm t_prm) :: stk_l in           (* push argument *)
  let stk_l, c_lambda = compile_typed_expr stk_l res in      (* Compile code  *)

  (* Env splitting code *)
  let n = List.length env in
  let c_env_split = MoC.product_split n in

  (* Env clean-up code *)
  let rec drops = (* drop env vars and argument *)
    let rec f = function 1 -> "DROP" | n -> "DROP; "^f (n-1) in f (n+1) in

  (* Function body with closure management code around *)
  let c_body = sprintf 
    "DUP; CAR; # arg\nDIP { CDR; %s }; # open closure\n%sDIP { %s } # Remove arg+closure vars\n" 
    c_env_split c_lambda drops in

  let t_param_pair = I.TProduct(None, lazy [t_prm; t_prod]) in
  let code = sprintf 
    "%s # Closure env; \nLAMBDA %s %s { %s }; # Closure code\nPAIR; # Closure"
    c_env_make (compile_etype t_param_pair) (compile_etype (snd res)) c_body in

    print_endline("Leaving cELc: List.tl "^sep_list ":" Stk.string_of_item stk);

  let stk = Stk.of_type "closure" it :: List.tl stk in

  stk, code  

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


and compile_EApp_closure stk f arg t_result =
  (* The closure is encodede as a `(f, env)` pair, which must be split
   * and recombined to call `f` with `(arg, env)` as its argument. *)

  (* TODO: need to erase the environment from closure type: 
   * `type closure a b = (∃e): ((a×e)->b) × e`
   * Can't be expressed in simply-typed lambda calculus, but they can be wrapped
   * in a big, contract-wide sum type.
   *)
  let stk0 = stk in
  let stk, c_closure = compile_typed_expr stk f in
  let stk, c_arg     = compile_typed_expr stk arg in
  let code = sprintf "%sDUP; CAR; SWAP; CDR # env:f\n%s PAIR; # (arg,env):f\nEXEC"
    c_closure c_arg in
  (Stk.of_type "call" t_result) :: stk0, code

and compile_EApp_combinator stk f arg t_result =
  let stk0 = stk in
  let stk, c_func = compile_typed_expr stk f in
  let stk, c_arg  = compile_typed_expr stk arg in
  (Stk.of_type "call" t_result) :: stk0, c_func^c_arg^"EXEC"

and compile_list_rev_map stk param_id param_type body list =
let a_type_name = compile_etype param_type in
let b_type_name = compile_etype (snd body) in
let stk_func_body, stk_list_a = 
    let hd_a = Stk.of_var param_id param_type
    and tl_a = Stk.of_type "tl_a" (I.TPrim("list", [param_type]))
    and list_b = Stk.of_type "list_b" (I.TPrim("list", [snd body])) in      
    hd_a :: tl_a :: list_b :: stk,
    list_b :: stk in
  let _, code_body = compile_typed_expr stk_func_body body in
  let _, code_list_a = compile_typed_expr stk_list_a list in
  let stk = Stk.of_type "list_b" (I.TPrim("list", [snd body])) :: List.tl stk in
  let code = 
    "# reverse list map # list_a:...\n"^
    sprintf "NIL %s; # list_b:...\n" b_type_name^
    code_list_a^
    "PUSH bool True; # True:list_a:list_b:...\n" ^
    "LOOP { # list_a:list_b:...\n"^
    "IF_CONS { # hd_a:tl_a:list_b:...\n"^
    code_body^
    "DIP { DROP; SWAP }; # Remove hd_a => hd_b:list_b:tl_a:...\n"^
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

and compile_list_map stk v_prm t_prm body list =
  let stk, code = compile_list_rev_map stk v_prm t_prm body list in
  stk, code^"\n"^compile_rev_list stk (snd body)


and compile_list_reduce stk v_prm t_prm v_elt t_elt v_acc t_acc res acc0 list =
  let stk, acc0 = compile_typed_expr stk acc0 in
  let result_stk = stk in
  let stk, code_list = compile_typed_expr stk list in
  let stk, code_body = compile_typed_expr (Stk.of_type "hd" t_elt :: stk) res in
  let code = 
    acc0^
    code_list^
    "PUSH bool True # True:list:acc:...\n"^
    "LOOP { #list:acc:...\n"^
    "IF_CONS { # hd:tl:acc:...\n"^
    code_body^ (* acc':hd:tl:acc:... *)
    "DIP { DROP; DIP { DROP } } # acc:tl:...\n"^
    "PUSH bool True; # True:acc:tl:...\n"^
    "} { # acc:...\n"^
    "DIP { NIL %s; PUSH bool False; } # False:acc:Nil:...\n"^
    "} # acc:Nil:...\nDIP { DROP }; # Reduced => acc:...\n" in
    result_stk, code

(* From a multi-parameter I.Elambda, retrieve the individual parameters
 * which have already been compiled into `let x=%n.0; ... let z=%n.i; body`.
 * This is used when we want to beta-reduce an application, e.g. replace
 * a `map` or `reduce` operation with a `LOOP`, allowing access to outer
 * variables.
 *
 * Takes a param name and lambda body, returns a list of `(v_prm, t_prm)`
 * parameters and 
 *
 * TODO: might not work properly in case of deep matching. Such cases might
 *   force to reorder the nested `let` statements. Another way would be
 *   to ensure that `compile_pattern` puts deeper lets deeper in the
 *   resulting term.
 *
 * TODO: in case of failure, recompose the list with the expected number
 *   of parameters, e.g. `[v0,t0; v1,t1; v2,t2], let v=(v0, v1, v2); body`
 *   if 3 parameters were expected.
 *)
and extract_lambda_params v_prm t_prm res =
  let rec f = function
    | I.ELet(x, (I.EProductGet((I.EId v, _), i, n), _), body) when v=v_prm ->
      let lst, body, _ = f (fst body) in (i, x) :: lst, body, n
    | body -> [], body, 0 in
  match f res with
  | [], body, 0 ->
    [v_prm, t_prm], body
  | params, body, n ->
    let types = match t_prm with
      | I.TProduct(_, lazy l) -> l 
      | _ -> unsound "multi-param lambda type" in
    let g i t = try List.assoc i params, t with Not_found -> Ast.fresh_var(), t in
    let params = List.mapi g types in
    params, body

and compile_EApp stk (e_f, t_f) (e_arg, t_arg as arg) t_result =
  (* Try to retrieve lambda's litteral value *)
  let litteral_lambda = match e_f with
  | I.ELambda(v_prm, t_prm, env, res) -> Some(v_prm, t_prm, env, res)
  | I.EId name -> begin match Stk.typed_expr_of_var stk name with
    | Some(I.ELambda(v_prm, t_prm, env, res), _) -> Some(v_prm, t_prm, env, res)
    | Some _ -> unsound "Applying a non-lambda"
    | None -> None
  end
  | _ -> None in

  match e_f, t_f, e_arg with

  (* Convert litteral I.ELambda into I.ELet *)
  | I.ELambda(v_prm, t_prm, env, res), _, _ -> 
    let let_in_expr = I.ELet(v_prm, arg, res) in
    print_endline("beta-reduce litteral lambda");
    compile_typed_expr stk (let_in_expr, snd res)

  | I.EId "contract-call", _, I.EProduct[contract; contract_arg; amount] -> 
      compile_contract_call stk contract contract_arg amount t_result

  | I.EId "list-map", _, I.EProduct[list; func] ->
    begin match litteral_lambda with
    | Some(v_prm, t_prm, _, res) -> compile_list_map stk v_prm t_prm res list
    | None -> not_impl ""
    end

  | I.EId "list-reduce", _, I.EProduct[list; acc0; func] ->
    begin match litteral_lambda with
    | Some(v_prm, t_prm, _, res) ->
      begin match extract_lambda_params v_prm t_prm (fst res) with
      | [v_elt, t_elt; v_acc, t_acc], f_body  ->
         compile_list_reduce stk v_prm t_prm v_elt t_elt v_acc t_acc res acc0 list
      | _ -> unsound "reduce parameters"
      end
    | None -> not_impl "list-reduce of unknown function"
    end

  (* Unbound variables must be primitives. *)
  | I.EId(name), _, _ when Stk.get_level stk name = None ->
    let args : (I.expr * I.etype) list = match arg with
    | I.EProduct(et_list), _ -> et_list 
    | e, t -> [e,t]
    in
    Stk.of_type name t_result :: stk, compile_primitive stk name args t_result
    
  (* Function to apply is an identifier containing a closure. *)
  | I.EId(name), I.TLambda(t_prm, t_res, false), _ ->
    begin match Stk.typed_expr_of_var stk name with

    (* Lambda closure => translate into a let-in *)
    | Some(I.ELambda(v_prm, t_prm, env, res), _) when env <> [] ->
      let let_in_expr = I.ELet(v_prm, arg, res) in
      print_endline("beta-reduce closure");
      print_endline(sep_list ":" Stk.string_of_item stk);
      compile_typed_expr stk (let_in_expr, snd res)    

    | Some _ -> unsound "Closure type"

    (* Unknown closure => apply it. *)
    | None -> compile_EApp_closure stk (e_f, t_f) (e_arg, t_arg) t_res
    end
  
  (* Function to apply is an identifier containing a lambda combinator. *)
  | I.EId(name), I.TLambda(t_prm, t_res, true), _ ->
    compile_EApp_combinator stk (e_f, t_f) (e_arg, t_arg) t_res

  | _ -> unsound "Apply non-lambda"

and compile_contract_call stk contract contract_arg amount t_result =
  (* in Michelson: param : tez : contract param result : storage : [] -> result : storage : [] *)
  (* in Lamtez: \/ param result: contract -> param -> tez -> result *)

  let stack_storage_type = (* All of the stack, except the final user storage *)
    let rec but_last = function [_] -> [] | t::x -> t::but_last x | [] -> assert false in
    List.map Stk.type_of_item (but_last stk) in

  let stk', c0 = compile_typed_expr stk contract in
  let stk', c1 = compile_typed_expr stk' amount in
  let stk', c2 = compile_typed_expr stk' contract_arg in

  let n_stack_saving = string_of_int (Stk_S.add stack_storage_type) in

  (Stk.of_type "contract-call" t_result)::stk,
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
    | "bool",   [],   0, 2 -> (Stk.of_type "False" it) :: stk, "PUSH bool False"
    | "bool",   [],   1, 2 -> (Stk.of_type "True" it)  :: stk, "PUSH bool True"
    | "option", [t'], 0, 2 -> (Stk.of_type "None" it)  :: stk, "NONE "^compile_etype t'
    | "list",   [t'], 0, 2 -> (Stk.of_type "Nil" it)   :: stk, "NIL "^compile_etype t'
    | "option", [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (Stk.of_type "Some" it)::List.tl stk, code^"SOME"
    | "list",   [t'], 1, 2 ->
      let stk, code = compile_typed_expr stk content in (Stk.of_type "Cons" it)::List.tl stk, code^"DUP; CDR; SWAP; CAR; CONS"
    | _ ->
      let types = List.map compile_etype types in
      let stk, code = compile_typed_expr stk content in
      (Stk.of_type (sprintf "sum<%d|%d>" i n) it) ::List.tl stk, code^MoC.sum_make i types
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
  let store_level = match Stk.get_level stk "@" with Some n -> n-1 | None -> assert false in
  (* Number of fields in user store *)
  let n = 
    match Stk.type_of_var stk "@" with
      | Some(I.TProduct(_, lazy fields)) -> List.length fields 
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
    (Stk.of_type "if" it)::stk, sprintf "%sIF { %s}\n{ %s}" code if_true if_false (* TODO make sure unit-bound variables in cases aren't used *)
  | "list", [(_, _, if_nil); (v, t_v, if_cons)] ->
    let _, if_cons_code = compile_typed_expr ((Stk.of_type "CONS" it)::stk) if_cons in
    let _, if_nil_code = compile_typed_expr stk if_nil in
    (Stk.of_type "if_cons" it) :: stk, 
    sprintf "%sIF_CONS { PAIR; # %s\n %s%s}\n{ %s}"
    code v if_cons_code if_nil_code (remove_unless_fail if_cons "cons")
  | "option", [(_, _, if_none); (v, t_v, if_some)] ->
    let _, if_some_code = compile_typed_expr ((Stk.of_var v t_v)::stk) if_some in
    let _, if_none_code = compile_typed_expr stk if_none in
    (Stk.of_type "if_none" it)::stk, 
    sprintf "%sIF_NONE { %s}\n{ # %s\n%s%s}" code if_none_code v if_some_code
    (remove_unless_fail if_some v)
  | _ -> (* User-defined sum type *)
    let f i (v, t_v, ie)  =
      let code = snd (compile_typed_expr ((Stk.of_var v t_v)::stk) ie) in
      sprintf "# | <%d>(%s):\n%s%s" i v code (remove_unless_fail ie v) in
    (Stk.of_type (sprintf "sum<%d>" (List.length cases)) it)::stk, code ^ MoC.sum_case (List.mapi f cases)

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
  | I.ELambda(v_prm, t_prm, env, res), t_lambda ->
    Stk_S.reset();

    let stk = [(Stk.of_var v_prm t_prm); (Stk.of_var "@" i_contract.I.storage_type)] in
    let stk, code = compile_typed_expr stk res in

    (* TODO simplify storage if there is no contract-call *)
    let t_compiler_store, saved_stacks = Stk_S.get_all() in
    let need_stack_store = List.length saved_stacks > 1 in
    let t_stores = 
      if not need_stack_store then i_contract.I.storage_type
      else I.TProduct(None, lazy [t_compiler_store; i_contract.I.storage_type]) in

    (* Piece everything together *)
    let code =
      sprintf "parameter %s;\n" (compile_etype t_prm) ^
      sprintf "storage %s;\n" (compile_etype t_stores) ^
      sprintf "return %s;\n" (compile_etype (snd res)) ^
      sprintf "code { DUP; CDR; SWAP; CAR; # split %s/store\n" v_prm ^
      (if need_stack_store then "DIP { CDR }; # remove stack store\n" else "")^
      sprintf "%s" code ^
      sprintf "DIP { DROP }; # remove %s\n" v_prm ^
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

