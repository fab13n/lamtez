open Utils
open Tree 
open TypingContext
  
module StringSet = Set.Make(String)

(* TODO: use Ephemerons to prevent memory leaks. *)
module E2T: sig
  val get: exprT -> typeT
  val set: exprT -> typeT -> unit
end = struct
  module HashedExpr = struct
    type t = exprT
    let equal = (==)
    let hash = Hashtbl.hash
  end
  module ExprHashtbl = Hashtbl.Make(HashedExpr)
  let tbl: typeT ExprHashtbl.t = ExprHashtbl.create (37)
  let get (e:exprT) = ExprHashtbl.find tbl e
  let set (e:exprT) t = ExprHashtbl.add tbl e t
end

let retrieve_type ctx e = 
  let t = E2T.get e in
  TypingContext.expand_type ctx t

  (* Combo of a fold_left with a map: the function f returns both
 * an accumulator and a transformed list element. *)
let list_fold_map f acc list = 
  let acc, rev_list = List.fold_left 
    (fun (acc, list') a -> let acc, b = f acc a in acc, b::list')
    (acc, []) list
  in
  acc, List.rev rev_list

(* Makes sure the two assoc lists have the same key set, perform a map2
 * on their elements, return the resulting assoc list. 
 * Quadratic is the length of b, but assoc lists are supposed to be short.
 * ('k -> 'a -> 'b -> 'c) -> ('k*'a) list -> ('k->'b) list -> ('k->'c) list.
 *)
let list_assoc_map2 f a b =
  if List.sort compare (List.map fst a) != List.sort compare (List.map fst b)
  then type_error "different tag sets for composite type";
  List.map (fun (k, va) -> k, f k va (List.assoc k b)) a

let _DEBUG_ = true
let debug_indent = ref 0

let rec typecheck_expr ctx expr =
  if _DEBUG_ then begin
    (* print_endline ("\n"^String.make 80 '*'); *)
    print_endline (String.make (2 * !debug_indent) ' '^"Typing "^TreePrint.string_of_expr expr); 
    (* print_endline ("In context: "^TypingContext.string_of_t ctx); *)
    incr debug_indent
  end;
  let ctx, t = match expr with
  | ENum n  -> ctx, tprim0 (if n >= 0 then "nat" else "int")
  | EString _ -> ctx, tprim0 "string"
  | ETez _  -> ctx, tprim0 "tez" 
  | ESig _  -> ctx, tprim0 "sig"
  | ETime _ -> ctx, tprim0 "time"
  | EId(id) -> ctx, instantiate_scheme (scheme_of_evar ctx id)

  | ELambda(id, (t_params, t_arg), e) ->
    if t_params != [] then unsupported "parametric parameter types";
    (* Type e supposing that id has type t_arg. *)
    let ctx = add_evar id (t_params, t_arg) ctx in
    let ctx, te = typecheck_expr ctx e in
    (* TODO generalize: all variables which appear (free) in t_arg and
     * not in the rest of the environment can be generalized. *)
    (*
     xhxm*)
    let ctx = forget_evar id ctx in
    ctx , TLambda(t_arg, te)

  | ELetIn(id, e0, e1) ->
    let ctx, t0 = typecheck_expr ctx e0 in
    (* TODO: generalize t0? *)
    let ctx = add_evar id ([], t0) ctx in
    let ctx, t1 = typecheck_expr ctx e1 in
    let ctx = forget_evar id ctx in
    ctx, t1

  | EApp(f, arg) ->
    let ctx, t_f = typecheck_expr ctx f in
    let ctx, t_arg = typecheck_expr ctx arg in
    let ctx, t_param, t_result = match t_f with
      | TLambda(t_param, t_result) -> ctx, t_param, t_result
      | TId("contract-call") ->
        (* TODO check that other variables aren't used after this. *)
        (* TODO check that storage argument type == contract storage type *)
        (* TODO check that we aren't in a lambda. *)
        not_impl "contract-call typing"
      | TId(id) ->
         let t_param, t_result = fresh_tvar(), fresh_tvar() in
         let ctx, _ = unify ctx t_f (TLambda(t_param, t_result)) in
         ctx, t_param, t_result
      | _ -> type_error "Applying a non-function" in
    let ctx, _ = unify ctx t_param t_arg in
    ctx, t_result

  | ETypeAnnot(e, t) ->
    let ctx, te = typecheck_expr ctx e in unify ctx t te
 
  | ETuple exprs ->
    (* Every element must typecheck_expr, the total type is their product. *)
    let ctx, types = list_fold_map typecheck_expr ctx exprs in
    ctx, TTuple(types)
 
  | ETupleGet(e, n) ->
    (* Can't use simply unification: we wouldn't know how many elements are in the tuple. *)
    let ctx, t_e = typecheck_expr ctx e in
    begin match t_e with
    | TTuple types ->
      (try ctx, List.nth types n with Failure _ -> type_error "Out of tuple index")
    | _ -> type_error "Not known to be a tuple"
    end
 
  | EProduct pairs -> typecheck_EProduct ctx pairs
  | EProductGet(e, tag) -> typecheck_EProductGet ctx e tag
  | ESum(tag, e) -> typecheck_ESum ctx tag e
  | ESumCase(e, cases) -> typecheck_ESumCase ctx e cases
  | EBinOp(a, op, b) -> typecheck_EBinOp ctx a op b
  | EUnOp(op, a) -> typecheck_EUnOp ctx op a
  in
  let t = expand_type ctx t in
  E2T.set expr t;
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: val "^TreePrint.string_of_expr expr^": "^TreePrint.string_of_type t);
  end;
  ctx, t

and typecheck_EProduct ctx e_pairs =
  let tag0 = fst (List.hd e_pairs) in
  let name = name_of_product_tag ctx tag0 in
  let t_result, t_items = instantiate_composite name (product_of_name ctx name) in
  let ctx, t_pairs = list_fold_map 
    (fun ctx (tag, e) -> 
      let ctx, t = typecheck_expr ctx e in 
      let ctx, t = unify ctx t (List.assoc tag t_items) in
      ctx, (tag, t))
    ctx e_pairs in
  ctx, t_result

and typecheck_ESumCase ctx e e_cases =
  let tag0, _ = List.hd e_cases in
  let name = try name_of_sum_tag ctx tag0 with Not_found -> type_error(tag0^" is not a sum tag") in
  let t_sum, case_types = instantiate_composite name (sum_of_name ctx name) in
  let ctx, t_e = typecheck_expr ctx e in
  let ctx, _ = unify ctx t_sum t_e in
  (* TODO check that declaration and case domains are equal. *)
  let ctx, t_pairs = list_fold_map 
    (fun ctx (tag, (v, e)) -> 
      let ctx = add_evar v ([], List.assoc tag case_types) ctx in
      let ctx, t = typecheck_expr ctx e in 
      let ctx = forget_evar v ctx in
      ctx, (tag, t))
    ctx e_cases in
  let ctx, t = List.fold_left 
    (fun (ctx, t) (tag, t') -> unify ctx t t') 
    (ctx, snd(List.hd t_pairs)) (List.tl t_pairs) in
  ctx, t

and typecheck_EProductGet ctx e tag =
  let name = try name_of_product_tag ctx tag with Not_found -> type_error(tag^" is not a product tag") in
  let t_prod, field_types = instantiate_composite name (product_of_name ctx name) in
  let ctx, t_e = typecheck_expr ctx e in
  let ctx, _ = unify ctx t_prod t_e in
  let t = List.assoc tag field_types in
  ctx, t

and typecheck_ESum ctx tag e =
  let name = try name_of_sum_tag ctx tag with Not_found -> type_error(tag^" is not a sum tag") in
  let t_sum, case_types = instantiate_composite name (sum_of_name ctx name) in
  let ctx, t_e = typecheck_expr ctx e in
  let ctx, _ = unify ctx t_e (List.assoc tag case_types) in
  ctx, t_sum

and typecheck_EBinOp ctx a op b =
  let prims_in candidates responses = List.for_all (fun t-> List.mem t responses) candidates in
  let p n = TApp(n, []) in
  let ctx, ta = typecheck_expr ctx a in
  let ctx, tb = typecheck_expr ctx b in
  let error op = type_error("Cannot "^op^" "^TreePrint.string_of_type ta^" and "^TreePrint.string_of_type tb) in
  match op with
  | BConcat -> 
    let ctx, _ = unify ctx ta (p "string") in
    let ctx, _ = unify ctx tb (p "string") in
    ctx, TApp("string", [])

  | BAdd ->
    (* nat² -> nat | (nat|int)² -> int | nat time -> time | tez² -> tez *)
    begin match ta, tb with
    | TApp("nat", []), TApp("nat", []) -> ctx, p "nat"
    | TApp(t0, []), TApp(t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    (* TODO shouldn't this be time int->time instead? *)      
    | TApp("nat", []), TApp("time", []) | TApp("time", []), TApp("nat", []) -> ctx, p "time"
    | TApp("tez", []), TApp("tez", []) -> ctx, p "tez"
    | TId id, TApp(t, []) | TApp(t, []), TId id when prims_in [t] ["nat"; "int"] ->
      let ctx, _ = unify ctx (TId id) (p "int") in ctx, p "int"
    | TId id, TApp("tez", []) | TApp("tez", []), TId id ->
      let ctx, _ = unify ctx (TId id) (p "tez") in ctx, p "tez"
    | TId id, TApp("time", []) | TApp("time", []), TId id ->
      let ctx, _ = unify ctx (TId id) (p "nat") in ctx, p "nat"
    | TId id0, TId id1 ->
      let ctx, _ = unify ctx ta (p "int") in
      let ctx, _ = unify ctx tb (p "int") in
      ctx, p "int"
    | _ -> error "add"
    end

  | BSub ->
    (* (int|nat)² -> int | tez² -> tez *)
    begin match ta, tb with
    | TApp(t0, []), TApp(t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    | TApp("tez", []), TApp("tez", []) -> ctx, p "tez"
    | TId id, TApp(t, []) | TApp(t, []), TId id when prims_in [t] ["nat"; "int"] ->
      let ctx, _ = unify ctx (TId id) (p "int") in ctx, p "int"
    | TId id, TApp("tez", []) | TApp("tez", []), TId id ->
      let ctx, _ = unify ctx (TId id) (p "tez") in ctx, p "tez"
    | TId id0, TId id1 ->
      let ctx, _ = unify ctx ta (p "int") in
      let ctx, _ = unify ctx tb (p "int") in
      ctx, p "int"
    | _ -> error "substract"
    end

  | BMul ->
    (* nat² -> nat | (int|nat)² -> int | tez nat -> tez*)
    begin match ta, tb with
    | TApp("nat", []), TApp("nat", []) -> ctx, p "nat"
    | TApp(t0, []), TApp(t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    | TApp("tez", []), TApp("nat", []) | TApp("nat", []), TApp("tez", []) -> ctx, p "tez"
    | TId id, TApp(t, []) | TApp(t, []), TId id when prims_in [t] ["nat"; "int"]  ->
      let ctx, _ = unify ctx (TId id) (p "int") in ctx, p "int"
    | TId id, TApp("tez", []) | TApp("tez", []), TId id ->
      let ctx, _ = unify ctx (TId id) (p "tez") in ctx, p "tez"
    | TId id0, TId id1 ->
      let ctx, _ = unify ctx ta (p "int") in
      let ctx, _ = unify ctx tb (p "int") in
      ctx, p "int"
    | _ -> error "multiply"
    end

  | BDiv ->
    (* nat² -> option (nat*nat) | (nat|int)² -> option(int*nat) 
     | tez nat -> option(tez*tez) | tez tez -> option(nat*tez) *)
    let op x y = TApp("option", [TTuple[TApp(x, []); TApp(y, [])]]) in
    begin match ta, tb with
    | TApp("nat", []), TApp("nat", []) -> ctx, op "nat" "nat"
    | TApp(t0, []), TApp(t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, op "int" "nat"
    | TApp("tez", []), TApp("nat", []) -> ctx, op "tez" "tez"
    | TApp("tez", []), TApp("tez", []) -> ctx, op "nat" "tez"
    | TId id, TApp(t, []) | TApp(t, []), (TId id) when prims_in [t] ["int"; "nat"] ->
      let ctx, _ = unify ctx (TId id) (p "int") in ctx, op "int" "nat"
    | TId id, TApp("tez", []) ->
      let ctx, _ = unify ctx (TId id) (p "tez") in ctx, op "nat" "tez"
    | TApp("tez", []), TId id -> (* `t1` Could be either tez or nat; let's arbitrarily pick nat *)
      let ctx, _ = unify ctx (TId id) (p "nat") in ctx, op "tez" "tez"
    | TId id0, TId id1 ->
      let ctx, _ = unify ctx ta (p "int") in
      let ctx, _ = unify ctx tb (p "int") in
      ctx, p "int"
    | _ -> error "divide"    
    end

  | BEq | BNeq | BLt | BLe | BGt | BGe ->
    (* a² -> bool *)
    let ctx, _ = unify ctx ta tb in ctx, p "bool"
  
  | BOr | BAnd | BXor ->
    (* bool² -> bool | nat² -> nat *)
    begin match ta, tb with
    | TApp("bool", []), TApp("bool", []) -> ctx, p "bool"
    | TApp("nat", []), TApp("nat", []) -> ctx, p "nat"
    | TId id, TApp(t, []) | TApp(t, []), TId id when prims_in [t] ["nat"; "bool"] ->
      let ctx, _ = unify ctx ta tb in ctx, p t 
    | TId id0, TId id1 -> (* have to choose arbitrarily between bool and nat *)
      let ctx, _ = unify ctx ta (p "bool") in
      let ctx, _ = unify ctx tb (p "bool") in
      ctx, p "bool"
    | _ -> error "apply logical operator"
    end

  | BLsl | BLsr ->
    (* nat² -> nat *)
    begin match ta, tb with
    | TApp("nat", []), TApp("nat", []) -> ctx, p "nat"
    | TId id, TApp("nat", []) | TApp("nat", []), TId id ->
      let ctx, _ = unify ctx ta tb in ctx, p "nat"
    | TId id0, TId id1 -> (* have to choose arbitrarily between bool and nat *)
      let ctx, _ = unify ctx ta (p "nat") in
      let ctx, _ = unify ctx tb (p "nat") in
      ctx, p "nat"
    | _ -> error "bit-shift"
    end

and typecheck_EUnOp ctx op a = 
  let p n = TApp(n, []) in
  let ctx, ta = typecheck_expr ctx a in
  match op with

  | UAbs ->
    (* int -> nat *)
    begin match ta with
    | TApp("int", []) -> ctx, p "nat"
    | TApp("nat", []) -> type_error "no point in getting the absolute val of a nat"
    | TId id -> let ctx, _ = unify ctx ta (p "int") in ctx, p "nat"
    | _ -> type_error "Cannot get abs of that"
    end

  | UNot ->
    (* bool -> bool | (nat|int) -> int *)
    begin match ta with
    | TApp("int", []) | TApp("nat", []) -> ctx, p "int"
    | TApp("bool", []) -> ctx, p "bool"
    | TId id -> let ctx, _ = unify ctx ta (p "bool") in ctx, p "bool"
    | _ -> type_error "Cannot get opposite of that"
    end

  | UNeg ->
    (* (nat|int) -> int *)
    begin match ta with
    | TApp("int", []) | TApp("nat", []) -> ctx, p "int"
    | TId id -> let ctx, _ = unify ctx ta (p "int") in ctx, p "int"
    | _ -> type_error "Cannot get the negation of that"
    end

let typecheck_decl ctx = function
  | DPrim(var, params) -> add_prim var params ctx
  | DAlias(var, params, t) -> add_alias var (params, t) ctx
  | DProduct(var, params, cases) -> add_product var params cases ctx
  | DSum(var, params, cases) -> add_sum var params cases ctx

  let typecheck_contract ctx (dd, e) =
  let ctx = List.fold_left typecheck_decl ctx dd in
  let ctx, t = typecheck_expr ctx e in
  let param = fresh_tvar ~prefix:"param" () in
  let storage = fresh_tvar ~prefix:"storage" () in
  let result = fresh_tvar ~prefix:"result" () in
  let t' = tlambda [param; storage; TTuple[result; storage]] in
  unify ctx t t'

(*

contract-call: il  va falloir verifier qu'il est appelé dans de bonnes conditions:

* en dehors de tout lambda;
* s'il est dans le e0 d'un let x=e0 in e1, typer e1 en oubliant toutes les variables au-dessus de x. 
* TODO: il faudrait quand meme supporter le droit a updater le storage avant appel.

Ca crée une dependance forte entre le lambda-terme representant le contrat, et les contract-call a l'interieur:
il faut retrouver le storage.

*)