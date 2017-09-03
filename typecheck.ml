open Utils
module Ctx = Typecheck_ctx
module A = Ast
module P = String_of_ast

module StringSet = Set.Make(String)

type typed_contract = {
  ctx:          Ctx.t;
  storage_type: A.etype;
  param_type:   A.etype;
  result_type:  A.etype;
  storage_init: A.expr option;
  code:         A.expr }

let _DEBUG_ = true
let debug_indent = ref 0

let rec typecheck_expr ctx expr =
  if _DEBUG_ then begin
    (* print_endline ("\n"^String.make 80 '*'); *)
    print_endline (String.make (2 * !debug_indent) ' '^"Typing "^P.string_of_expr expr);
    (* print_endline ("In context: "^Ctx.string_of_t ctx); *)
    incr debug_indent
  end;

  let ctx, t = match expr with
  | A.ELit(_, c) -> begin match c with
    | A.LNat _    -> ctx, A.tprim "nat"
    | A.LInt _    -> ctx, A.tprim "int"
    | A.LString _ -> ctx, A.tprim "string"
    | A.LTez _    -> ctx, A.tprim "tez"
    | A.LSig _    -> ctx, A.tprim "sig"
    | A.LTime _   -> ctx, A.tprim "time"
    end
  | A.EColl(_, A.CList, list) -> typecheck_EColl_CList ctx list
  | A.EColl(_, A.CMap,  list) -> typecheck_EColl_CMap  ctx list
  | A.EColl(_, A.CSet,  list) -> typecheck_EColl_CSet  ctx list
  | A.EId(_, id) ->
    let scheme = Ctx.scheme_of_evar ctx id in
    ctx, Ctx.instantiate_scheme (scheme)
  | A.ELambda(_, id, scheme, e) -> typecheck_ELambda ctx id scheme e
  | A.ELet(_, id, t_id, e0, e1) -> typecheck_ELetIn ctx id t_id e0 e1
  | A.EApp(_, f, arg) -> typecheck_EApp ctx f arg
  | A.ETypeAnnot(_, e, t) -> let ctx, te = typecheck_expr ctx e in Ctx.unify ctx t te
  | A.ETuple(_, exprs) -> let ctx, types = list_fold_map typecheck_expr ctx exprs in ctx, A.TTuple(A.noloc, types)
  | A.ETupleGet(_, e, n) -> typecheck_ETupleGet ctx e n
  | A.EProduct(_, pairs) -> typecheck_EProduct ctx pairs
  | A.EProductGet(_, e, tag) -> typecheck_EProductGet ctx e tag
  | A.EProductSet(_, e0, tag, e1) -> typecheck_EProductSet ctx e0 tag e1
  | A.EStoreSet(_, v, e0, e1) -> typecheck_EStoreSet ctx v e0 e1
  | A.ESum(_, tag, e) -> typecheck_ESum ctx tag e
  | A.ESumCase(_, e, cases) -> typecheck_ESumCase ctx e cases
  | A.EBinOp(loc, a, op, b) -> typecheck_EBinOp ctx loc a op b
  | A.EUnOp(_, op, a) -> typecheck_EUnOp ctx op a
  in
  let t = Ctx.expand_type ctx t in
  let ctx = Ctx.save_type expr t ctx in
  if _DEBUG_ then begin
    decr debug_indent;
    print_endline (String.make (2 * !debug_indent) ' '^"Result: val "^P.string_of_expr expr^": "^P.string_of_type t);
  end;
  ctx, t

and typecheck_EColl_CList ctx elts =
  let ctx, types = list_fold_map typecheck_expr ctx elts in 
  ctx, A.TApp(A.noloc, "list", types)

and typecheck_EColl_CMap ctx elts =
  not_impl "EColl_CMap"

and typecheck_EColl_CSet ctx elts =
  let ctx, types = list_fold_map typecheck_expr ctx elts in 
  ctx, A.TApp(A.noloc, "set", types)

and typecheck_ELambda ctx id scheme e =
  if fst scheme <> [] then unsupported "parametric parameter types";
  (* TODO fail if id is bound by default ctx? *)
  (* Type e supposing that id has type t_arg. *)
  let ctx, prev = Ctx.push_evar id scheme ctx in
  let ctx, te = typecheck_expr ctx e in
  (* TODO let-generalization? *)
  let ctx = Ctx.pop_evar prev ctx in
  ctx , A.TLambda(A.noloc, snd scheme, te)

and typecheck_ELetIn ctx id t_id e0 e1 =
  (* TODO fail if id is bound by default ctx? *)
  let ctx, t0 = typecheck_expr ctx e0 in
  let ctx, t0 = Ctx.unify ctx t_id t0 in
  (* TODO: generalize t0? *)
  let ctx, prev = Ctx.push_evar id ([], t0) ctx in
  let ctx, t1 = typecheck_expr ctx e1 in
  let ctx = Ctx.pop_evar prev ctx in
  ctx, t1

and typecheck_EApp ctx f arg =
  let ctx, t_f = typecheck_expr ctx f in
  let ctx, t_arg = typecheck_expr ctx arg in
  let ctx, t_param, t_result = match t_f with
    | A.TLambda(_, t_param, t_result) -> ctx, t_param, t_result
    | A.TId(_, id) ->
        let t_param, t_result = A.fresh_tvar(), A.fresh_tvar() in
        let ctx, _ = Ctx.unify ctx t_f (A.TLambda(A.noloc, t_param, t_result)) in
        ctx, t_param, t_result
    | _ -> type_error (A.loc_of_expr f) "Applying a non-function" in
  let ctx, _ = Ctx.unify ctx t_param t_arg in
  ctx, t_result

and typecheck_ETupleGet ctx e n =
  let ctx, t_e = typecheck_expr ctx e in
  begin match t_e with
  | A.TTuple(_, types) ->
    begin try ctx, List.nth types n 
    with Failure _ -> type_error (A.loc_of_expr e) "Out of tuple index" end
  | _ -> type_error (A.loc_of_expr e) "Not a tuple"
  end

and typecheck_EProduct ctx e_pairs =
  let tag0 = fst (List.hd e_pairs) in
  let name = Ctx.name_of_product_tag ctx tag0 in
  let t_result, t_items = Ctx.instantiate_composite name (Ctx.product_of_name ctx name) in
  let ctx, t_pairs = list_fold_map
    (fun ctx (tag, e) ->
      let ctx, t = typecheck_expr ctx e in
      let ctx, t = Ctx.unify ctx t (List.assoc tag t_items) in
      ctx, (tag, t))
    ctx e_pairs in
  ctx, t_result

and typecheck_ESumCase ctx e e_cases =
  let tag0, _ = List.hd e_cases in
  let name = try Ctx.name_of_sum_tag ctx tag0 
    with Not_found -> type_error (A.loc_of_expr e) (tag0^" is not a sum tag") in
  let t_sum, case_types = Ctx.instantiate_composite name (Ctx.sum_of_name ctx name) in
  let ctx, t_e = typecheck_expr ctx e in
  let ctx, _ = Ctx.unify ctx t_sum t_e in
  (* TODO check that declaration and case domains are equal. *)
  let ctx, t_pairs = list_fold_map
    (fun ctx (tag, (v, e)) ->
      (* TODO fail if v is bound by default ctx? *)
      let ctx, prev = Ctx.push_evar v ([], List.assoc tag case_types) ctx in
      let ctx, t = typecheck_expr ctx e in
      let ctx = Ctx.pop_evar prev ctx in
      ctx, (tag, t))
    ctx e_cases in
  let ctx, t = List.fold_left
    (fun (ctx, t) (tag, t') -> Ctx.unify ctx t t')
    (ctx, snd(List.hd t_pairs)) (List.tl t_pairs) in
  ctx, t

and typecheck_EProductGet ctx e_product tag =
  let name = try Ctx.name_of_product_tag ctx tag 
    with Not_found -> type_error (A.loc_of_expr e_product) (tag^" is not a product tag") in
  let t_product0, field_types = Ctx.instantiate_composite name (Ctx.product_of_name ctx name) in
  let ctx, t_product1 = typecheck_expr ctx e_product in
  let ctx, _ = Ctx.unify ctx t_product0 t_product1 in
  let t = List.assoc tag field_types in
  ctx, t

and typecheck_EProductSet ctx e_product tag e_field =
  let name = try Ctx.name_of_product_tag ctx tag 
    with Not_found -> type_error (A.loc_of_expr e_product) (tag^" is not a product tag") in
  let t_product0, field_types = Ctx.instantiate_composite name (Ctx.product_of_name ctx name) in
  let ctx, t_product1 = typecheck_expr ctx e_product in
  let ctx, t_product2 = Ctx.unify ctx t_product0 t_product1 in
  let t_field0 = List.assoc tag field_types in
  let ctx, t_field1 = typecheck_expr ctx e_field in
  let ctx, _ = Ctx.unify ctx t_field0 t_field1 in
  ctx, t_product2

and typecheck_EStoreSet ctx v e_field e =
  let _, field_types = Ctx.instantiate_composite "@" (Ctx.product_of_name ctx "@") in
  let t_field0 = List.assoc v field_types in
  let ctx, t_field1 = typecheck_expr ctx e_field in
  let ctx, _ = Ctx.unify ctx t_field0 t_field1 in
  typecheck_expr ctx e

and typecheck_ESum ctx tag e =
  let name = try Ctx.name_of_sum_tag ctx tag
    with Not_found -> type_error (A.loc_of_expr e) (tag^" is not a sum tag") in
  let t_sum, case_types = Ctx.instantiate_composite name (Ctx.sum_of_name ctx name) in
  let ctx, t_e = typecheck_expr ctx e in
  let ctx, _ = Ctx.unify ctx t_e (List.assoc tag case_types) in
  ctx, t_sum

and typecheck_EBinOp ctx loc a op b =
  let prims_in candidates responses = List.for_all (fun t-> List.mem t responses) candidates in
  let p n = A.TApp(A.noloc, n, []) in
  let ctx, ta = typecheck_expr ctx a in
  let ctx, tb = typecheck_expr ctx b in
  let error op = type_error loc ("Cannot "^op^" "^P.string_of_type ta^" and "^P.string_of_type tb) in
  match op with
  | A.BConcat ->
    let ctx, _ = Ctx.unify ctx ta (p "string") in
    let ctx, _ = Ctx.unify ctx tb (p "string") in
    ctx, A.TApp(A.noloc, "string", [])

  | A.BAdd ->
    (* nat² -> nat | (nat|int)² -> int | nat time -> time | tez² -> tez *)
    begin match ta, tb with
    | A.TApp(_, "nat", []), A.TApp(_, "nat", []) -> ctx, p "nat"
    | A.TApp(_, t0, []), A.TApp(_, t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    (* TODO shouldn't this be time int->time instead? *)
    | A.TApp(_, "nat", []), A.TApp(_, "time", []) | A.TApp(_, "time", []), A.TApp(_, "nat", []) -> ctx, p "time"
    | A.TApp(_, "tez", []), A.TApp(_, "tez", []) -> ctx, p "tez"
    | A.TId(_, id), A.TApp(_, "nat", []) | A.TApp(_, "nat", []), A.TId(_, id) ->
      type_error loc ("Need more type annotation to determine wether  addition is "^
                      "(nat, int) -> int, (nat, nat) -> nat or (nat, time) -> time.")
      (* let ctx, _ = Ctx.unify ctx (A.TId(_, id)) (p "int") in ctx, p "int" *)
    | A.TId(_, id), A.TApp(_, "int", []) | A.TApp(_, "int", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "int") in ctx, p "int"
    | A.TId(_, id), A.TApp(_, "tez", []) | A.TApp(_, "tez", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "tez") in ctx, p "tez"
    | A.TId(_, id), A.TApp(_, "time", []) | A.TApp(_, "time", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "nat") in ctx, p "nat"
    | A.TId(_, id0), A.TId(_, id1) ->
      type_error loc ("Need more type annotation to determine addition type.")
    | _ -> error "add"
    end

  | A.BSub ->
    (* (int|nat)² -> int | tez² -> tez *)
    begin match ta, tb with
    | A.TApp(_, t0, []), A.TApp(_, t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    | A.TApp(_, "tez", []), A.TApp(_, "tez", []) -> ctx, p "tez"
    | A.TId(_, id), A.TApp(_, t, []) | A.TApp(_, t, []), A.TId(_, id) when prims_in [t] ["nat"; "int"] ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "int") in ctx, p "int"
    | A.TId(_, id), A.TApp(_, "tez", []) | A.TApp(_, "tez", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "tez") in ctx, p "tez"
    | A.TId(_, id0), A.TId(_, id1) ->
      type_error loc ("Need more annotations to determine substraction type.")
      (* let ctx, _ = Ctx.unify ctx ta (p "int") in
         let ctx, _ = Ctx.unify ctx tb (p "int") in
         ctx, p "int" *)
    | _ -> error "substract"
    end

  | A.BMul ->
    (* nat² -> nat | (int|nat)² -> int | tez nat -> tez*)
    begin match ta, tb with
    | A.TApp(_, "nat", []), A.TApp(_, "nat", []) -> ctx, p "nat"
    | A.TApp(_, t0, []), A.TApp(_, t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, p "int"
    | A.TApp(_, "tez", []), A.TApp(_, "nat", []) | A.TApp(_, "nat", []), A.TApp(_, "tez", []) -> ctx, p "tez"
    | A.TId(_, id), A.TApp(_, "nat", []) | A.TApp(_, "nat", []), A.TId(_, id)  ->
      type_error loc ("Need more type annotation to determine wether  multiplication is "^
                      "(nat, int) -> int, (nat, nat) -> nat or (nat, tez) -> tez.")
      (* let ctx, _ = Ctx.unify ctx (A.TId(_, id)) (p "int") in ctx, p "int" *)
    | A.TId(_, id), A.TApp(_, "int", []) | A.TApp(_, "int", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "int") in ctx, p "int"
    | A.TId(_, id), A.TApp(_, "tez", []) | A.TApp(_, "tez", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "nat") in ctx, p "tez"
    | A.TId(_, id0), A.TId(_, id1) ->
      type_error loc ("Need more annotations to determine multiplication type.")
      (* let ctx, _ = Ctx.unify ctx ta (p "int") in
      let ctx, _ = Ctx.unify ctx tb (p "int") in
      ctx, p "int"  *)
    | _ -> error "multiply"
    end

  | A.BDiv ->
    (* nat² -> option (nat*nat) | (nat|int)² -> option(int*nat)
     | tez nat -> option(tez*tez) | tez tez -> option(nat*tez) *)
    let op x y = A.TApp(A.noloc, "option", [A.TTuple(A.noloc, [A.TApp(A.noloc, x, []); A.TApp(A.noloc, y, [])])]) in
    begin match ta, tb with
    | A.TApp(_, "nat", []), A.TApp(_, "nat", []) -> ctx, op "nat" "nat"
    | A.TApp(_, t0, []), A.TApp(_, t1, []) when prims_in [t0; t1] ["int"; "nat"] -> ctx, op "int" "nat"
    | A.TApp(_, "tez", []), A.TApp(_, "nat", []) -> ctx, op "tez" "tez"
    | A.TApp(_, "tez", []), A.TApp(_, "tez", []) -> ctx, op "nat" "tez"
    | A.TId(_, id), A.TApp(_, t, []) | A.TApp(_, t, []), (A.TId(_, id)) when prims_in [t] ["int"; "nat"] ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "int") in ctx, op "int" "nat"
    | A.TId(_, id), A.TApp(_, "tez", []) ->
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "tez") in ctx, op "nat" "tez"
    | A.TApp(_, "tez", []), A.TId(_, id) -> (* `t1` Could be either tez or nat; let's arbitrarily pick nat *)
      let ctx, _ = Ctx.unify ctx (A.TId(A.noloc, id)) (p "nat") in ctx, op "tez" "tez"
    | A.TId(_, id0), A.TId(_, id1) ->
      let ctx, _ = Ctx.unify ctx ta (p "int") in
      let ctx, _ = Ctx.unify ctx tb (p "int") in
      ctx, p "int"
    | _ -> error "divide"
    end

  | A.BEq | A.BNeq | A.BLt | A.BLe | A.BGt | A.BGe ->
    (* a² -> bool *)
    let ctx, _ = Ctx.unify ctx ta tb in ctx, p "bool"

  | A.BOr | A.BAnd | A.BXor ->
    (* bool² -> bool | nat² -> nat *)
    begin match ta, tb with
    | A.TApp(_, "bool", []), A.TApp(_, "bool", []) -> ctx, p "bool"
    | A.TApp(_, "nat", []), A.TApp(_, "nat", []) -> ctx, p "nat"
    | A.TId(_, id), A.TApp(_, t, []) | A.TApp(_, t, []), A.TId(_, id) when prims_in [t] ["nat"; "bool"] ->
      let ctx, _ = Ctx.unify ctx ta tb in ctx, p t
    | A.TId(_, id0), A.TId(_, id1) -> (* have to choose arbitrarily between bool and nat *)
      let ctx, _ = Ctx.unify ctx ta (p "bool") in
      let ctx, _ = Ctx.unify ctx tb (p "bool") in
      ctx, p "bool"
    | _ -> error "apply logical operator"
    end

  | A.BLsl | A.BLsr ->
    (* nat² -> nat *)
    begin match ta, tb with
    | A.TApp(_, "nat", []), A.TApp(_, "nat", []) -> ctx, p "nat"
    | A.TId(_, id), A.TApp(_, "nat", []) | A.TApp(_, "nat", []), A.TId(_, id) ->
      let ctx, _ = Ctx.unify ctx ta tb in ctx, p "nat"
    | A.TId(_, id0), A.TId(_, id1) -> (* have to choose arbitrarily between bool and nat *)
      let ctx, _ = Ctx.unify ctx ta (p "nat") in
      let ctx, _ = Ctx.unify ctx tb (p "nat") in
      ctx, p "nat"
    | _ -> error "bit-shift"
    end

and typecheck_EUnOp ctx op a =
  let p n = A.TApp(A.noloc, n, []) in
  let ctx, ta = typecheck_expr ctx a in
  match op with

  | A.UAbs ->
    (* int -> nat *)
    begin match ta with
    | A.TApp(_, "int", []) -> ctx, p "nat"
    | A.TApp(_, "nat", []) -> type_error (A.loc_of_expr a) "no point in getting the absolute val of a nat"
    | A.TId(_, id) -> let ctx, _ = Ctx.unify ctx ta (p "int") in ctx, p "nat"
    | _ -> type_error (A.loc_of_expr a) "Cannot get abs of that"
    end

  | A.UNot ->
    (* bool -> bool | (nat|int) -> int *)
    begin match ta with
    | A.TApp(_, "int", []) | A.TApp(_, "nat", []) -> ctx, p "int"
    | A.TApp(_, "bool", []) -> ctx, p "bool"
    | A.TId(_, id) -> let ctx, _ = Ctx.unify ctx ta (p "bool") in ctx, p "bool"
    | _ -> type_error (A.loc_of_expr a) "Cannot get opposite of that"
    end

  | A.UNeg ->
    (* (nat|int) -> int *)
    begin match ta with
    | A.TApp(_, "int", []) | A.TApp(_, "nat", []) -> ctx, p "int"
    | A.TId(_, id) -> let ctx, _ = Ctx.unify ctx ta (p "int") in ctx, p "int"
    | _ -> type_error (A.loc_of_expr a) "Cannot get the negation of that"
    end

let typecheck_decl ctx = function
  | A.DPrim(_, var, params) -> Ctx.add_prim var params ctx
  | A.DAlias(_, var, params, t) -> Ctx.add_alias var (params, t) ctx
  | A.DProduct(_, var, params, cases) -> Ctx.add_product var params cases ctx
  | A.DSum(_, var, params, cases) -> Ctx.add_sum var params cases ctx

let typecheck_store (tag, etype, init) (ctx, fields, inits) =
  if List.mem_assoc tag fields then unsound("Storage field "^tag^" redefined");
  let ctx, inits = match inits, init with
  | None, _ | _, None -> ctx, None
  | Some inits, Some init ->
    let ctx, t_init = typecheck_expr ctx init in
    let ctx, _ = Ctx.unify ctx etype t_init in
    ctx, Some ((tag, init)::inits)
  in
  (ctx, (tag, etype)::fields, inits)

let check_contract_calls expr = 
  let rec forbidden list where =
    if List.exists f list
    then unsupported ("Contract calls forbidden in "^where)
    else false
  and f = function
  | A.ELit _ | A.EId _ -> false
  | A.EProductGet(_, e, _) | A.ESum(_, _, e) | A.EUnOp(_, _, e) | A.ETypeAnnot(_, e, _)       -> f e
  | A.ESumCase(_, e, list) -> List.exists (fun (v, (_, e)) -> v<>"call-contract" && f e) list
  | A.EColl(_, _, list)                   -> forbidden list "collections"
  | A.ELambda(_, "call-contract", _, _)   -> false
  | A.ELambda(_, _, _, e)                 -> forbidden [e] "functions"
  | A.EApp(_, e0, e1)                     -> forbidden [e0; e1] "function applications"
  | A.EBinOp(_, e0, _, e1)                -> forbidden [e0; e1] "binary operators"
  | A.EProductSet(_, e0, _, e1)           -> forbidden [e0; e1] "product updates"
  | A.EStoreSet(_, _, e0, e1)             -> forbidden [e0; e1] "stored field updates"
  | A.ETuple(_, list)                     -> forbidden list "tuples"
  | A.EProduct(_, list)                   -> forbidden (List.map snd list) "product types"
  | A.ETupleGet(_, e, _)                  -> f e
  | A.ELet(_, "call-contract", _, _, _) -> false
  | A.ELet(_, _, _, e0, e1)             -> f e0 || f e1
  in let _ = f expr in
  ()

let check_store_set expr =
  let rec forbidden list where =
    if List.exists f list
    then unsupported ("Storage updates forbidden in "^where)
    else false
  and f = function
  | A.ELit _ | A.EId _ -> false
  | A.EProductGet(_, e, _) | A.ESum(_, _, e) | A.EUnOp(_, _, e) | A.ETypeAnnot(_, e, _) -> f e
  | A.ESumCase(_, e, list) -> List.exists (fun (v, (_, e)) -> f e) list
  | A.EColl(_, _, list)                   -> forbidden list "collections"
  | A.ELambda(_, _, _, e)                 -> forbidden [e] "functions"
  | A.EApp(_, e0, e1)                     -> forbidden [e0; e1] "function applications"
  | A.EBinOp(_, e0, _, e1)                -> forbidden [e0; e1] "binary operators"
  | A.EProductSet(_, e0, _, e1)           -> forbidden [e0; e1] "product updates"
  | A.EStoreSet(_, _, e0, e1)             -> forbidden [e0; e1] " surrounding updates"
  | A.ETuple(_, list)                     -> forbidden list "tuples"
  | A.ETupleGet(_, e, _)                  -> f e
  | A.EProduct(_, list)                   -> forbidden (List.map snd list) "product types"
  | A.ELet(_, "call-contract", _, _, _) -> false
  | A.ELet(_, _, _, e0, e1)             -> f e0 || f e1
  in let _ = f expr in
  ()
  
let typecheck_contract ctx (type_declarations, storage_fields, code) =
  (* TODO is the arity of A.TApp() type properly checked? *)

  (* Incorporate type declarations in the context. *)
  let ctx = List.fold_left typecheck_decl ctx type_declarations in

  (* Turn store declarations into a sum declaration and product. *)
  let ctx, store_fields, init_fields = List.fold_right typecheck_store storage_fields (ctx, [], Some []) in
  let ctx = match store_fields with
  | [] -> let ctx = Ctx.add_alias "@" ([], A.tunit) ctx in
          Ctx.add_evar "@" ([], A.tunit) ctx
  | _ -> let ctx = Ctx.add_product "@" [] store_fields ctx in
         Ctx.add_evar "@" ([], A.tprim "@") ctx in
    
  let ctx, storage_init = match init_fields with None -> ctx, None | Some fields -> 
    (* The expression must be typechecked, in order to be registered for Ctx.retrive_type. *)
    let e = if fields=[] then A.eunit else A.EProduct(A.noloc, fields) in
    let ctx, _ = typecheck_expr ctx e in
    ctx, Some e
  in

  (* Compile the code itself *)
  let ctx, t = typecheck_expr ctx code in
  let t_param = A.fresh_tvar ~prefix:"param" () in
  let t_result = A.fresh_tvar ~prefix:"result" () in
  let ctx, t_code =  Ctx.unify ctx t (A.tlambda [t_param; t_result]) in
  let t_store = Ctx.expand_type ctx (A.tid "@") in
  let ctx = Ctx.add_evar "@" ([], A.TApp(A.noloc, "@", [])) ctx in

  begin match code with
    | A.ELambda(_, _, _, body) -> check_contract_calls body; check_store_set body;
    | _ -> unsupported "Contract code must be a litteral lambda"
  end;

  (* Check for unresolved polymorphism. *)
  (* TODO reassociate TId with their EId. reverse lookup in ctx? *)
  let f_code = A.get_free_tvars t_code in
  if f_code <> [] then type_error 
      (A.loc_of_expr code) 
      ("Unresolved types "^String.concat ", " f_code^
       " in code type: "^P.string_of_type t_code^"; add type annotations.");
  let f_store = A.get_free_tvars t_store in
  if f_store <> [] then type_error 
      (A.loc_of_expr code) 
      ("Unresolved types "^String.concat ", " f_store^
       " in storage type: "^P.string_of_type t_code^"; add type annotations.");


  let t_param, t_result = match t_code with A.TLambda(_, a, b) -> a, b | _ -> assert false in

  (* TODO migrate contract-call and EStoreSet checks here. *)
  { ctx          = ctx; 
    storage_type = t_store; 
    param_type   = t_param; 
    result_type  = t_result; 
    storage_init = storage_init;
    code         = code }
