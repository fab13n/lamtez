(* Compile a type lamtez term into an intermediate representation where:
 * * Nodes are fully type-annotated;
 * * Labelled products and sums are replaced by indexed versions;
 * * Lambdas and applications are replaced by multi-arg versions,
 *   eta-expanding partially applied functions (TODO);
 * * TApp types are sorted between sums, products and primitives;
 *
 * sum and product type contents are lazy, because some inductive types
 * such as `list` have infinite expanded types.
 *)

open Utils
open Printf

module A = Ast
module I = Intermediate
module P = String_of_ast
module Ctx = Typecheck_ctx

let prim_translations = [
  "time", "timestamp"; "sig", "signature";
]

let rec compile_etype ctx t =
  let c = compile_etype ctx in
  match t with
  | A.TId id ->
    begin match Ctx.expand_type ctx t with (* TODO the re-expansion shouldn't be necessary here *)
    | A.TId id -> failwith ("unresolved type variable "^id)
    | t -> c t
    end
  | A.TLambda _ as t ->
    let rec get = function A.TLambda(a, b) -> let p, t = get b in a::p, t | t -> [], t in
    let params, result = get t in
    I.TLambda(List.map c params, c result)
  | A.TTuple(list) -> I.TProduct(None, lazy(List.map c list))
  | A.TApp(name, args) -> begin match Ctx.decl_of_name ctx name with
    | A.DProduct(name, params, fields) ->
      I.TProduct(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args fields)))
    | A.DSum(name, params, cases) ->
      I.TSum(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args cases)))
    | A.DPrim(name, params) ->
      let name = try List.assoc name prim_translations with Not_found -> name in
      I.TPrim(name, List.map c args)
    | A.DAlias _ -> unsound "Aliases should have been simplified by now"
  end
  | A.TFail -> I.TPrim("fail", [])

and compile_decl_pairs params args tagged_fields =
  List.map (fun (tag, t) -> A.replace_tvars params args t) tagged_fields

let binop_dic = [
  A.BEq, "EQ"; A.BNeq, "NEQ"; A.BLe, "LE"; A.BLt, "LT"; A.BGe, "GE"; A.BGt, "GT"; A.BConcat, "CONCAT";
  A.BOr, "OR"; A.BAnd, "AND"; A.BXor, "XOR";
  A.BAdd, "ADD"; A.BSub, "SUB"; A.BMul, "MUL"; A.BDiv, "EDIV"; A.BLsr, "LSR"; A.BLsl, "LSL"]

let unop_dic = [A.UNot, "NOT"; A.UNeg, "NEG"; A.UAbs, "ABS"]

let get_product_tags ctx (t:A.etype) =
  let name = match t with A.TApp(name, _)  -> name | _ -> unsound "bad product type" in
  let tags = match Ctx.decl_of_name ctx name with
    | A.DProduct(_, type_params, fields) -> List.map fst fields
    | d -> unsound ("Not a product type: "^P.string_of_type t^" = "^P.string_of_type_decl d) in
  tags

let get_sum_decl_cases ctx (t:A.etype) =
  match t with
  | A.TApp(name, type_args)  ->
    begin match Ctx.decl_of_name ctx name with
    | A.DSum(_, type_params, cases) ->
      List.map (fun (tag, t) -> tag, A.replace_tvars type_params type_args t) cases
    | d -> unsound ("Not a sum type: "^P.string_of_type t^" = "^P.string_of_type_decl d)
    end
  | t -> unsound ("Not a sum type: "^P.string_of_type t)

let rec compile_expr ctx e =
  let c = compile_expr ctx in
  let e_type = Typecheck.retrieve_type ctx e in
  (* print_endline("exprT->iExpr: "^P.string_of_expr e^"; typeT: "^P.string_of_type e_type);  *)
  let it = compile_etype ctx e_type in

  match e with

  | A.ENat n | A.EInt n ->
    let s = string_of_int n in
    let s = if n>=0 then s else "("^s^")" in
    I.ELit(s), it

  | A.EString(s) -> I.ELit(sprintf "\"%s\"" s), it
  | A.ETez(n)    -> I.ELit(sprintf "\"%d.%02d\"" (n/100) (n mod 100)), it
  | A.ETime(s)   -> I.ELit(sprintf "\"%s\"" s), it
  | A.ESig(s)    -> I.ELit(sprintf "\"%s\"" s), it
  | A.EId(id)    -> I.EId id, it

  | A.ELambda _ as e ->
    let rec get = function A.ELambda(a, _, b) -> let p, t = get b in a::p, t | t -> [], t in
    let param_names, body = get e in
    let param_types = match it with I.TLambda(p, _) -> p | _ -> unsound "bad lambda type" in
    let typed_names = List.map2 (fun n t -> n, t) param_names param_types in
    I.ELambda(typed_names, c body), it

  | A.ELetIn(id, t, e0, e1) ->
    let te0 = c e0 and (ie1, it1) as te1 = c e1 in
    I.ELetIn(id, te0, te1), it1

  | A.EApp _ as e ->
    let rec get = function A.EApp(f, a) -> let f', args = get f in f', a::args | e -> e, [] in
    let f, args = get e in
    I.EApp(c f, List.map c args), it

  | A.ETuple(list) -> I.EProduct(List.map c list), it

  | A.ETupleGet(e_tuple, i) ->
    let t_tuple = Typecheck.retrieve_type ctx e_tuple in
    begin match t_tuple with
    | A.TTuple(list) -> I.EProductGet(c e_tuple, i, List.length list), it
    | t -> unsound("Not a tuple type "^P.string_of_type t)
    end
  | A.EProduct(fields) ->
    let tags = get_product_tags ctx e_type in
    I.EProduct (List.map (fun tag -> c (List.assoc tag fields)) tags), it

  | A.EProductGet(e_product, tag) ->
    let t_product = Typecheck.retrieve_type ctx e_product in
    let tags = get_product_tags ctx t_product in
    let tag2num = List.mapi (fun i t -> t, i) tags in
    I.EProductGet(c e_product, List.assoc tag tag2num, List.length tags), it

  | A.EProductSet(e_product, tag, e_field) -> not_impl "product update"

  | A.EStoreSet(v, e0, e1) -> not_impl "store set"

  | A.ESum(tag, e) ->
    let tags = get_sum_decl_cases ctx e_type in
    let tag2num = List.mapi (fun i (tag, _) -> tag, i) tags in
    I.ESum(List.assoc tag tag2num, List.length tags, c e), it

  | A.ESumCase(e_test, e_cases) ->
    (* TODO d_cases are generic. *)
    let t_test = Typecheck.retrieve_type ctx e_test in
    let d_cases = get_sum_decl_cases ctx t_test in
    let rec f e_cases (d_tag, d_type) =
      let e_var, e_expr = List.assoc d_tag e_cases in
      e_var, compile_etype ctx d_type, c e_expr
    in
    I.ESumCase(c e_test, List.map (f e_cases) d_cases), it

  | A.EBinOp(e0, op, e1) ->
    let (_, it0) as iet0 = c e0 and (_, it1) as iet1= c e1 in
    let lt = I.TLambda([it0; it1], it) in
    (* TODO: I.EId??? *)
    I.EApp((I.EId(List.assoc op binop_dic), lt), [iet0;  iet1]), it

  | A.EUnOp(op, e) ->
    let (_, it') as iet' = c e in
    let lt = I.TLambda([it'], it) in
    I.EApp((I.EId(List.assoc op unop_dic), lt), [iet']), it

  | A.ETypeAnnot (e, t) -> c e

let compile_contract ctx (type_declarations, store_fields, expr) =
    (* Declarations are already passed in ctx thanks to typechecking;
     * store_fields are not. *)
    let n_contract_calls =
      let rec forbidden list where =
        if List.exists (fun e -> count e > 0) list
        then unsupported ("Contracts forbidden in "^where) else 0
      and count = function
      | A.ENat _ | A.EInt _ | A.EString _ | A.ETez _ | A.ETime _ | A.ESig _ | A.EId _ -> 0
      | A.ELambda(_, _, e) -> forbidden [e] "functions"
      | A.EApp(e0, e1) -> forbidden [e0; e1] "function applications"
      | A.EBinOp(e0, _, e1) -> forbidden [e0; e1] "binary operators"
      | A.EProductSet(e0, _, e1) -> forbidden [e0; e1] "product updates"
      | A.EStoreSet(_, e0, e1) -> forbidden [e0; e1] "stored field updates"
      | A.ETuple(list) -> forbidden list "tuples"
      | A.ETupleGet(e, _) -> count e
      | A.EProduct(list) -> forbidden (List.map snd list) "product types"
      | A.EProductGet(e, _) | A.ESum(_, e) | A.EUnOp(_, e) | A.ETypeAnnot(e, _) -> count e
      | A.ELetIn(_, _, e0, e1) -> count e0 + count e1
      | A.ESumCase(e, list) ->
        List.fold_left (fun n (_, (_, e)) -> n+count e) (count e) list
      in count expr in
    let store_type = Ctx.product_of_name ctx "@" in

    let stack_store_type = I.TSum(None, lazy []) in
    (* quel type donner au champ de sauvegarde ? Pour l'instant je ne le connais pas,
     * comme je ne l'utiliserai que pour les contract-call je peux le gerer spécialement (il doit juste etre imprimable)
     * -> je vais le laisser comme une primitive.
     *)
    ()