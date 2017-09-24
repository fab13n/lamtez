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

let _DEBUG_ = ref false

let prim_translations = [
  "time", "timestamp"; "sig", "signature";
]

let rec compile_etype ctx t =
  let c = compile_etype ctx in
  let split_function_args t =
    let rec rev_split_args = function 
    | A.TLambda(_, arg, result)
    | A.TApp(_, "result", [_; arg; result]) ->
      let args, result = rev_split_args result in arg::args, result
    | t -> [], t in
    let rev_args, result = rev_split_args t in
    List.rev rev_args, result in

  match t with
  | A.TId(_, id) ->
    begin match Ctx.expand_type ctx t with (* TODO the re-expansion shouldn't be necessary here *)
    | A.TId(_, id) -> failwith ("unresolved type variable "^id)
    | t -> c t
    end
  | A.TLambda _ ->
    let args, result = split_function_args t in
    I.TLambda(List.map c args, c result)
  | A.TApp(_, "closure", _) as t ->
    let args, result = split_function_args t in
    I.TPrim("closure", c result :: List.map c args)
  | A.TTuple(_, list) -> I.TProduct(None, lazy(List.map c list))
  | A.TApp(_, name, args) -> begin match Ctx.decl_of_name ctx name with
    | A.DProduct(_, name, params, fields) ->
      I.TProduct(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args fields)))
    | A.DSum(_, name, params, cases) ->
      I.TSum(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args cases)))
    | A.DPrim(_, name, params) ->
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
  let name = match t with A.TApp(_, name, _)  -> name | _ -> unsound "bad product type" in
  let tags = match Ctx.decl_of_name ctx name with
    | A.DProduct(_, _, type_params, fields) -> List.map fst fields
    | d -> unsound ("Not a product type: "^P.string_of_type t^" = "^P.string_of_type_decl d) in
  tags

let get_sum_decl_cases ctx (t:A.etype) =
  match t with
  | A.TApp(_, name, type_args)  ->
    begin match Ctx.decl_of_name ctx name with
    | A.DSum(_, _, type_params, cases) ->
      List.map (fun (tag, t) -> tag, A.replace_tvars type_params type_args t) cases
    | d -> unsound ("Not a sum type: "^P.string_of_type t^" = "^P.string_of_type_decl d)
    end
  | t -> unsound ("Not a sum type: "^P.string_of_type t)

(* Compiles the bindings described by `pattern`.
 * The result is a function which transforms a term, using the variables bound
 * by `pattern`, into a variable name, and a term which depends only on that
 * term ()
 *)
let rec compile_pattern ctx (p: A.pattern) (t: I.etype): string * (I.typed_expr->I.typed_expr) =
  match p with
  | A.PId id -> id, (fun x->x)
  | A.PAny -> A.fresh_var ~prefix:"_" (), (fun x->x)
  | A.PTuple plist -> compile_product_pattern ctx plist t
  | A.PProduct tagged_patterns ->
    let prod_name = match t with
      | I.TProduct(Some(name, []), _) -> name 
      | _ -> unsound "Need a named product type" in
    let tags = match Ctx.decl_of_name ctx prod_name with
      | A.DProduct(_, _, _, fields) -> List.map fst fields
      | _ -> assert false in 
    let f tag = try List.assoc tag tagged_patterns with Not_found -> A.PAny in
    let plist = List.map f tags in
    compile_product_pattern ctx plist t

and compile_product_pattern ctx plist t =
  let n = List.length plist in
  let prefix = String.concat "-" (List.flatten @@ List.map A.pattern_binds_list plist) in 
  let id = A.fresh_var ~prefix () in
  let field_types = match t with I.TProduct(_, lazy tlist) -> tlist | _ -> unsound("pattern type") in
  let fold (i, f) = function A.PAny -> i+1, f | p' ->
      (* f applies the accumulated transformations of already folded fields;
       * f' applies the transformation binding field <i|n>;
       * f'' applies both transformations. *)
      let t' = List.nth field_types i in
      let id', f' = compile_pattern ctx p' t' in
      let f'' te = 
        let te_var = I.EId id, t in
        let te_field = I.EProductGet(te_var, i, n), t' in
        f (I.ELet(id', te_field, f' te), t) in
      (* print_endline @@ sprintf "Fold <%d|%d>: p=%s\n  id: %s, f: X->%s\n  id': %s, f': X->%s\n  f'': X->%s" 
        i n (String_of_ast.string_of_pattern p') 
        id (String_of_intermediate.string_of_untyped_expr @@ fst @@ f @@ (I.EId "X", I.TPrim("X", [])))
        id' (String_of_intermediate.string_of_untyped_expr @@ fst @@ f' @@ (I.EId "X", I.TPrim("X", [])))
        (String_of_intermediate.string_of_untyped_expr @@ fst @@ f'' @@ (I.EId "X", I.TPrim("X", [])));  *)
      i+1, f''
  in
  let _, f = List.fold_left fold (0, (fun x->x)) plist in
  id, f

let rec compile_expr ctx e =
  let c = compile_expr ctx in
  let e_type = Ctx.retrieve_type ctx e in
  (* print_endline("exprT->iExpr: "^P.string_of_expr e^"; typeT: "^P.string_of_type e_type);   *)
  let it = compile_etype ctx e_type in

  match e with
  | A.ELit(_, c) -> begin match c with
    | A.LNat(_, n) | A.LInt(_, n) ->
      let s = string_of_int n in
      let s = if n>=0 then s else "("^s^")" in
      I.ELit(s), it
    | A.LString(_, s) -> I.ELit(sprintf "\"%s\"" s), it
    | A.LTez(_, n)    -> I.ELit(sprintf "\"%d.%02d\"" (n/100) (n mod 100)), it
    | A.LTime(_, s) | A.LSig(_, s) | A.LKey(_, s) ->
      I.ELit(sprintf "\"%s\"" s), it
    end
  | A.EColl(_, k, list) -> I.EColl(k, List.map c list), it
  | A.EId(_, id) -> I.EId id, it

  | A.ELambda _ as e ->
    (* Get nested param vars and types *)
    let rec split_param_names = function
      | A.ELambda(_, A.PId var, _, e_body, t_body) ->
        let vars, body = split_param_names e_body in
        var :: vars, e_body
      | non_lambda_expr -> [], non_lambda_expr in
    let rev_param_names, body_expr = split_param_names e in
    let param_types = match it with
      | I.TLambda(p, _) | I.TPrim("closure", _ ::p) -> p | _ -> unsound "lambda" in
    let typed_names = List.map2 (fun n t -> n, t) (List.rev rev_param_names) param_types in
    I.ELambda(typed_names, c body_expr), it

  | A.ELet(_, p, ps, e0, e1) ->
    assert (fst ps = []);
    let te0 = c e0 and (ie1, it1) as te1 = c e1 in
    begin match p with
    | A.PId id -> I.ELet(id, te0, te1), it1
    | A.PAny ->  I.ELet(A.fresh_var ~prefix:"_" (), te0, te1), it1
    | A.PTuple _ | A.PProduct _ -> 
      let id, f = compile_pattern ctx p (compile_etype ctx @@ snd ps) in
      I.ELet(id, te0, f @@ te1), it
    end

  | A.ESequence(_, list) ->
    let fold acc x = I.ELet(Ast.fresh_var ~prefix:"_" (), c x, acc), (snd acc) in
    let rev_list = List.rev list in
    List.fold_left fold (c (List.hd rev_list)) (List.tl rev_list)

  | A.EApp _ as e ->
    let rec get = function A.EApp(_, f, a) -> let f', args = get f in f', a::args | e -> e, [] in
    let f, rev_args = get e in
    I.EApp(c f, List.rev_map c rev_args), it

  | A.ETuple(_, list) -> I.EProduct(List.map c list), it

  | A.ETupleGet(_, e_tuple, i) ->
    let t_tuple = Ctx.retrieve_type ctx e_tuple in
    begin match t_tuple with
    | A.TTuple(_, list) -> I.EProductGet(c e_tuple, i, List.length list), it
    | t -> unsound("Not a tuple type "^P.string_of_type t)
    end
  | A.EProduct(_, fields) ->
    let tags = get_product_tags ctx e_type in
    I.EProduct (List.map (fun tag -> c (List.assoc tag fields)) tags), it

  | A.EProductGet(_, e_product, tag) ->
    let t_product = Ctx.retrieve_type ctx e_product in
    let tags = get_product_tags ctx t_product in
    let tag2num = List.mapi (fun i t -> t, i) tags in
    I.EProductGet(c e_product, List.assoc tag tag2num, List.length tags), it

  | A.EProductSet(_, e_product, tag, e_field) ->
    let t_product = Ctx.retrieve_type ctx e_product in
    let tags = get_product_tags ctx t_product in
    let tag2num = List.mapi (fun i t -> t, i) tags in
    let i = List.assoc tag tag2num and n = List.length tag2num in
    I.EProductSet(c e_product, i, n, c e_field), it

  | A.EStoreSet(loc, tag, e_field, e_rest) ->
    let t_store = A.TApp(loc, "@", []) in
    let tags = get_product_tags ctx t_store in
    let tag2num = List.mapi (fun i t -> t, i) tags in
    I.EStoreSet(List.assoc tag tag2num, c e_field, c e_rest), it

  | A.ESum(_, tag, e) ->
    let tags = get_sum_decl_cases ctx e_type in
    let tag2num = List.mapi (fun i (tag, _) -> tag, i) tags in
    I.ESum(List.assoc tag tag2num, List.length tags, c e), it

  | A.ESumCase(_, e_test, e_cases) ->
    (* TODO d_cases are generic. *)
    let t_test = Ctx.retrieve_type ctx e_test in
    let d_cases = get_sum_decl_cases ctx t_test in
    let rec f e_cases (d_tag, d_type) =
      let e_pattern, e_expr = List.assoc d_tag e_cases in
      match e_pattern with
      | A.PId e_var -> e_var, compile_etype ctx d_type, c e_expr
      | A.PAny -> A.fresh_var(), compile_etype ctx d_type, c e_expr
      | _ -> not_impl "patterns in sum cases" 
    in
    I.ESumCase(c e_test, List.map (f e_cases) d_cases), it

  | A.EBinOp(_, e0, op, e1) ->
    let (_, it0) as iet0 = c e0 and (_, it1) as iet1= c e1 in
    let lt = I.TLambda([it0; it1], it) in
    (* TODO: I.EId??? *)
    I.EApp((I.EId(List.assoc op binop_dic), lt), [iet0;  iet1]), it

  | A.EUnOp(_, op, e) ->
    let (_, it') as iet' = c e in
    let lt = I.TLambda([it'], it) in
    I.EApp((I.EId(List.assoc op unop_dic), lt), [iet']), it

  | A.ETypeAnnot (_, e, t) -> c e

let compile_contract (c: Typecheck.typed_contract) : I.contract =
  let ctx = c.Typecheck.ctx in
  { I.code         = compile_expr  ctx c.Typecheck.code;
    I.storage_type = compile_etype ctx c.Typecheck.storage_type;
    I.storage_init = ( match c.Typecheck.storage_init with
                     | Some e -> Some (compile_expr ctx e)
                     | None   -> None
                     ) }
