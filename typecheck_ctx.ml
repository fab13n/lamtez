open Utils
module A = Ast
module P = String_of_ast

let _DEBUG_ = ref false

module StringMap = Map.Make(String)
module ExprMap = Map.Make(struct type t = A.expr let compare=compare end)

type composite = {type_params: A.tvar list; cases: (A.tag*A.etype) list}
type substitutions = (A.tvar * A.etype) list

type t = {
  sums: composite StringMap.t; (* type_params, (case, type)* *)
  products: composite StringMap.t;
  product_tags: string StringMap.t;
  sum_tags: string StringMap.t;
  aliases: A.scheme StringMap.t;
  primitives: A.tvar list StringMap.t;
  evars: A.scheme StringMap.t;
  types_assoc: A.etype ExprMap.t;
}

let empty = {
  sums = StringMap.empty;
  products = StringMap.empty;
  sum_tags = StringMap.empty;
  product_tags = StringMap.empty;
  aliases = StringMap.empty;
  evars = StringMap.empty;
  primitives = StringMap.empty;
  types_assoc = ExprMap.empty;
}

let string_of_t ctx =
  let sot = P.string_of_type in 
  let sos = P.string_of_scheme in
  let list_of_map m = StringMap.fold (fun name x acc -> (name, x)::acc) m [] in
  let string_of_comp sep (name, c) =
    "type "^name ^" "^ sep_list " " (fun x->x) c.type_params ^ " = " ^
    sep_list sep (fun (tag, t) -> tag^" "^sot t) c.cases
  in
  let string_of_alias (name, (p, t)) = "type "^sep_list " " (fun x->x) (name::p)^" = "^sot t in
  let string_of_evar (name, s) = "val "^name^": "^sos s in
  let is_not_dummy_alias = function name, ([], A.TApp(_, name', [])) -> false | _ -> true in
  sep_list "\n" (fun x->x) (List.flatten [
    List.map (string_of_comp " + ") (list_of_map ctx.sums);
    List.map (string_of_comp " * ") (list_of_map ctx.products) ;
    List.map string_of_alias (List.filter is_not_dummy_alias (list_of_map ctx.aliases));
    List.map string_of_evar (list_of_map ctx.evars);
    ["# sum tags: "^sep_list ", " (fun (a,b) -> a^"->"^b) (list_of_map ctx.sum_tags)];
    ["# product tags: "^sep_list ", " (fun (a,b) -> a^"->"^b) (list_of_map ctx.product_tags)];
  ])

let product_of_name, sum_of_name =
  let composite_of_name cmap name =
    let c = StringMap.find name cmap in
    c.type_params, c.cases
  in
  (fun ctx -> composite_of_name ctx.products),
  (fun ctx -> composite_of_name ctx.sums)

let name_of_sum_tag     ctx tag = StringMap.find tag ctx.sum_tags
let name_of_product_tag ctx tag = StringMap.find tag ctx.product_tags

let decl_of_name ctx name =
  try
    let c = StringMap.find name ctx.sums
    in A.DSum(A.noloc, name, c.type_params, c.cases)
  with Not_found -> try
    let c = StringMap.find name ctx.products
    in A.DProduct(A.noloc, name, c.type_params, c.cases)
  with Not_found -> try
    let params = StringMap.find name ctx.primitives
    in A.DPrim(A.noloc, name, params)
  with Not_found -> try
    let (params, t) = StringMap.find name ctx.aliases
    in A.DAlias(A.noloc, name, params, t)
  with Not_found ->
    raise Not_found

let check_fresh_name ctx name =
  if StringMap.mem name ctx.sums
  || StringMap.mem name ctx.products
  || StringMap.mem name ctx.aliases
  || StringMap.mem name ctx.primitives
  then type_error A.noloc ("duplicate type name "^name)

let check_fresh_tag map cases =
  List.iter (fun (tag, _) -> if StringMap.mem tag map then type_error A.noloc ("duplicate tag "^tag)) cases

let add_alias name scheme ctx =
  check_fresh_name ctx name;
  {ctx with aliases = StringMap.add name scheme ctx.aliases}

let add_composite names_map tags_map aliases_map name type_params cases ctx =
  check_fresh_name ctx name;
  check_fresh_tag ctx.sum_tags cases;
  check_fresh_tag ctx.product_tags cases;
  let aliases = if type_params<>[] then aliases_map else StringMap.add name ([], A.tapp name []) aliases_map in
  let names_map = StringMap.add name {type_params; cases} names_map in
  let tags_map = List.fold_left (fun tags_map (tag, _) -> StringMap.add tag name tags_map) tags_map cases in
  aliases, names_map, tags_map

let add_sum name type_params cases ctx =
  let aliases, sums, sum_tags =
    add_composite ctx.sums ctx.sum_tags ctx.aliases name type_params cases ctx in
  {ctx with aliases; sums; sum_tags}

let add_product name type_params cases ctx =
  let aliases, products, product_tags =
    add_composite ctx.products ctx.product_tags ctx.aliases name type_params cases ctx in
  {ctx with aliases; products; product_tags}

let add_prim name type_params ctx =
  check_fresh_name ctx name;
  let ctx = if type_params<>[] then ctx else
     add_alias name ([], A.TApp(A.noloc, name, [])) ctx in
  let p = StringMap.add name type_params ctx.primitives in
  {ctx with primitives = p}

let add_evar name t ctx =
  {ctx with evars=StringMap.add name t ctx.evars}

let forget_evar name ctx =
  {ctx with evars=StringMap.remove name ctx.evars}

type bookmark_item = A.evar * A.scheme option
type bookmark = bookmark_item list
let bookmark_empty = []

let push_evar name t ctx =
  let prev_content = try Some(StringMap.find name ctx.evars) with Not_found -> None in
  add_evar name t ctx, (name, prev_content)

let pop_evar (name, prev_t) ctx =
  match prev_t with
  | None -> forget_evar name ctx
  | Some t -> add_evar name t ctx

let push_evars list ctx =
  let fold (ctx, bookmark) (name, scheme) =
    let ctx, prev = push_evar name scheme ctx in
    ctx, prev :: bookmark
  in
  List.fold_left fold (ctx, []) list

let pop_evars bookmark ctx =
  List.fold_right pop_evar bookmark ctx

let instantiate_scheme (params, t) =
  let x = List.fold_left (fun t p -> A.replace_tvar p (A.fresh_tvar()) t) t params in
  (* print_endline ("Instanciate "^P.string_of_scheme (params, t)^" ::= "^P.string_of_type x); *)
  x

let instantiate_composite name (params, d_pairs) =
  let subst = List.map (fun v -> (v, A.fresh_tvar())) params in
  let r (tag, t) = tag, List.fold_left (fun t (v, v') -> A.replace_tvar v v' t) t subst in
  A.TApp(A.noloc, name, List.map snd subst), List.map r d_pairs

(* Replace tvars with their values as much as possible, deep into a typeT *)
let rec expand_type ctx t =
  let r = expand_type ctx in
  match t with
  | A.TFail -> t
  | A.TLambda(_, t0, t1) -> A.TLambda(A.noloc, r t0, r t1)
  | A.TApp(_, name, args) -> A.TApp(A.noloc, name, List.map r args)
  | A.TTuple(_, types) -> A.TTuple(A.noloc, List.map r types)
  | A.TId(_, id) -> (try r (instantiate_scheme (StringMap.find id ctx.aliases)) with Not_found -> t)

and expand_scheme ctx (v, t) =
  failwith "Check expand_scheme!";
  [], expand_type ctx t

and scheme_of_evar ctx name =
  try StringMap.find name ctx.evars
  with Not_found -> type_error A.noloc ("Unbound variable "^name)

let save_type e t ctx =
  {ctx with types_assoc = ExprMap.add e t ctx.types_assoc}

let retrieve_type ctx e = 
  try ExprMap.find e ctx.types_assoc
  with Not_found -> failwith ("This expression was never typechecked: "^String_of_ast.string_of_expr e)

(* Combo of a fold_left2 with a map2: the function f returns both
 * an accumulator and a transformed list element.
 *     ('acc -> 'a -> 'b -> ('acc*'c)) -> 'acc ->
 *     'a list -> 'b list -> ('acc * 'c list)
 *)
let list_fold_map2 f acc a_list b_list =
  let acc, rev_c_list = List.fold_left2
    (fun (acc, c_list) a b -> let acc, c = f acc a b in acc, c::c_list)
    (acc, []) a_list b_list
  in
  acc, List.rev rev_c_list

let get_evars ctx =
  List.map fst @@ StringMap.bindings ctx.evars

let rec unify ctx t0 t1 =
  (* TODO: have a direction, to choose a prefered model for the result and report loc
   * and differenciate nat <: int from int <: nat *)
  (* TODO: add awareness of nat <: int *)
  let t0 = expand_type ctx t0 in
  let t1 = expand_type ctx t1 in
  match t0, t1 with
  | A.TFail, t | t, A.TFail -> ctx, t
  | A.TId(_, id0), A.TId(_, id1) ->
    if id0=id1 then ctx, t0 else
      (* TODO use better ordering, which favors manually created vars. *)
      let id0, id1 = min id0 id1, max id0 id1 in
      if !_DEBUG_ then print_endline ("Constraint: var "^id1^" => var "^id0);
      add_alias id1 ([], A.TId(A.noloc, id0)) ctx, A.TId(A.noloc, id0)
  | A.TId(_, id), t | t, A.TId(_, id) ->
  if !_DEBUG_ then print_endline ("Constraint: var "^id^" => type "^P.string_of_type t);
      add_alias id ([], t) ctx, t
  | A.TLambda(_, t00, t01), A.TLambda(_, t10, t11) ->
    let ctx, t0 = unify ctx t00 t10 in
    let ctx, t1 = unify ctx t01 t11 in
    ctx, A.TLambda(A.noloc, t0, t1)
  (* | A.TApp(_, "nat", []), A.TApp(_, "int", []) | A.TApp(_, "int", []), A.TApp(_, "nat", []) ->
    ctx, A.TApp(A.noloc, "nat", []) *)
  | A.TApp(_, name0, args0), A.TApp(_, name1, args1)
    when name0=name1 && List.length args0 = List.length args1 ->
    let ctx, args_u = list_fold_map2 unify ctx args0 args1 in
    ctx, A.TApp(A.noloc, name0, args_u)
  | A.TTuple(_, a), A.TTuple(_, b) when List.length a = List.length b ->
    let ctx, c = list_fold_map2 unify ctx a b in
    ctx, A.TTuple(A.noloc, c)
  | _ -> type_error A.noloc ("Not unifiable: "^P.string_of_type t0^" and "^P.string_of_type t1)
  (* TODO add locations to msg. They must come from exprs, not types. *)