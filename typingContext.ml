open Utils
open Tree

let _DEBUG_ = true

module StringMap = Map.Make(String)

type composite = {type_params: tvar list; cases: (tag*Tree.typeT) list}
type substitutions = (tvar * Tree.typeT) list

type t = {
  sums: composite StringMap.t; (* type_params, (case, type)* *)
  products: composite StringMap.t;
  product_tags: string StringMap.t;
  sum_tags: string StringMap.t;
  aliases: schemeT StringMap.t;
  primitives: tvar list StringMap.t;
  evars: schemeT StringMap.t;
}

let empty = {
  sums = StringMap.empty;
  products = StringMap.empty;
  sum_tags = StringMap.empty;
  product_tags = StringMap.empty;
  aliases = StringMap.empty;
  evars = StringMap.empty;
  primitives = StringMap.empty;
}

let string_of_t ctx =
  let open TreePrint in 
  let list_of_map m = StringMap.fold (fun name x acc -> (name, x)::acc) m [] in
  let string_of_comp sep (name, c) = 
    "type "^name ^" "^ sep_list " " (fun x->x) c.type_params ^ " = " ^ 
    sep_list sep (fun (tag, t) -> tag^" "^string_of_type t) c.cases
  in
  let string_of_alias (name, (p, t)) = "type "^sep_list " " (fun x->x) (name::p)^" = "^string_of_type t in
  let string_of_evar (name, s) = "val "^name^": "^string_of_scheme s in
  let is_not_dummy_alias = function name, ([], TApp(name', [])) -> false | _ -> true in
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
    in DSum(name, c.type_params, c.cases)
  with Not_found -> try
    let c = StringMap.find name ctx.products
    in DProduct(name, c.type_params, c.cases)
  with Not_found -> try
    let params = StringMap.find name ctx.primitives
    in DPrim(name, params)
  with Not_found -> try
    let (params, t) = StringMap.find name ctx.aliases
    in DAlias(name, params, t)
  with Not_found ->
    raise Not_found

let check_fresh_name ctx name =
  if StringMap.mem name ctx.sums
  || StringMap.mem name ctx.products
  || StringMap.mem name ctx.aliases 
  || StringMap.mem name ctx.primitives
  then type_error ("duplicate type name "^name)
  
let check_fresh_tag map cases =
  List.iter (fun (tag, _) -> if StringMap.mem tag map then type_error ("duplicate tag "^tag)) cases

let add_alias name scheme ctx = 
  check_fresh_name ctx name;
  {ctx with aliases = StringMap.add name scheme ctx.aliases}

let add_composite names_map tags_map aliases_map name type_params cases ctx =
  check_fresh_name ctx name;
  check_fresh_tag ctx.sum_tags cases;
  check_fresh_tag ctx.product_tags cases;
  ( (if type_params<>[] then aliases_map else StringMap.add name ([], TApp(name, [])) aliases_map),
    StringMap.add name {type_params; cases} names_map,
    List.fold_left (fun tags_map (tag, _) -> StringMap.add tag name tags_map) tags_map cases)

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
     add_alias name ([], TApp(name, [])) ctx in
  let p = StringMap.add name type_params ctx.primitives in
  {ctx with primitives = p}

let add_evar name t ctx =
  {ctx with evars=StringMap.add name t ctx.evars}

let forget_evar name ctx =
  {ctx with evars=StringMap.remove name ctx.evars}

type u = evar * schemeT option

let push_evar name t ctx =
  let prev_content = try Some(StringMap.find name ctx.evars) with Not_found -> None in
  add_evar name t ctx, (name, prev_content)

let pop_evar (name, prev_t) ctx =
  match prev_t with
  | None -> forget_evar name ctx
  | Some t -> add_evar name t ctx

let instantiate_scheme (params, t) =
  let x = List.fold_left (fun t p -> replace_tvar p (fresh_tvar()) t) t params in
  (* print_endline ("Instanciate "^TreePrint.string_of_scheme (params, t)^" ::= "^TreePrint.string_of_type x); *)
  x

let instantiate_composite name (params, d_pairs) =
  let subst = List.map (fun v -> (v, fresh_tvar())) params in
  let r (tag, t) = tag, List.fold_left (fun t (v, v') -> replace_tvar v v' t) t subst in
  TApp(name, List.map snd subst), List.map r d_pairs

(* Replace tvars with their values as much as possible, deep into a typeT *)
let rec expand_type ctx t =
  let r = expand_type ctx in  
  match t with
  | TFail -> t
  | TLambda(t0, t1) -> TLambda(r t0, r t1)
  | TApp(name, args) -> TApp(name, List.map r args)
  | TTuple(types) -> TTuple(List.map r types)
  | TId id -> (try r (instantiate_scheme (StringMap.find id ctx.aliases)) with Not_found -> t)

and expand_scheme ctx (v, t) =
  failwith "Check expand_scheme!";
  [], expand_type ctx t

and scheme_of_evar ctx name = 
  try StringMap.find name ctx.evars
  with Not_found -> type_error("Unbound variable "^name)

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

let rec unify ctx t0 t1 =
  (* TODO: add awareness of nat <: int *)
  let t0 = expand_type ctx t0 in
  let t1 = expand_type ctx t1 in
  match t0, t1 with
  | TFail, t | t, TFail -> ctx, t
  | TId id0, TId id1 ->
    if id0=id1 then ctx, t0 else
      (* TODO use better ordering, which favors manually created vars. *)
      let id0, id1 = min id0 id1, max id0 id1 in
      print_endline ("Constraint: var "^id1^" => var "^id0);
      add_alias id1 ([], TId id0) ctx, TId id0
  | TId id, t | t, TId id ->
      print_endline ("Constraint: var "^id^" => type "^TreePrint.string_of_type t);
      add_alias id ([], t) ctx, t
  | TLambda(t00, t01), TLambda(t10, t11) ->
    let ctx, t0 = unify ctx t00 t10 in
    let ctx, t1 = unify ctx t01 t11 in
    ctx, TLambda(t0, t1)
  | TApp("nat", []), TApp("int", []) | TApp("int", []), TApp("nat", []) ->
    ctx, TApp("nat", [])
  | TApp(name0, args0), TApp(name1, args1) 
    when name0=name1 && List.length args0 = List.length args1 ->
    let ctx, args_u = list_fold_map2 unify ctx args0 args1 in
    ctx, TApp(name0, args_u)
  | TTuple(a), TTuple(b) when List.length a = List.length b ->
    let ctx, c = list_fold_map2 unify ctx a b in
    ctx, TTuple(c)
  | _ -> type_error ("Not unifiable: "^TreePrint.string_of_type t0^" and "^TreePrint.string_of_type t1)

