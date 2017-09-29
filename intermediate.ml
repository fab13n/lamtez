(* Compile a type lamtez term into an intermediate representation where:
 * * Nodes are fully type-annotated;
 * * Labelled products and sums are replaced by indexed versions;
 * * ELambda terms include their environments, the variables they capture
 *   out of their scope.
 * * TApp types are sorted between sums, products and primitives;
 * * TLambda carry a flag indicating whether they are closure-free;
 * * Patterns are precompiled in binders (ELambda, ESumCase, ELet);
 * * ESequences changed into ELet;
 *
 * sum and product type contents are lazy, because some inductive types
 * such as `list` have infinite expanded types. 
 *)

type tvar = string
type tname = string

type etype =
| TPrim    of tname * etype list
| TLambda  of etype * etype * bool (* arg, res, cmb *)
| TProduct of (tname * etype list) option * etype list Lazy.t
| TSum     of (tname * etype list) option * etype list Lazy.t (* TODO name and args shouldn't be optional. *)

type evar = string

type collection_kind = Ast.collection_kind

type typed_expr = expr * etype

and expr =
| ELit        of string
| EColl       of collection_kind * typed_expr list
| EId         of evar
| ELambda     of evar * etype * (evar*etype) list * typed_expr (* v_prm, t_prm, env, res *)
| ELet        of evar * typed_expr * typed_expr
| EApp        of typed_expr * typed_expr
| EProduct    of typed_expr list
| ESum        of int * int * typed_expr
| EProductGet of typed_expr * int * int
| EProductSet of typed_expr * int * int * typed_expr
| EStoreSet   of int * typed_expr * typed_expr
| ESumCase    of typed_expr * (evar * etype * typed_expr) list

type store = (int * etype) list

type contract = {
  storage_type: etype;
  storage_init: typed_expr option;
  code:         typed_expr }

let et_product et_list =
  let types = List.map snd et_list in
  let etype = TProduct(None, lazy types) in
  EProduct(et_list), etype

let get_free_evars ?except e =
  let module S = Set.Make(String) in
  let (+) = S.union
  and (-) s e = S.remove e s 
  and (--) s0 s1 = S.diff s0 s1 in
  let rec f et = match (fst et) with
    | EId(id) -> S.singleton id
    | ELit _ -> S.empty
    | ELambda(v, _, _, et0) -> f et0 - v
    | EApp(et0, et1)  -> f et0 + f et1
    | ELet(v, et0, et1) -> f et0 + (f et1 - v)
    | EColl(_, list) | EProduct(list) ->
      List.fold_left (+) S.empty (List.map f list) 
    | EProductSet(et0, _, _,  et1) | EStoreSet(_, et0, et1) -> 
      f et0 + f et1
    | EProductGet(et0, _, _)
    | ESum(_, _, et0) -> f et0
    | ESumCase(e, list) ->
      let fold acc (v, _, e) = acc + (f e - v) in
      List.fold_left fold (f e) list
  in
  let set = match except with
    | None -> f e 
    | Some exceptions -> f e -- S.of_list exceptions
  in List.sort compare @@ S.elements set
