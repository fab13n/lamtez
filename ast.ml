type tag  = string
type evar = string
type tvar = string

type loc = (Lexing.position * Lexing.position) option
let noloc = None

type etype =
  | TId     of loc * tvar
  | TLambda of loc * etype * etype
  | TTuple  of loc * etype list (* TODO encode as TApp("tuple-N", list)? *)
  | TApp    of loc * tvar * etype list
  | TFail

type scheme = tvar list * etype

type decl =
  | DProduct of loc * tvar * tvar list * (tag*etype) list
  | DSum     of loc * tvar * tvar list * (tag*etype) list
  | DAlias   of loc * tvar * tvar list * etype
  | DPrim    of loc * tvar * tvar list

type binOp =
  | BEq | BNeq | BLe | BLt | BGe | BGt | BConcat
  | BOr | BAnd | BXor | BAdd | BSub | BMul | BDiv | BLsr | BLsl

type unOp = UNot | UNeg | UAbs

type literal =
  | LNat    of loc * int
  | LInt    of loc * int
  | LString of loc * string
  | LTez    of loc * int
  | LTime   of loc * string
  | LSig    of loc * string

type collection_kind = CSet | CMap | CList

type expr =
  | ELit    of loc * literal
  | EColl   of loc * collection_kind * expr list
  | EId     of loc * evar
  | ELambda of loc * evar * scheme * expr (* TODO optional result annotation *)
  | ELet    of loc * evar * etype * expr * expr (* TODO type should be a scheme for consistency *)
  | ESequence of loc * expr list
  | EApp    of loc * expr * expr

  | ETuple    of loc * expr list
  | ETupleGet of loc * expr * int

  | EProduct    of loc * (tag*expr) list
  | EProductGet of loc * expr * tag
  | EProductSet of loc * expr * tag * expr
  | EStoreSet   of loc * tag * expr * expr

  | ESum     of loc * tag * expr
  | ESumCase of loc * expr * (tag * (evar * expr)) list

  | EBinOp of loc * expr * binOp * expr
  | EUnOp  of loc * unOp * expr

  | ETypeAnnot of loc * expr * etype

type contract = decl list * (tag * etype * expr option) list * expr

let string_of_loc: loc -> string = function
  | None -> "?"
  | Some((p1, p2)) ->
    let open Printf in
    let open Lexing in
    if p1.pos_lnum=p2.pos_lnum then 
      sprintf "File \"%s\", line %d, characters %d-%d" 
              p1.pos_fname p1.pos_lnum p1.pos_cnum p2.pos_cnum
    else
      sprintf "File \"%s\", line %d-%d, characters %d-%d" 
              p1.pos_fname p1.pos_lnum p2.pos_lnum p1.pos_cnum p2.pos_cnum

let loc_of_expr = function
| ELit(loc, _) | EColl(loc, _, _)| EId(loc, _) | ELambda(loc, _, _, _) | ELet(loc, _, _, _, _)
| EApp(loc, _, _) | ETuple(loc, _) | ETupleGet(loc, _, _) | EProduct(loc, _)
| EProductGet(loc, _, _) | EProductSet(loc, _, _, _) | EStoreSet(loc, _, _, _)
| ESum(loc, _, _) | ESumCase(loc, _, _) | EBinOp(loc, _, _, _) | EUnOp(loc, _, _)
| ETypeAnnot(loc, _, _) | ESequence(loc, _) -> loc

let loc_of_etype = function
| TId(loc, _) | TLambda(loc, _, _) | TTuple(loc, _) | TApp(loc, _, _) -> loc
| TFail -> noloc

let loc_of_decl = function
| DProduct(loc, _, _, _) | DSum(loc, _, _, _)
| DAlias(loc, _, _, _) | DPrim(loc, _, _) -> loc

let fresh_var =
  let fresh_var_counter = ref 0 in
  fun ?prefix:(prefix="") () ->
    incr fresh_var_counter;
    prefix ^ "%" ^ string_of_int !fresh_var_counter

let fresh_tvar ?prefix:(prefix="") () = TId(noloc, fresh_var ~prefix ())
let fresh_evar ?prefix:(prefix="") () = EId(noloc, fresh_var ~prefix ())

let noloc = None

let loc2 a b = match a, b with
  | Some(a, _), Some(_, b) | Some(a, b), None | None, Some(a, b) -> Some(a, b)
  | None, None -> None
let loc2e a b = loc2 (loc_of_expr a) (loc_of_expr b)

let rec tlambda ?(loc=noloc) l = match l with
  | [] -> raise (Invalid_argument "tlambda")
  | [t] -> t 
  | t :: ts' -> TLambda(loc, t, tlambda ts')
let tapp ?(loc=noloc) name args = TApp(noloc, name, args)
let tprim ?(loc=noloc) id = tapp id []
let tzero = tprim "zero" 
let tunit = TTuple(noloc, [])
let toption ?(loc=noloc) x = tapp "option" [x]
let tid ?(loc=noloc) id = TId(loc, id)
let ttuple ?(loc=noloc) list = match list with
| [] -> tunit
| [t] -> t
| list -> TTuple(loc, list)

let eid ?(loc=noloc) id = EId(loc, id)
let eunit_loc ~loc = ETuple(loc, [])
let eunit = eunit_loc noloc
let etuple ?(loc=noloc) list = match list with
  | [] -> eunit_loc ~loc
  | [e] -> e
  | list -> ETuple(loc, list) 
let esum ?(loc=noloc) id args = 
  let arg = match args with
  | [] -> eunit
  | [e] -> e
  | list ->
    let loc = loc2e (List.hd list) (List.hd (List.rev list)) in
    etuple ~loc list in
  ESum(loc, id, arg) 
let eapp = function [] -> assert false | f :: args ->
  let l1 = loc_of_expr f in
  let fold acc arg =
    let loc = loc2 l1 (loc_of_expr arg) in
    EApp(loc, acc, arg) in
  List.fold_left fold f args
let esequence ?(loc=noloc) l = ESequence(loc, l)
let eif ?(loc=noloc) list = (* TODO handle locs better *)
  let rec f = function
    | [cond, body_then; ESum(_, "True", _), body_else] -> 
      ESumCase(loc, cond, 
               ["True", (fresh_var(), body_then);
                "False",(fresh_var(), body_else)])
    | [cond, body] -> 
      ESumCase(loc, cond, 
               ["True", (fresh_var(), body);
                "False",(fresh_var(), eunit)])
    | (cond, body_then) :: rest -> 
      ESumCase(loc, cond, 
               ["True", (fresh_var(), body_then);
                "False",(fresh_var(), f rest)])
    | [] -> raise (Invalid_argument "eif")
  in
  f list 

let fresh_vars, fresh_tvars, fresh_evars =
  let rec f g acc = function 0 -> acc | n -> f g (g()::acc) (n-1) in
  let repeat (type a) (g:?prefix:string -> unit -> a) ?prefix:(prefix="") n =
    List.rev (f (g ~prefix) [] n) in
  repeat fresh_var, repeat fresh_tvar, repeat fresh_evar

let get_free_tvars t =
  let module S = Set.Make(String) in
  let rec f = function
    | TFail -> S.empty
    | TId(_, id) -> S.singleton id
    | TLambda(_, e0, e1) -> S.union (f e0) (f e1)
    | TTuple(_, list) 
    | TApp(_, _, list) -> 
      List.fold_left S.union S.empty (List.map f list) in
  S.elements (f t)

let rec replace_evar var e e' =
  let r = replace_evar var e in
  match e' with
  | EId(_, var') when var'=var -> e
  | ELit _ | EId _ -> e'
  | EColl(loc, kind, list) -> EColl(loc, kind, List.map r list)
  | ELambda(_, var', _, _) when var'==var -> e'
  | ELambda(loc, var', t, e0) -> ELambda(loc, var', t, r e0)
  | ELet(loc, var', t, e0, e1) when var=var' -> ELet(loc, var', t, r e0, e1)
  | ELet(loc, var', t, e0, e1) -> ELet(loc, var', t, r e0, r e1)
  | EApp(loc, e0, e1) -> EApp(loc, r e0, r e1)
  | ETuple(loc, list) -> ETuple (loc, List.map r list)
  | ESequence(loc, list) -> ESequence (loc, List.map r list)
  | ETupleGet(loc, e0, tag) -> ETupleGet(loc, r e0, tag)
  | EProduct(loc, pairs) -> EProduct (loc, List.map (fun (tag, e) -> (tag, r e)) pairs)
  | EProductGet(loc, e0, tag) -> EProductGet(loc, e0, tag)
  | EProductSet(loc, e0, tag, e1) -> EProductSet(loc, r e0, tag, r e1)
  | EStoreSet(loc, v, e0, e1) -> EStoreSet(loc, v, r e0, r e1)
  | ESum(loc, tag, e0) -> ESum(loc, tag, r e0)
  | ESumCase(loc, e0, cases) ->
    let f (tag, (var', ec)) = if var'=var then (tag, (var, ec)) else (tag, (var, r ec)) in
    ESumCase(loc, r e0, (List.map f cases))
  | EBinOp(loc, e0, op, e1) -> EBinOp(loc, r e0, op, r e1)
  | EUnOp(loc, op, e0) -> EUnOp(loc, op, r e0)
  | ETypeAnnot(loc, e0, t) -> ETypeAnnot(loc, r e0, t)

let rec replace_tvar var t term =
  let r = replace_tvar var t in
  match term with
  | TId(_, var') when var'=var -> t
  | TId _ | TFail -> term
  | TLambda(loc, t0, t1) -> TLambda(loc, r t0, r t1)
  | TApp(loc, name, type_args) -> TApp(loc, name, List.map r type_args)
  | TTuple(loc, list) -> TTuple(loc, List.map r list)

let replace_tvars tvars types t = List.fold_left2
    (fun t v t' -> replace_tvar v t' t)
    t tvars types

(* Keep track of: EXEC  LOOP EDIV  *)
(* Units: tez time signature key *)
(* Euclidian division: None if zero, Some(div, rest) otherwis; also works on tez *)
(* For CREATE_ACCOUNT: eca_spendable has to be false, eca_code has to be None, storage has to be Unit *)
