type tag  = string
type evar = string
type tvar = string

type loc = (Lexing.position * Lexing.position) option
let noloc = None

type etype =
  | TId     of loc * tvar
  | TLambda of loc * etype * etype
  | TTuple  of loc * etype list (* TODO encode as TApp("tupleN", list) *)
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

type expr =
  | ENat    of loc * int
  | EInt    of loc * int
  | EString of loc * string
  | ETez    of loc * int
  | ETime   of loc * string
  | ESig    of loc * string

  | EId     of loc * evar
  | ELambda of loc * evar * scheme * expr
  | ELet    of loc * evar * etype * expr * expr (* TODO type should be a scheme for consistency *)
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

type contract = decl list * (tag * etype) list * expr

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
| ENat(loc, _) | EInt(loc, _) | EString(loc, _) | ETez(loc, _) | ETime(loc, _)
| ESig(loc, _) | EId(loc, _) | ELambda(loc, _, _, _) | ELet(loc, _, _, _, _)
| EApp(loc, _, _) | ETuple(loc, _) | ETupleGet(loc, _, _) | EProduct(loc, _)
| EProductGet(loc, _, _) | EProductSet(loc, _, _, _) | EStoreSet(loc, _, _, _)
| ESum(loc, _, _) | ESumCase(loc, _, _) | EBinOp(loc, _, _, _) | EUnOp(loc, _, _)
| ETypeAnnot(loc, _, _) -> loc

let loc_of_etype = function
| TId(loc, _) | TLambda(loc, _, _) | TTuple(loc, _) | TApp(loc, _, _) -> loc
| TFail -> noloc

let loc_of_dec = function
| DProduct(loc, _, _, _) | DSum(loc, _, _, _)
| DAlias(loc, _, _, _) | DPrim(loc, _, _) -> loc

let tprim0 id = TApp(noloc, id, [])
let rec tlambda = function [] -> raise Not_found | [t] -> t | t :: ts' -> TLambda(noloc, t, tlambda ts')
let tzero = TApp(noloc, "zero", [])
let tunit = TApp(noloc, "unit", [])
let toption x = TApp(noloc, "option", [x])
let tlist = TFail

let fresh_var =
  let fresh_var_counter = ref 0 in
  fun ?prefix:(prefix="") () ->
    incr fresh_var_counter;
    prefix ^ "%" ^ string_of_int !fresh_var_counter

let fresh_tvar ?prefix:(prefix="_") () = TId(noloc, fresh_var())
let fresh_evar ?prefix:(prefix="_") () = EId(noloc, fresh_var())

let fresh_vars, fresh_tvars, fresh_evars =
  let rec f g acc = function 0 -> acc | n -> f g (g()::acc) (n-1) in
  let repeat (type a) (g:?prefix:string -> unit -> a) ?prefix:(prefix="_") n =
    List.rev (f (g ~prefix) [] n) in
  repeat fresh_var, repeat fresh_tvar, repeat fresh_evar

let rec replace_evar var e e' =
  let r = replace_evar var e in
  match e' with
  | EId(_, var') when var'=var -> e
  | EString _ | ENat _| EInt _| ETez _ | ETime _ | ESig _ | EId _ -> e'
  | ELambda(_, var', _, _) when var'==var -> e'
  | ELambda(loc, var', t, e0) -> ELambda(loc, var', t, r e0)
  | ELet(loc, var', t, e0, e1) when var=var' -> ELet(loc, var', t, r e0, e1)
  | ELet(loc, var', t, e0, e1) -> ELet(loc, var', t, r e0, r e1)
  | EApp(loc, e0, e1) -> EApp(loc, r e0, r e1)
  | ETuple(loc, list) -> ETuple (loc, List.map r list)
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
