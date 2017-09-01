
type tag  = string
type evar = string
type tvar = string

type etype =
  | TId of tvar
  | TLambda of etype * etype
  | TTuple of etype list (* TODO encode as TApp("tupleN", list) *)
  | TApp of tvar * etype list
  | TFail

type scheme = tvar list * etype

type decl =
  | DProduct of tvar * tvar list * (tag*etype) list
  | DSum     of tvar * tvar list * (tag*etype) list
  | DAlias   of tvar * tvar list * etype
  | DPrim    of tvar * tvar list

type binOp =
  | BEq | BNeq | BLe | BLt | BGe | BGt | BConcat
  | BOr | BAnd | BXor | BAdd | BSub | BMul | BDiv | BLsr | BLsl

type unOp = UNot | UNeg | UAbs

type expr =
  | ENat of int
  | EInt of int
  | EString of string
  | ETez of int
  | ETime of string
  | ESig of string

  | EId of evar
  | ELambda of evar * scheme * expr
  | ELetIn of evar * etype * expr * expr (* TODO type should be a scheme for consistency *)
  | EApp of expr * expr

  | ETuple of expr list
  | ETupleGet of expr * int

  | EProduct of (tag*expr) list
  | EProductGet of expr * tag
  | EProductSet of expr * tag * expr
  | EStoreSet of tag * expr * expr

  | ESum of tag * expr
  | ESumCase of expr * (tag * (evar * expr)) list

  | EBinOp of expr * binOp * expr
  | EUnOp of unOp * expr

  | ETypeAnnot of expr * etype

type contract = decl list * (tag * etype) list * expr

let tprim0 id = TApp(id, [])
let rec tlambda = function [] -> raise Not_found | [t] -> t | t :: ts' -> TLambda(t, tlambda ts')
let tzero = TApp("zero", [])
let tunit = TApp("unit", [])
let toption x = TApp("option", [x])
let tlist = TFail

let fresh_var =
  let fresh_var_counter = ref 0 in
  fun ?prefix:(prefix="_") () ->
    incr fresh_var_counter;
    prefix ^ "%" ^ string_of_int !fresh_var_counter

let fresh_tvar ?prefix:(prefix="_") () = TId(fresh_var())
let fresh_evar ?prefix:(prefix="_") () = EId(fresh_var())

let fresh_vars, fresh_tvars, fresh_evars =
  let rec f g acc = function 0 -> acc | n -> f g (g()::acc) (n-1) in
  let repeat (type a) (g:?prefix:string -> unit -> a) ?prefix:(prefix="_") n =
    List.rev (f (g ~prefix) [] n) in
  repeat fresh_var, repeat fresh_tvar, repeat fresh_evar

let rec replace_evar var e e' =
  let r = replace_evar var e in
  match e' with
  | EId var' when var'=var -> e
  | EString _ | ENat _| EInt _| ETez _ | ETime _ | ESig _ | EId _ -> e'
  | ELambda(var', _, _) when var'==var -> e'
  | ELambda(var', t, e0) -> ELambda(var', t, r e0)
  | ELetIn(var', t, e0, e1) when var=var' -> ELetIn(var', t, r e0, e1)
  | ELetIn(var', t, e0, e1) -> ELetIn(var', t, r e0, r e1)
  | EApp(e0, e1) -> EApp(r e0, r e1)
  | ETuple(list) -> ETuple (List.map r list)
  | ETupleGet(e0, tag) -> ETupleGet(r e0, tag)
  | EProduct(pairs) -> EProduct (List.map (fun (tag, e) -> (tag, r e)) pairs)
  | EProductGet(e0, tag) -> EProductGet(e0, tag)
  | EProductSet(e0, tag, e1) -> EProductSet(r e0, tag, r e1)
  | EStoreSet(v, e0, e1) -> EStoreSet(v, r e0, r e1)
  | ESum(tag, e0) -> ESum(tag, r e0)
  | ESumCase(e0, cases) ->
    let f (tag, (var', ec)) = if var'=var then (tag, (var, ec)) else (tag, (var, r ec)) in
    ESumCase(r e0, (List.map f cases))
  | EBinOp(e0, op, e1) -> EBinOp(r e0, op, r e1)
  | EUnOp(op, e0) -> EUnOp(op, r e0)
  | ETypeAnnot(e0, t) -> ETypeAnnot(r e0, t)

let rec replace_tvar var t term =
  let r = replace_tvar var t in
  match term with
  | TId var' when var'=var -> t
  | TId _ | TFail -> term
  | TLambda(t0, t1) -> TLambda(r t0, r t1)
  | TApp(name, type_args) -> TApp(name, List.map r type_args)
  | TTuple(list) -> TTuple(List.map r list)

let replace_tvars tvars types t = List.fold_left2
    (fun t v t' -> replace_tvar v t' t)
    t tvars types


(* Keep track of: EXEC  LOOP EDIV  *)
(* Units: tez time signature key *)
(* Euclidian division: None if zero, Some(div, rest) otherwis; also works on tez *)
(* For CREATE_ACCOUNT: eca_spendable has to be false, eca_code has to be None, storage has to be Unit *)
