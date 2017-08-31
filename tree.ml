
type tag = string
type evar = string
type tvar = string

type typeT =
  | TId of tvar
  | TLambda of typeT * typeT
  | TTuple of typeT list (* TODO encode as TApp("tupleN", list) *)
  | TApp of tvar * typeT list
  | TFail

type schemeT = tvar list * typeT

type declT =
  | DProduct of tvar * tvar list * (tag*typeT) list
  | DSum     of tvar * tvar list * (tag*typeT) list
  | DAlias   of tvar * tvar list * typeT
  | DPrim    of tvar * tvar list

type binOp =
  | BEq | BNeq | BLe | BLt | BGe | BGt | BConcat
  | BOr | BAnd | BXor | BAdd | BSub | BMul | BDiv | BLsr | BLsl

type unOp = UNot | UNeg | UAbs

type exprT =
  | ENat of int
  | EInt of int
  | EString of string
  | ETez of int
  | ETime of string
  | ESig of string

  | EId of evar
  | ELambda of evar * schemeT * exprT
  | ELetIn of evar * typeT * exprT * exprT (* TODO type should be a scheme for consistency *)
  | EApp of exprT * exprT

  | ETuple of exprT list
  | ETupleGet of exprT * int

  | EProduct of (tag*exprT) list
  | EProductGet of exprT * tag
  | EProductSet of exprT * tag * exprT
  
  | ESum of tag * exprT
  | ESumCase of exprT * (tag * (evar * exprT)) list

  | EBinOp of exprT * binOp * exprT
  | EUnOp of unOp * exprT

  | ETypeAnnot of exprT * typeT

type programT = declT list * (tag * typeT) list * exprT

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

(* Rename variables whenever necessary so that no variable binder
 * shadows another. *)
let rec unshadow scoped e =
  let r = unshadow scoped in
  match e with
  | EString _ | ENat _| EInt _ | ETez _ | ETime _ | ESig _ | EId _ -> e
  | ELambda(v, t, e0) when List.mem v scoped ->
    let v' = fresh_var ~prefix:v () in
    ELambda(v', t, replace_evar v (EId v') e0)
  | ELambda(v, t, e0) ->
    ELambda(v, t, unshadow (v::scoped) e0)
  | ELetIn(v, t, e0, e1) when List.mem  v scoped ->
    let v' = fresh_var ~prefix: v () in
    ELetIn(v', t, r e0, replace_evar v (EId v') e1)
  | ELetIn(v, t, e0, e1) ->
    ELetIn(v, t, r e0, unshadow (v::scoped) e1)
  | EApp(e0, e1) -> EApp(r e0, r e1)
  | ETuple(list) -> ETuple(List.map r list)
  | ETupleGet(e0, tag) -> ETupleGet(r e0, tag)
  | EProduct(pairs) -> EProduct (List.map (fun (tag, e) -> (tag, r e)) pairs)
  | EProductGet(e, tag) -> EProductGet(r e, tag)
  | EProductSet(e0, tag, e1) -> EProductSet(r e0, tag, r e1)
  | ESum(tag, e0) -> ESum(tag, r e0)
  | ESumCase(e0, pairs) -> 
    let f (tag, (v, e)) = 
      if List.mem v scoped then
        let v' = fresh_var ~prefix:v () in
        (tag, (v, replace_evar v (EId v') e))
      else (tag, (v, unshadow (v::scoped) e))
    in
    ESumCase(r e0, (List.map f pairs))
  | EBinOp(e0, op, e1) -> EBinOp(r e0, op, r e1)
  | EUnOp(op, e0) -> EUnOp(op, r e0)
  | ETypeAnnot(t, e0) -> ETypeAnnot(r t, e0)

(* Keep track of: EXEC  LOOP EDIV  *)
(* Units: tez time signature key *)
(* Euclidian division: None if zero, Some(div, rest) otherwis; also works on tez *)
(* For CREATE_ACCOUNT: eca_spendable has to be false, eca_code has to be None, storage has to be Unit *)
