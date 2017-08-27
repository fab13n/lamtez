
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
  | ENum of int
  | EString of string
  | ETez of int
  | ETime of string
  | ESig of string

  | EId of evar
  | ELambda of evar * schemeT * exprT
  | ELetIn of evar * exprT * exprT
  | EApp of exprT * exprT

  | ETuple of exprT list
  | ETupleGet of exprT * int

  | EProduct of (tag*exprT) list
  | EProductGet of exprT * tag
  
  | ESum of tag * exprT
  | ESumCase of exprT * (tag * (evar * exprT)) list

  | EBinOp of exprT * binOp * exprT
  | EUnOp of unOp * exprT

  | ETypeAnnot of exprT * typeT

type programT = declT list * exprT

let tprim0 id = TApp(id, [])
let rec tlambda = function [] -> raise Not_found | [t] -> t | t :: ts' -> TLambda(t, tlambda ts')
let tzero = TApp("zero", [])
let tone = TApp("one", [])
let toption x = TApp("option", [x])
let tlist = TFail

let fresh_var =
  let fresh_var_counter = ref 0 in
  fun ?prefix:(prefix="_") () -> 
    incr fresh_var_counter;
    prefix ^ "%" ^ string_of_int !fresh_var_counter

let fresh_tvar ?prefix:(prefix="_") () = TId(fresh_var())
let fresh_evar ?prefix:(prefix="_") () = EId(fresh_var())


let rec replace_evar var t term = 
  let r = replace_evar var t in
  match term with
  | EId var' when var'=var -> t 
  | EString _ | ENum _| ETez _ | ETime _ | ESig _ | EId _ -> term
  | ELambda(var', t, term') when var'==var -> term
  | ELambda(var', t, term') -> ELambda(var', t, r term')
  | ELetIn(var', t0, t1) when var=var' -> ELetIn(var', r t0, t1)
  | ELetIn(var', t0, t1) -> ELetIn(var', r t0, r t1)  
  | EApp(t0, t1) -> EApp(r t0, r t1)
  | ETuple(list) -> ETuple (List.map r list)
  | ETupleGet(t, tag) -> ETupleGet(r t, tag)
  | EProduct(pairs) -> EProduct (List.map (fun (tag, t) -> (tag, r t)) pairs)
  | EProductGet(t, tag) -> EProductGet(t, tag)
  | ESum(tag, t) -> ESum(tag, r t)
  | ESumCase(t, triplets) -> 
    let f (tag, (var', t)) = if var'=var then (tag, (var, t)) else (tag, (var, r t)) in
    ESumCase(r t, (List.map f triplets))
  | EBinOp(a, op, b) -> EBinOp(r a, op, r b)
  | EUnOp(op, a) -> EUnOp(op, r a)
  | ETypeAnnot(t, a) -> ETypeAnnot(r t, a)

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
let rec unshadow scoped term =
  let r = unshadow scoped in
  match term with
  | EString _ | ENum _| ETez _ | ETime _ | ESig _ | EId _ -> term
  | ELambda(v, t, term') when List.mem v scoped ->
    let v' = fresh_var ~prefix:v () in
    ELambda(v', t, replace_evar v (EId v') term')
  | ELambda(v, t, term') ->
    ELambda(v, t, unshadow (v::scoped) term')
  | ELetIn(v, e0, e1) when List.mem  v scoped ->
    let v' = fresh_var ~prefix: v () in
    ELetIn(v', r e0, replace_evar v (EId v') e1)
  | ELetIn(v, e0, e1) ->
    ELetIn(v, r e0, unshadow (v::scoped) e1)
  | EApp(t0, t1) -> EApp(r t0, r t1)
  | ETuple(list) -> ETuple(List.map r list)
  | ETupleGet(t, tag) -> ETupleGet(r t, tag)
  | EProduct(pairs) -> EProduct (List.map (fun (tag, t) -> (tag, r t)) pairs)
  | EProductGet(t, tag) -> EProductGet(t, tag)
  | ESum(tag, t) -> ESum(tag, r t)
  | ESumCase(t, pairs) -> 
    let f (tag, (v, t)) = 
      if List.mem v scoped then
        let v' = fresh_var ~prefix:v () in
        (tag, (v, replace_evar v (EId v') t))
      else (tag, (v, unshadow (v::scoped) t))
    in
    ESumCase(r t, (List.map f pairs))
  | EBinOp(a, op, b) -> EBinOp(r a, op, r b)
  | EUnOp(op, a) -> EUnOp(op, r a)
  | ETypeAnnot(t, a) -> ETypeAnnot(r t, a)

(* Keep track of: EXEC  LOOP EDIV  *)
(* Units: tez time signature key *)
(* Euclidian division: None if zero, Some(div, rest) otherwis; also works on tez *)
(* For CREATE_ACCOUNT: eca_spendable has to be false, eca_code has to be None, storage has to be Unit *)
