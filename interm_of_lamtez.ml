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
open Tree
open TypingContext
open Printf

type itVar = string

type iType =
| ITPrim of itVar * iType list
| ITLambda of iType list * iType
| ITProduct of (itVar * iType list) option * iType list Lazy.t
| ITSum of (itVar * iType list) option * iType list Lazy.t

type ieVar = string

type iTypedExpr = iExpr * iType

and iExpr =
| IELit of string
| IEId of ieVar
| IELambda of (ieVar * iType) list * iTypedExpr
| IELetIn of (ieVar * iTypedExpr * iTypedExpr)
| IEApp of iTypedExpr * iTypedExpr list
| IEProduct of iTypedExpr list
| IESum of int * int * iTypedExpr
| IEProductGet of iTypedExpr * int * int
| IESumCase of iTypedExpr * (ieVar * iType * iTypedExpr) list
(* TODO add support for options and lists? *)


let rec string_of_iType = 
  let t = string_of_iType in
  function
  | ITPrim(name, []) -> name
  | ITPrim(name, args) -> "("^name^sep_list " " t args^")"  
  | ITLambda(params, result) -> "("^sep_list ", " t params^" -> "^t result^")"
  | ITProduct(Some("unit", []), lazy []) -> "unit"
  | ITProduct(_, lazy []) -> "(*)"
  | ITProduct(_, lazy list) -> "("^sep_list " * " t list^")"
  | ITSum(_, lazy []) -> "(+)"
  | ITSum(_, lazy list) -> "("^sep_list " + " t list^")"

let rec string_of_iExpr = 
  let t = string_of_iType in
  let et = string_of_iTypedExpr in
  function
  | IELit s | IEId s -> s
  | IELambda(params, body) ->
    "(\\"^sep_list " " (fun (v, vt) -> "["^v^":"^t vt^"]") params^" -> "^et body^")"
  | IELetIn(v, e0, e1) -> "let "^v^" = "^et e0^" in "^et e1
  | IEApp(f, args) -> "("^sep_list " " et (f::args)^")"
  | IEProduct x  -> "("^sep_list ", " et x^")"
  | IESum (i, n, x) -> sprintf "{%d/%d} %s" i n (et x)
  | IEProductGet(x, i, n) -> sprintf "%s.{%d/%d}" (et x) i n
  | IESumCase(e, cases) -> 
    let f (var, it, e_case) = "["^var^":"^t it^"] -> "^et e_case in
    "("^et e^" ? "^sep_list " | " f cases^")"

and string_of_iTypedExpr (e, t) = "["^string_of_iExpr e^":"^string_of_iType t^"]"

let rec string_of_untyped_iExpr e =
  let r (e, t) = string_of_untyped_iExpr e in
  match e with
  | IELit s | IEId s -> s
  | IELambda(params, body) ->
    "\\"^sep_list " " fst params^" -> "^r body
  | IELetIn(v, e0, e1) -> "let "^v^" = "^r e0^" in "^r e1
  | IEApp(f, args) -> "("^sep_list " " r (f::args)^")"
  | IEProduct x  -> "("^sep_list ", " r x^")"
  | IESum (i, n, x) -> sprintf "%d(%s)" i (r x)
  | IEProductGet(x, i, n) -> sprintf "%s.%d" (r x) i
  | IESumCase(e, cases) ->
    let f i (v, _, e_case) = sprintf "%d(%s): %s" i v (r e_case) in
    let cases = List.mapi f cases in
    "("^r e^" ? "^String.concat " | " cases^")"
  
let prim_translations = [
  "time", "timestamp"; "sig", "signature";
]  

let rec compile_typeT ctx t =
  let c = compile_typeT ctx in
  match t with
  | TId id ->
    begin match TypingContext.expand_type ctx t with (* TODO the re-expansion shouldn't be necessary here *)
    | TId id -> failwith ("unresolved type variable "^id)
    | t -> c t
    end
  | TLambda _ as t ->
    let rec get = function TLambda(a, b) -> let p, t = get b in a::p, t | t -> [], t in
    let params, result = get t in
    ITLambda(List.map c params, c result) 
  | TTuple(list) -> ITProduct(None, lazy(List.map c list))
  | TApp(name, args) -> begin match TypingContext.decl_of_name ctx name with
    | DProduct(name, params, fields) ->
      ITProduct(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args fields)))
    | DSum(name, params, cases) ->
      ITSum(Some(name, List.map c args), lazy(List.map c (compile_decl_pairs params args cases)))
    | DPrim(name, params) ->
      let name = try List.assoc name prim_translations with Not_found -> name in
      ITPrim(name, List.map c args)
    | DAlias _ -> unsound "Aliases should have been simplified by now"
  end    
  | TFail -> ITPrim("fail", [])

and compile_decl_pairs params args tagged_fields =
  List.map (fun (tag, t) -> replace_tvars params args t) tagged_fields

let binop_dic = [
  BEq, "EQ"; BNeq, "NEQ"; BLe, "LE"; BLt, "LT"; BGe, "GE"; BGt, "GT"; BConcat, "CONCAT";
  BOr, "OR"; BAnd, "AND"; BXor, "XOR"; 
  BAdd, "ADD"; BSub, "SUB"; BMul, "MUL"; BDiv, "EDIV"; BLsr, "LSR"; BLsl, "LSL"]

let unop_dic = [UNot, "NOT"; UNeg, "NEG"; UAbs, "ABS"]

let get_product_tags ctx (t:typeT) =
  let name = match t with TApp(name, _)  -> name | _ -> unsound "bad product type" in
  let tags = match TypingContext.decl_of_name ctx name with
    | DProduct(_, type_params, fields) -> List.map fst fields 
    | d -> unsound ("Not a product type: "^TreePrint.string_of_type t^" = "^TreePrint.string_of_decl d) in
  tags

let get_sum_decl_cases ctx (t:typeT) =
  match t with
  | TApp(name, type_args)  ->
    begin match TypingContext.decl_of_name ctx name with
    | DSum(_, type_params, cases) ->
      List.map (fun (tag, t) -> tag, replace_tvars type_params type_args t) cases
    | d -> unsound ("Not a sum type: "^TreePrint.string_of_type t^" = "^TreePrint.string_of_decl d) 
    end
  | t -> unsound ("Not a sum type: "^TreePrint.string_of_type t) 

let rec compile_exprT ctx e =
  let c = compile_exprT ctx in
  let e_type = Typing.retrieve_type ctx e in
  print_endline("exprT->iExpr: "^TreePrint.string_of_expr e^"; typeT: "^TreePrint.string_of_type e_type); 
  let it = compile_typeT ctx e_type in

  match e with

  | ENat n | EInt n -> 
    let s = string_of_int n in 
    let s = if n>=0 then s else "("^s^")" in
    IELit(s), it

  | EString(s) -> IELit(sprintf "\"%s\"" s), it
  | ETez(n)    -> IELit(sprintf "\"%d.%02d\"" (n/100) (n mod 100)), it
  | ETime(s)   -> IELit(sprintf "\"%s\"" s), it
  | ESig(s)    -> IELit(sprintf "\"%s\"" s), it
  | EId(id)    -> IEId id, it

  | ELambda _ as e ->
    let rec get = function ELambda(a, _, b) -> let p, t = get b in a::p, t | t -> [], t in
    let param_names, body = get e in
    let param_types = match it with ITLambda(p, _) -> p | _ -> unsound "bad lambda type" in
    let typed_names = List.map2 (fun n t -> n, t) param_names param_types in
    IELambda(typed_names, c body), it

  | ELetIn(id, t, e0, e1) ->
    let te0 = c e0 and (ie1, it1) as te1 = c e1 in
    IELetIn(id, te0, te1), it1

  | EApp _ as e ->
    let rec get = function EApp(f, a) -> let f', args = get f in f', a::args | e -> e, [] in
    let f, args = get e in
    IEApp(c f, List.map c args), it

  | ETuple(list) -> IEProduct(List.map c list), it

  | ETupleGet(e_tuple, i) ->
    let t_tuple = Typing.retrieve_type ctx e_tuple in
    begin match t_tuple with
    | TTuple(list) -> IEProductGet(c e_tuple, i, List.length list), it
    | t -> unsound("Not a tuple type "^TreePrint.string_of_type t)
    end
  | EProduct(fields) ->
    let tags = get_product_tags ctx e_type in
    IEProduct (List.map (fun tag -> c (List.assoc tag fields)) tags), it

  | EProductGet(e_product, tag) ->
    let t_product = Typing.retrieve_type ctx e_product in
    let tags = get_product_tags ctx t_product in
    let tag2num = List.mapi (fun i t -> t, i) tags in
    IEProductGet(c e_product, List.assoc tag tag2num, List.length tags), it

  | ESum(tag, e) ->
    let tags = get_sum_decl_cases ctx e_type in
    let tag2num = List.mapi (fun i (tag, _) -> tag, i) tags in
    IESum(List.assoc tag tag2num, List.length tags, c e), it

  | ESumCase(e_test, e_cases) ->
    (* TODO d_cases are generic. *)
    let t_test = Typing.retrieve_type ctx e_test in
    let d_cases = get_sum_decl_cases ctx t_test in
    let rec f e_cases (d_tag, d_type) =
      let e_var, e_expr = List.assoc d_tag e_cases in
      e_var, compile_typeT ctx d_type, c e_expr
    in
    IESumCase(c e_test, List.map (f e_cases) d_cases), it

  | EBinOp(e0, op, e1) ->
    let (_, it0) as iet0 = c e0 and (_, it1) as iet1= c e1 in
    let lt = ITLambda([it0; it1], it) in
    (* TODO: IEId??? *)
    IEApp((IEId(List.assoc op binop_dic), lt), [iet0;  iet1]), it

  | EUnOp(op, e) ->
    let (_, it') as iet' = c e in
    let lt = ITLambda([it'], it) in
    IEApp((IEId(List.assoc op unop_dic), lt), [iet']), it

  | ETypeAnnot (e, t) -> c e
