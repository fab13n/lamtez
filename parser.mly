%{ 
open Utils
open Ast

let noloc = None
let loc startpos endpos = Some(startpos, endpos)
let loc2 a b = match a, b with
  | Some(a, _), Some(_, b) | Some(a, b), None | None, Some(a, b) -> Some(a, b)
  | None, None -> None
let loc2e a b = loc2 (loc_of_expr a) (loc_of_expr b)

let eid id = EId(noloc, id)
let esum id args =
  let loc, arg = match args with
  | [] -> noloc, eid "unit"
  | [e] -> loc_of_expr e, e
  | list ->
    let loc = loc2e (List.hd list) (List.hd (List.rev list)) in
    loc, ETuple(loc, list) in
  ESum(loc, id, arg) 

let eapp = function [] -> assert false | f :: args ->
  let l1 = loc_of_expr f in
  let fold acc arg =
    let loc = loc2 l1 (loc_of_expr arg) in
    EApp(loc, acc, arg) in
  List.fold_left fold f args

(* Parse applications: either set/map/list magic functions,
 * or a regular nesting of curryfied applications. *)
let app loc f args = 
  let collection k list = EColl(loc, k, args) in
  match f with
  | EId(_, "list") -> collection CList args
  | EId(_, "map")  -> collection CMap  args
  | EId(_, "set")  -> collection CSet  args
  | f              -> eapp (f::args)
%}
%token <int> NAT
%token <int> INT
%token <int> TEZ
%token <string> STRING
%token <string> TIMESTAMP
%token <string> SIGNATURE
%token <string> ID
%token <string> TAG
%token LPAREN RPAREN
%token LAMBDA ARROW FORALL TYPE_ANNOT
%token COMMA COLON SEMICOLON LEFT_ARROW
%token <int> TUPLE_GET
%token <string> PRODUCT_GET
%token LBRACE RBRACE
%token CASE BAR STORE
%token EQ NEQ LE LT GE GT CONCAT
%token OR AND XOR PLUS MINUS STAR DIV LSR LSL
%token TYPE LET
%token EOF
%start <Ast.contract> contract

%right ARROW
%nonassoc CASE
%left AND OR XOR
%nonassoc EQ NEQ
%nonassoc LE LT GE GT
%nonassoc LSR LSL
%left PLUS MINUS
%left STAR DIV
%%

contract: d=etype_decl* s=store_decl* e=expr EOF {d, s, e}

etype:
| a=etype ARROW b=etype {TLambda(loc $startpos $endpos, a, b)}
| id=ID args=etype_arg* {if args=[] then TId(loc $startpos $endpos, id) else TApp(loc $startpos $endpos, id, args)}
| t=etype_tuple {t}

etype_arg: id=ID {TId(loc $startpos $endpos, id)} | t=etype_tuple {t}
etype_tuple: LPAREN types=separated_nonempty_list(STAR, etype) RPAREN {match types with [t]->t | _ ->TTuple(loc $startpos $endpos, types)}

scheme:
| FORALL vars=ID* COLON t=etype {vars, t}
| t=etype {[], t}

etype_decl: TYPE name=ID params=ID* EQ r=composite_decl_rhs {r name params}

composite_decl_rhs:
| t=etype {fun name params -> if name="primitive" && params=[] then DPrim(loc $startpos $endpos, name, params) else DAlias(loc $startpos $endpos, name, params, t)}
| p0=composite_decl_pair STAR pp=separated_list(STAR, composite_decl_pair) {fun name params -> DProduct(loc $startpos $endpos, name, params, p0::pp)}
| p0=composite_decl_pair PLUS pp=separated_list(PLUS, composite_decl_pair) {fun name params -> DSum(loc $startpos $endpos, name, params, p0::pp)}

composite_decl_pair: tag=TAG COLON? t=etype {(tag, t)}

store_decl:
| STORE name=tag_or_id TYPE_ANNOT t=etype EQ v=data SEMICOLON? {(name, t, Some v)}
| STORE name=tag_or_id TYPE_ANNOT t=etype SEMICOLON? {(name, t, None)}

atomic_constant:
| n=INT {LInt(loc $startpos $endpos, n)}
| n=NAT {LNat(loc $startpos $endpos, n)}
| n=TEZ {LTez(loc $startpos $endpos, n)}
| n=TIMESTAMP {LTime(loc $startpos $endpos, n)}
| s=SIGNATURE {LSig(loc $startpos $endpos, s)}
| s=STRING {LString(loc $startpos $endpos, s)} (* TODO Unescape *)
(* TODO support crypto keys *)

data:
| c=atomic_constant {ELit(loc $startpos $endpos, c)}
| LAMBDA p=parameter+ COLON e=expr {not_impl "lambda data"}
| LPAREN p=separated_list(COMMA, data) RPAREN {match p with [] -> not_impl "unit data" | [e] -> e | p -> ETuple(loc $startpos $endpos, p)}
| LBRACE p=separated_list(COMMA, data_product_pair) RBRACE {EProduct(loc $startpos $endpos, p);}
| tag=TAG e=data? {match e with Some e -> ESum(loc $startpos $endpos, tag, e) | None -> ESum(loc $startpos $endpos, tag, not_impl "data unit")}

data_product_pair: tag=TAG COLON? data=data {tag, data}

expr0:
| c=atomic_constant {ELit(loc $startpos $endpos, c)}
| s=ID {EId(loc $startpos $endpos, s)}
| LAMBDA p=parameter+ COLON e=expr {List.fold_right (fun (pe, pt) acc -> ELambda(loc $startpos $endpos, pe, pt, acc)) p e}
| LPAREN p=separated_list(COMMA, expr) RPAREN {match p with [] -> EId(loc $startpos $endpos, "unit") | [e] -> e | p -> ETuple(loc $startpos $endpos, p)}
| LBRACE p=separated_list(COMMA, product_pair) RBRACE {EProduct(loc $startpos $endpos, p);}
| LET p=parameter EQ e0=expr SEMICOLON e1=expr {ELet(loc $startpos $endpos, fst p, snd (snd p), e0, e1)} (* TODO keep annotation if present *)
| e=expr0 tag=PRODUCT_GET {EProductGet(loc $startpos $endpos, e, tag)}
| e0=expr0 tag=PRODUCT_GET LEFT_ARROW e1=expr {EProductSet(loc $startpos $endpos, e0, tag, e1)}
| e=expr0 n=TUPLE_GET {ETupleGet(loc $startpos $endpos, e, n)}
| STORE s=tag_or_id  {EProductGet(loc $startpos $endpos, EId(loc $startpos $endpos, "@"), s)}
| STORE s=tag_or_id LEFT_ARROW e0=expr SEMICOLON e1=expr {EStoreSet(loc $startpos $endpos, s, e0, e1)}

expr:
| f=expr0 args=arg* { app (loc $startpos $endpos) f args }
| tag=TAG e=expr0? {match e with Some e -> ESum(loc $startpos $endpos, tag, e) | None -> ESum(loc $startpos $endpos, tag, EId(loc $startpos $endpos, "unit"))}
| e=expr CASE BAR? c=separated_list(BAR, sum_case) {ESumCase(loc $startpos $endpos, e, c)}
| e=expr TYPE_ANNOT t=etype {ETypeAnnot(loc $startpos $endpos, e, t)}
| a=expr EQ  b=expr {EBinOp(loc $startpos $endpos, a, BEq, b)}
| a=expr NEQ b=expr {EBinOp(loc $startpos $endpos, a, BNeq, b)}
| a=expr LE  b=expr {EBinOp(loc $startpos $endpos, a, BLe, b)}
| a=expr LT  b=expr {EBinOp(loc $startpos $endpos, a, BLt, b)}
| a=expr GE  b=expr {EBinOp(loc $startpos $endpos, a, BGe, b)}
| a=expr GT  b=expr {EBinOp(loc $startpos $endpos, a, BGt, b)}
| a=expr CONCAT b=expr {EBinOp(loc $startpos $endpos, a, BConcat, b)}
| a=expr OR b=expr {EBinOp(loc $startpos $endpos, a, BOr, b)}
| a=expr AND b=expr {EBinOp(loc $startpos $endpos, a, BAnd, b)}
| a=expr XOR b=expr {EBinOp(loc $startpos $endpos, a, BXor, b)}
| a=expr PLUS b=expr {EBinOp(loc $startpos $endpos, a, BAdd, b)}
| a=expr MINUS b=expr {EBinOp(loc $startpos $endpos, a, BSub, b)}
| a=expr STAR b=expr {EBinOp(loc $startpos $endpos, a, BMul, b)}
| a=expr DIV b=expr {EBinOp(loc $startpos $endpos, a, BDiv, b)}
| a=expr LSR b=expr {EBinOp(loc $startpos $endpos, a, BLsr, b)}
| a=expr LSL b=expr {EBinOp(loc $startpos $endpos, a, BLsl, b)}
| MINUS a=expr {EUnOp(loc $startpos $endpos, UNeg, a)}

arg:
| e=expr0 {e}
| tag=TAG {ESum(loc $startpos $endpos, tag, EId(loc $startpos $endpos, "unit"))}
| LPAREN e=expr RPAREN {e}

tag_or_id: t=TAG {t} | v=ID {String.capitalize_ascii v}

sum_case: 
| tag=TAG COLON expr=expr {(tag, (fresh_var(), expr))}
| tag=TAG var=ID COLON? expr=expr {(tag, (var, expr))}

product_pair: tag=TAG COLON? expr=expr {tag, expr}

parameter:
| id=ID {id, ([], fresh_tvar ~prefix:id ())}
| LPAREN id=ID TYPE_ANNOT t=scheme RPAREN {(id, t)}
(* TODO support for irrefutable pattern (products and tuples),
 * by generating a LetIn(...) functor to apply to function/letin body. *)
