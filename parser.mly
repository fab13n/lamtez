%{ 
open Utils
open Ast

let loc startpos endpos = Some(startpos, endpos)

(* Parse applications: either set/map/list magic functions,
 * or a regular nesting of curryfied applications. *)
let app loc f args = 
  let collection k list = EColl(loc, k, args) in
  match f with
  | EId(_, "list") -> collection CList args
  | EId(_, "map")  -> collection CMap  args
  | EId(_, "set")  -> collection CSet  args
  | f              -> eapp (f::args)

let data_collection ?(loc=noloc) constr_name args =
  if not (List.mem constr_name ["list";"set";"map"]) then
    failwith "Not a data constructor";
  app loc (EId(noloc, constr_name)) args

%}
%token <int> NAT
%token <int> INT
%token <int> TEZ
%token <string> STRING
%token <string> TIMESTAMP
%token <string> SIGNATURE
%token <string> KEY
%token <string> ID
%token <string> TAG
%token LPAREN RPAREN
%token LAMBDA ARROW FORALL TYPE_ANNOT
%token COMMA COLON SEMICOLON LEFT_ARROW
%token <int> TUPLE_GET
%token <string> PRODUCT_GET
%token LBRACE RBRACE
%token BAR STORE
%token EQ NEQ LE LT GE GT CONCAT
%token OR AND XOR PLUS MINUS STAR DIV LSR LSL
%token TYPE LET IF CASE ELSE NOT
%token EOF

%start <Ast.contract> contract
%start <(string*Ast.expr) list> data_store
%start <Ast.expr> data_parameter

%right ARROW
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
| s=STRING {LString(loc $startpos $endpos, s)}
| s=KEY {LKey(loc $startpos $endpos, s)}

data:
| c=atomic_constant {ELit(loc $startpos $endpos, c)}
| LAMBDA p=parameter+ COLON e=expr {not_impl "lambda data"}
| LPAREN p=separated_list(COMMA, data) RPAREN {etuple ~loc:(loc $startpos $endpos) p}
| LPAREN constr=ID args=data* RPAREN {data_collection ~loc:(loc $startpos $endpos) constr args} 
| LBRACE p=separated_list(COMMA, data_product_pair) RBRACE {EProduct(loc $startpos $endpos, p);} 
| tag=TAG e=data? {match e with Some e -> ESum(loc $startpos $endpos, tag, e) | None -> ESum(loc $startpos $endpos, tag, eunit)}

data_product_pair: tag=TAG COLON? data=data {tag, data}

data_store_item: STORE i=tag_or_id EQ d=data {i, d}

data_store: x=data_store_item* EOF {x}
data_parameter: d=data EOF {d}

expr0:
| c=atomic_constant {ELit(loc $startpos $endpos, c)}
| s=ID {EId(loc $startpos $endpos, s)}
| LAMBDA p=parameter+ t=lambda_annot COLON e=expr_sequence {
  (* TODO put the lambda annot in outermost lambda *)
  let fold (pe, pt) acc = ELambda(loc $startpos $endpos, pe, pt, acc, ([], fresh_tvar())) in
  List.fold_right fold p e}
| LPAREN RPAREN {eunit_loc (loc $startpos $endpos)}
| LPAREN e=expr RPAREN {e}
| LPAREN e0=expr COMMA rest=separated_nonempty_list(COMMA, expr) RPAREN {
  let loc = loc $startpos $endpos in 
  etuple ~loc (e0::rest) }
| LPAREN e0=expr SEMICOLON rest=separated_nonempty_list(SEMICOLON, expr) RPAREN {
  let loc = loc $startpos $endpos in 
  esequence ~loc (e0::rest) }
| LPAREN CASE e=expr BAR c=separated_list(BAR, sum_case) RPAREN {ESumCase(loc $startpos $endpos, e, c)}
| LPAREN IF BAR? c=separated_list(BAR, if_case) RPAREN {let loc=loc $startpos $endpos in eif ~loc c}

| LBRACE p=separated_list(COMMA, product_pair) RBRACE {EProduct(loc $startpos $endpos, p);}
| LET p=parameter EQ e0=expr SEMICOLON e1=expr {ELet(loc $startpos $endpos, fst p, snd p, e0, e1)} (* TODO keep annotation if present *)
| e=expr0 tag=PRODUCT_GET {EProductGet(loc $startpos $endpos, e, tag)}
| e0=expr0 tag=PRODUCT_GET LEFT_ARROW e1=expr {EProductSet(loc $startpos $endpos, e0, tag, e1)}
| e=expr0 n=TUPLE_GET {ETupleGet(loc $startpos $endpos, e, n)}
| STORE s=tag_or_id  {EProductGet(loc $startpos $endpos, EId(loc $startpos $endpos, "@"), s)}
| STORE s=tag_or_id LEFT_ARROW e0=expr SEMICOLON e1=expr {EStoreSet(loc $startpos $endpos, s, e0, e1)}

lambda_annot: TYPE_ANNOT t=etype {[], t} | {[], fresh_tvar()}

expr:
| f=expr0 args=expr_arg* { app (loc $startpos $endpos) f args }
| tag=TAG e=expr0? {
  let loc=loc $startpos $endpos in 
  let arg = match e with Some e -> [e] | None -> [] in
  esum ~loc tag arg}
| e=expr TYPE_ANNOT t=etype {ETypeAnnot(loc $startpos $endpos, e, t)}
(* TODO can put infix operators in a separate rule if it's inlined, to preserve precedences. *)
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
| NOT   a=expr {EUnOp(loc $startpos $endpos, UNot, a)}

expr_arg:
| e=expr0 {e}
| tag=TAG {esum ~loc:(loc $startpos $endpos) tag []}
/* Why did I put this?! | LPAREN e=expr RPAREN {e} */

expr_sequence: l=separated_nonempty_list(SEMICOLON, expr) {
  match l with
  | [e] -> e 
  | _ -> let loc =loc $startpos $endpos in esequence ~loc l
}

tag_or_id: t=TAG {t} | v=ID {String.capitalize_ascii v}

sum_case: 
| tag=TAG COLON expr=expr_sequence {(tag, (fresh_var(), expr))}
| tag=TAG var=ID COLON? expr=expr_sequence {(tag, (var, expr))}

if_case:
| cond=expr COLON body=expr_sequence {(cond, body)}
| ELSE COLON? body=expr_sequence {(esum "True" [], body)}

product_pair: tag=TAG COLON? expr=expr {tag, expr}

parameter:
| id=ID {id, ([], fresh_tvar ~prefix:id ())}
| LPAREN id=ID TYPE_ANNOT t=scheme RPAREN {(id, t)}
(* TODO support for irrefutable pattern (products and tuples),
 * by generating an ELet(...) functor to apply to function/letin body. *)
