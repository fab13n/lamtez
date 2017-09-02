%{ 
open Ast
let noloc = None
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
| a=etype ARROW b=etype {TLambda(noloc, a, b)}
| id=ID args=etype_arg* {if args=[] then TId(noloc, id) else TApp(noloc, id, args)}
| t=etype_tuple {t}

etype_arg: id=ID {TId(noloc, id)} | t=etype_tuple {t}
etype_tuple: LPAREN types=separated_nonempty_list(STAR, etype) RPAREN {match types with [t]->t | _ ->TTuple(noloc, types)}

scheme:
| FORALL vars=ID* COLON t=etype {vars, t}
| t=etype {[], t}

etype_decl: TYPE name=ID params=ID* EQ r=composite_decl_rhs {r name params}

composite_decl_rhs:
| t=etype {fun name params -> if name="primitive" && params=[] then DPrim(noloc, name, params) else DAlias(noloc, name, params, t)}
| p0=composite_decl_pair STAR pp=separated_list(STAR, composite_decl_pair) {fun name params -> DProduct(noloc, name, params, p0::pp)}
| p0=composite_decl_pair PLUS pp=separated_list(PLUS, composite_decl_pair) {fun name params -> DSum(noloc, name, params, p0::pp)}

composite_decl_pair: tag=TAG COLON? t=etype {(tag, t)}

store_decl:
| STORE name=tag_or_id TYPE_ANNOT t=etype {(name, t)}

expr0:
| n=INT {EInt(noloc, n)}
| n=NAT {ENat(noloc, n)}
| n=TEZ {ETez(noloc, n)}
| n=TIMESTAMP {ETime(noloc, n)}
| s=SIGNATURE {ESig(noloc, s)}
| s=STRING {EString(noloc, s)} (* TODO Unescape *)
(* TODO support crypto keys *)
| s=ID {EId(noloc, s)}
| LAMBDA p=parameter+ COLON e=expr {List.fold_right (fun (pe, pt) acc -> ELambda(noloc, pe, pt, acc)) p e}
| LPAREN p=separated_list(COMMA, expr) RPAREN {match p with [] -> EId(noloc, "unit") | [e] -> e | p -> ETuple(noloc, p)}
| LBRACE p=separated_list(COMMA, product_pair) RBRACE {EProduct(noloc, p);}
| LET p=parameter EQ e0=expr SEMICOLON e1=expr {ELet(noloc, fst p, snd (snd p), e0, e1)} (* TODO keep annotation if present *)
| e=expr0 tag=PRODUCT_GET {EProductGet(noloc, e, tag)}
| e0=expr0 tag=PRODUCT_GET LEFT_ARROW e1=expr {EProductSet(noloc, e0, tag, e1)}
| e=expr0 n=TUPLE_GET {ETupleGet(noloc, e, n)}
| STORE s=tag_or_id  {EProductGet(noloc, EId(noloc, "@"), s)}
| STORE s=tag_or_id LEFT_ARROW e0=expr SEMICOLON e1=expr {EStoreSet(noloc, s, e0, e1)}

expr:
| f=expr0 args=arg* {List.fold_left (fun acc arg -> EApp(noloc, acc, arg)) f args}
| tag=TAG e=expr0? {match e with Some e -> ESum(noloc, tag, e) | None -> ESum(noloc, tag, EId(noloc, "unit"))}
| e=expr CASE BAR? c=separated_list(BAR, sum_case) {ESumCase(noloc, e, c)}
| e=expr TYPE_ANNOT t=etype {ETypeAnnot(noloc, e, t)}
| a=expr EQ  b=expr {EBinOp(noloc, a, BEq, b)}
| a=expr NEQ b=expr {EBinOp(noloc, a, BNeq, b)}
| a=expr LE  b=expr {EBinOp(noloc, a, BLe, b)}
| a=expr LT  b=expr {EBinOp(noloc, a, BLt, b)}
| a=expr GE  b=expr {EBinOp(noloc, a, BGe, b)}
| a=expr GT  b=expr {EBinOp(noloc, a, BGt, b)}
| a=expr CONCAT b=expr {EBinOp(noloc, a, BConcat, b)}
| a=expr OR b=expr {EBinOp(noloc, a, BOr, b)}
| a=expr AND b=expr {EBinOp(noloc, a, BAnd, b)}
| a=expr XOR b=expr {EBinOp(noloc, a, BXor, b)}
| a=expr PLUS b=expr {EBinOp(noloc, a, BAdd, b)}
| a=expr MINUS b=expr {EBinOp(noloc, a, BSub, b)}
| a=expr STAR b=expr {EBinOp(noloc, a, BMul, b)}
| a=expr DIV b=expr {EBinOp(noloc, a, BDiv, b)}
| a=expr LSR b=expr {EBinOp(noloc, a, BLsr, b)}
| a=expr LSL b=expr {EBinOp(noloc, a, BLsl, b)}
| MINUS a=expr {EUnOp(noloc, UNeg, a)}

arg:
| e=expr0 {e}
| tag=TAG {ESum(noloc, tag, EId(noloc, "unit"))}
| LPAREN e=expr RPAREN {e}

tag_or_id: t=TAG {t} | v=ID {String.capitalize_ascii v}

sum_case: 
| tag=TAG COLON expr=expr {(tag, (fresh_var(), expr))}
| tag=TAG var=ID COLON? expr=expr {(tag, (var, expr))}

product_pair: tag=TAG COLON? expr=expr {tag, expr}

parameter:
| id=ID {id, ([], fresh_tvar())}
| LPAREN id=ID TYPE_ANNOT t=scheme RPAREN {(id, t)}
(* TODO support for irrefutable pattern (products and tuples),
 * by generating a LetIn(...) functor to apply to function/letin body. *)
