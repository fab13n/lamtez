%{ 
open Ast
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
%start <Ast.contract> main

%right ARROW
%nonassoc CASE
%left AND OR XOR
%nonassoc EQ NEQ
%nonassoc LE LT GE GT
%nonassoc LSR LSL
%left PLUS MINUS
%left STAR DIV
%%

main: d=type_decl* s=store_decl* e=expr EOF {d, s, e}


typeT:
| a=typeT ARROW b=typeT {TLambda(a, b)}
| id=ID args=type_arg* {if args=[] then TId(id) else TApp(id, args)}
| t=type_tuple {t}

type_arg: id=ID {TId(id)} | t=type_tuple {t}
type_tuple: LPAREN types=separated_nonempty_list(STAR, typeT) RPAREN {match types with [t]->t | _ ->TTuple(types)}

schemeT:
| FORALL vars=ID* COLON t=typeT {vars, t}
| t=typeT {[], t}

type_decl: TYPE name=ID params=ID* EQ r=composite_decl_rhs {r name params}

store_decl:
| STORE name=tag_or_id TYPE_ANNOT t=typeT {(name, t)}

composite_decl_rhs:
| t=typeT {fun name params -> if name="primitive" && params=[] then DPrim(name, params) else DAlias(name, params, t)}
| p0=composite_decl_pair STAR pp=separated_list(STAR, composite_decl_pair) {fun name params -> DProduct(name, params, p0::pp)}
| p0=composite_decl_pair PLUS pp=separated_list(PLUS, composite_decl_pair) {fun name params -> DSum(name, params, p0::pp)}

composite_decl_pair: tag=TAG COLON? t=typeT {(tag, t)}

expr0:
| n=INT {EInt n}
| n=NAT {ENat n}
| n=TEZ {ETez n}
| n=TIMESTAMP {ETime n}
| s=SIGNATURE {ESig s}
| s=STRING {EString s} (* TODO Unescape *)
(* TODO support crypto keys *)
| s=ID {EId s}
| LAMBDA p=parameter+ COLON e=expr {List.fold_right (fun (pe, pt) acc -> ELambda(pe, pt, acc)) p e}
| LPAREN p=separated_list(COMMA, expr) RPAREN {match p with [] -> EId "unit" | [e] -> e | p -> ETuple(p)}
| LBRACE p=separated_list(COMMA, product_pair) RBRACE {EProduct(p);}
| LET p=parameter EQ e0=expr SEMICOLON e1=expr {ELetIn(fst p, snd (snd p), e0, e1)} (* TODO keep annotation if present *)
| e=expr0 tag=PRODUCT_GET {EProductGet(e, tag)}
| e0=expr0 tag=PRODUCT_GET LEFT_ARROW e1=expr {EProductSet(e0, tag, e1)}
| e=expr0 n=TUPLE_GET {ETupleGet(e, n)}
| STORE s=tag_or_id  {EProductGet(EId("@"), s)}
| STORE s=tag_or_id LEFT_ARROW e0=expr SEMICOLON e1=expr {EStoreSet(s, e0, e1)}

expr:
| f=expr0 args=arg* {List.fold_left (fun acc arg -> EApp(acc, arg)) f args}
| tag=TAG e=expr0? {match e with Some e -> ESum(tag, e) | None -> ESum(tag, EId "unit")}
| e=expr CASE BAR? c=separated_list(BAR, sum_case) {ESumCase(e, c)}
| e=expr TYPE_ANNOT t=typeT {ETypeAnnot(e, t)}
| a=expr EQ  b=expr {EBinOp(a, BEq, b)}
| a=expr NEQ b=expr {EBinOp(a, BNeq, b)}
| a=expr LE  b=expr {EBinOp(a, BLe, b)}
| a=expr LT  b=expr {EBinOp(a, BLt, b)}
| a=expr GE  b=expr {EBinOp(a, BGe, b)}
| a=expr GT  b=expr {EBinOp(a, BGt, b)}
| a=expr CONCAT b=expr {EBinOp(a, BConcat, b)}
| a=expr OR b=expr {EBinOp(a, BOr, b)}
| a=expr AND b=expr {EBinOp(a, BAnd, b)}
| a=expr XOR b=expr {EBinOp(a, BXor, b)}
| a=expr PLUS b=expr {EBinOp(a, BAdd, b)}
| a=expr MINUS b=expr {EBinOp(a, BSub, b)}
| a=expr STAR b=expr {EBinOp(a, BMul, b)}
| a=expr DIV b=expr {EBinOp(a, BDiv, b)}
| a=expr LSR b=expr {EBinOp(a, BLsr, b)}
| a=expr LSL b=expr {EBinOp(a, BLsl, b)}
| MINUS a=expr {EUnOp(UNeg, a)}

arg:
| e=expr0 {e}
| tag=TAG {ESum(tag, EId "unit")}
| LPAREN e=expr RPAREN {e}

tag_or_id: t=TAG {t} | v=ID {String.capitalize_ascii v}

sum_case: 
| tag=TAG COLON expr=expr {(tag, (fresh_var(), expr))}
| tag=TAG var=ID COLON? expr=expr {(tag, (var, expr))}

product_pair: tag=TAG COLON? expr=expr {tag, expr}

parameter:
| id=ID {id, ([], fresh_tvar())}
| LPAREN id=ID TYPE_ANNOT t=schemeT RPAREN {(id, t)}
(* TODO support for irrefutable pattern (products and tuples),
 * by generating a LetIn(...) functor to apply to function/letin body. *)
