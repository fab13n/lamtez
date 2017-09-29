{
  (* Header *)
  open Lexing
  open Parser

  exception Lexing_error of Lexing.position

  (* Remove `a` characters on the left and `b` characters on the right of the next lexeme in `lexbuf`. *)
  let trim lexbuf a b =
    let s = Lexing.lexeme lexbuf in
    String.sub s a (String.length s - a - b)

  let int_of_tz_cents s =
    let l = String.length s in
    let ints  = String.sub s 2 (l-5) in
    let cents = String.sub s (l-2) 2 in
    100 * int_of_string ints + int_of_string cents

  let int_of_tz_int s =
    let l = String.length s in
    let ints = String.sub s 2 (l-2) in
    100 * int_of_string ints

}

let white = ['\n' '\r' '\t' ' ']+
let d = ['0'-'9']
let id = ['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '-' '_' ]*
let tag = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '-' '_' ]*
let num = '-'? d+
let tz_int = "tz" d+
let tz_cents = "tz" d* '.' d d
let timezone = 'Z' | ('+' d d? (':' d d)?)
let time = d d d d '-' d d '-' d d 'T' d d ':' d d ':' d d timezone
let b58 = ['1'-'9' 'A'-'H' 'J'-'N' 'P'-'Z' 'a'-'k' 'm'-'z']
let hex = ['0'-'9' 'a'-'f']
let sig = "sig:" hex+
let key = "tz1" b58+

rule read = parse
| [' ' '\t']+ {read lexbuf}
| '\r' '\n'? | '\n' '\r' ? {Lexing.new_line lexbuf; read lexbuf}
| '#' [^'\r' '\n']* ['\r' '\n'] {Lexing.new_line lexbuf; read lexbuf}
| "type" {TYPE}
| "let" {LET}
| "if" {IF}
| "case" {CASE}
| "else" {ELSE}
| "end" {END}
| ';' {SEMICOLON}
| "<-" {LEFT_ARROW}
| "\\/" {FORALL}
| '@' {STORE}
| "::" {TYPE_ANNOT}
| '"' { let buffer = Buffer.create 1 in STRING (string_cont buffer lexbuf) }
| ('+'|'-') num {INT(int_of_string (Lexing.lexeme lexbuf))}
| num {NAT(int_of_string (Lexing.lexeme lexbuf))}
| tz_cents {TEZ(int_of_tz_cents(Lexing.lexeme lexbuf))}
| tz_int {TEZ(int_of_tz_int(Lexing.lexeme lexbuf))}
| time {TIMESTAMP(Lexing.lexeme lexbuf)}
| sig {SIGNATURE(trim lexbuf 4 0)}
| key {KEY(Lexing.lexeme lexbuf)}

| '.' d+ {TUPLE_GET(int_of_string (trim lexbuf 1 0))}
| '.' tag {PRODUCT_GET(trim lexbuf 1 0)}

| '(' {LPAREN} | ')' {RPAREN} 
| '\\' {LAMBDA} | "fun" {LAMBDA}
| "->" {ARROW} | "=>" {DOUBLE_ARROW}
| ',' {COMMA} | ':' {COLON} | '{' {LBRACE} | '}' {RBRACE} | '|' {BAR}
| '=' {EQ} | "!=" {NEQ} | '<' {LT} | "<=" {LE} | '>' {GT} | ">=" {GE} | '^' {CONCAT}
| '+' {PLUS} | '-' {MINUS} | '*' {STAR} | '/' {DIV} | ">>" {LSR} | "<<" {LSL}
| "||" {OR} | "&&" {AND} | "^^" {XOR} | "not" {NOT}

| id {ID(Lexing.lexeme lexbuf)} (* must be after alhabetic keywords *)
| tag {TAG(Lexing.lexeme lexbuf)}

| eof {EOF}

| _ { raise(Lexing_error(Lexing.lexeme_start_p lexbuf))}

and string_cont buffer = parse
| '"' { Buffer.contents buffer }
| '\\' (_ as k) { Buffer.add_char buffer '\\'; 
                  Buffer.add_char buffer k;
                  string_cont buffer lexbuf }
| '\n' { failwith "Unterminated string" }
| eof { raise End_of_file }
| _ as k { Buffer.add_char buffer k; string_cont buffer lexbuf }

 (* unescaped version; I'd rather store string escaped, as I'll pass them
  * escaped to the Michelson generator.
 and  string_cont buffer = parse
 | '"' { Buffer.contents buffer }
 | "\\t" { Buffer.add_char buffer '\t'; string_cont buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; string_cont buffer lexbuf }
 | '\\' '"' { Buffer.add_char buffer '"'; string_cont buffer lexbuf }
 | '\\' '\\' { Buffer.add_char buffer '\\'; string_cont buffer lexbuf }
 | eof { raise End_of_file }
 | _ as char { Buffer.add_char buffer char; string_cont buffer lexbuf }
*)

{
  (* Trailer *)
}