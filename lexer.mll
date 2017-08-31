{
  (* Header *)
  open Lexing
  open Parser

  exception Lexing_error of string

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
let sig = "sig:" b58+
let string = '"' [^'"']* '"' (* TODO handle escaped quotes and \r\n *)

(* λ == \;  Λ == /\; ∀ == \/; → == -> *)

rule read = parse
| white {read lexbuf}
| '#' [^'\r' '\n']* ['\r' '\n'] {read lexbuf}
| "type" {TYPE}
| "let" {LET}
| "in" {IN}
| "<-" {LEFT_ARROW}
| "or" {OR} | "and" {AND} | "xor" {XOR}
| "\\/" {FORALL}
| string {STRING(trim lexbuf 1 1)}
| ('+'|'-') num {INT(int_of_string (Lexing.lexeme lexbuf))}
| num {NAT(int_of_string (Lexing.lexeme lexbuf))}
| tz_cents {TEZ(int_of_tz_cents(Lexing.lexeme lexbuf))}
| tz_int {TEZ(int_of_tz_int(Lexing.lexeme lexbuf))}
| time {TIMESTAMP(Lexing.lexeme lexbuf)}
| sig {SIGNATURE(trim lexbuf 4 0)}
| id {ID(Lexing.lexeme lexbuf)}
| tag {TAG(Lexing.lexeme lexbuf)}
| '(' {LPAREN} | ')' {RPAREN} | '\\' {LAMBDA} | "->" {ARROW}
| ',' {COMMA} | ':' {COLON} | '{' {LBRACE} | '}' {RBRACE} | '?' {CASE} | '|' {BAR}
| '=' {EQ} | "!=" {NEQ} | '<' {LT} | "<=" {LE} | '>' {GT} | ">=" {GE} | '^' {CONCAT}
| '+' {PLUS} | '-' {MINUS} | '*' {STAR} | '/' {DIV} | ">>" {LSR} | "<<" {LSL}
| '.' d+ {TUPLE_GET(int_of_string (trim lexbuf 1 0))}
| '.' tag {PRODUCT_GET(trim lexbuf 1 0)}
| eof {EOF}


{
  (* Trailer *)
}