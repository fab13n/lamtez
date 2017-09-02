open Utils
open Ast

let rec string_of_type t =
  let sot = string_of_type in
  match t with
  | TId(_, s) -> s
  | TFail -> "fail"
  | TLambda(_) as t ->
      let rec f = function TLambda(_, a, b) -> sot a^" -> "^f b | t -> sot t in "("^f t^")"
  | TTuple(_, list) -> "("^sep_list " * " sot list^")"
  | TApp(_, name, []) -> "'"^name
  | TApp(_, name, args) -> "("^name^" "^sep_list " " sot args^")"

let string_of_decl_pair (tag, t) = tag^": "^string_of_type t

let string_of_type_decl d =
  let left =
    match d with DSum(_, n, p, _) | DProduct(_, n, p, _) | DAlias(_, n, p, _) | DPrim(_, n, p) ->
    "type "^sep_list " " (fun x->x) (n::p)
  in
  let right =
    match d with
    | DSum(_, _, _, pairs) -> sep_list " + " string_of_decl_pair pairs^")"
    | DProduct(_, _, _, pairs) -> sep_list " * " string_of_decl_pair pairs^")"
    | DAlias(_, _, _, t) -> string_of_type t
    | DPrim(_, _, _) -> "primitive"
  in
  left^" = "^right

let string_of_store_decl (tag, t) =
  "@"^(String.uncapitalize_ascii tag)^": "^string_of_type t

let string_of_scheme (vars, t) =
  if vars=[] then string_of_type t
  else "∀ "^sep_list " " (fun x->x) vars^": "^string_of_type t

let string_of_binop = function
| BAdd -> "+" | BAnd -> "and" | BConcat -> "^" | BDiv -> "÷" | BEq -> "="
| BGe -> ">=" | BGt -> ">" | BLe -> "<=" | BLsl -> "<<" | BLsr -> ">>" | BLt -> "<"
| BMul -> "×" | BNeq -> "≠" | BOr -> "or" | BSub -> "-" | BXor -> "xor"

let string_of_unop = function UAbs -> "abs" | UNeg -> "-" | UNot -> "!"

let rec string_of_expr e =
  let soe = string_of_expr in
  match e with
  | EString(_, s) -> "\""^s^"\""
  | ENat(_, n) -> string_of_int n
  | EInt(_, n) -> (if n<=0 then "+" else "")^string_of_int n
  | ETez(_, n) -> Printf.sprintf "TZ%d.%02d" (n/100) (n mod 100)
  | ETime(_, s) -> s
  | ESig(_, s) -> "sig:"^s
  | EId(_, s) -> s
  | ELambda _ ->
    let rec f = function
      | ELambda(_, v, t, e) -> "("^v^": "^string_of_scheme t^") "^f e
      | e -> ": "^soe e in
    "(λ"^f e^")"
  | ELet(_, v, t, e0, e1) -> "let ("^v^": "^string_of_type t^") = "^soe e0^" in "^soe e1
  | EApp _ as e -> let rec f = function EApp(_, a, b) -> f a^" "^soe b | e -> soe e in "("^f e^")"
  | ETuple(_, list) -> "(" ^ sep_list ", " soe list ^ ")"
  | ETupleGet(_, e0, tag) -> soe e0 ^"."^string_of_int tag
  | EProduct(_, pairs) -> "{"^sep_list ", " (fun (tag, e) -> tag^" "^soe e) pairs^"}"
  | EProductGet(_, e0, tag) -> soe e0^"."^tag
  | EProductSet(_, e0, tag, e1) -> soe e0^"."^tag^" <- "^soe e1
  | EStoreSet(_, v, e0, e1) -> "@"^v^" <- "^soe e0^"; "^soe e1
  | ESum(_, tag, e0) -> tag^" "^soe e0
  | ESumCase(_, e0, triplets) -> "("^soe e0^" ? "^sep_list " | " (fun (tag, (v, e)) -> tag^": "^soe e) triplets^")"
  | EBinOp(_, e0, op, e1) -> "("^soe e0^" "^string_of_binop op^" "^soe e1^")"
  | EUnOp(_, op, e0) -> string_of_unop op^soe e0
  | ETypeAnnot(_, e0, t) -> "("^soe e0^": "^string_of_type t^")"

let string_of_contract (d, s, e) =
  sep_list "\n" string_of_type_decl d ^ "\n" ^
  sep_list "\n" string_of_store_decl s ^ "\n" ^
  string_of_expr e
