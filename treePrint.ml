open Tree

let sep_list separator f = function
| [] -> ""
| a :: b -> List.fold_left (fun acc e -> acc^separator^f e) (f a) b

let rec string_of_type t = match t with
| TId s -> s
| TFail -> "fail"
| TLambda(a, b) -> "("^string_of_type a^" → "^string_of_type b^")"
| TTuple(list) -> "("^sep_list "*" string_of_type list^")"
| TApp(name, []) -> name
| TApp(name, args) -> "("^name^" "^sep_list " " string_of_type args^")"

let string_of_decl_pair (tag, t) = tag^": "^string_of_type t

let string_of_decl d = 
  let left =
    match d with DSum(n, p, _) | DProduct(n, p, _) | DAlias(n, p, _) | DPrim(n, p) -> 
    "type "^sep_list " " (fun x->x) (n::p)
  in
  let right =
    match d with
    | DSum(_, _, pairs) -> sep_list " + " string_of_decl_pair pairs^")"
    | DProduct(_, _, pairs) -> sep_list " * " string_of_decl_pair pairs^")"
    | DAlias(_, _, t) -> string_of_type t
    | DPrim(_, _) -> "primitive"
  in
  left^" = "^right

let string_of_scheme (vars, t) =
  if vars=[] then string_of_type t
  else "∀ "^sep_list " " (fun x->x) vars^": "^string_of_type t

let string_of_binop = function
| BAdd -> "+" | BAnd -> "and" | BConcat -> "^" | BDiv -> "÷" | BEq -> "=" 
| BGe -> ">=" | BGt -> ">" | BLe -> "<=" | BLsl -> "<<" | BLsr -> ">>" | BLt -> "<"
| BMul -> "×" | BNeq -> "≠" | BOr -> "or" | BSub -> "-" | BXor -> "xor"

let string_of_unop = function UAbs -> "abs" | UNeg -> "-" | UNot -> "!"

let rec string_of_expr e = match e with 
| EString s -> "\""^s^"\""
| ENum n -> string_of_int n
| ETez n -> Printf.sprintf "TZ%d.%02d" (n/100) (n mod 100)
| ETime s -> s
| ESig s -> "sig:"^s
| EId s -> s
| ELambda(v, t, e) -> "λ("^v^": "^string_of_scheme t^"): "^string_of_expr e
| ELetIn(v, e0, e1) -> "let "^v^" = "^string_of_expr e0^" in "^string_of_expr e1
| EApp(a, b) -> "("^string_of_expr a^" "^string_of_expr b^")"
| ETuple(list) -> "(" ^ sep_list ", " string_of_expr list ^ ")"
| ETupleGet(e, tag) -> string_of_expr e ^"."^string_of_int tag
| EProduct(pairs) -> "{"^sep_list ", " (fun (tag, e) -> tag^" "^string_of_expr e) pairs^"}"
| EProductGet(t, tag) -> string_of_expr t^"."^tag
| ESum(tag, t) -> tag^" "^string_of_expr t
| ESumCase(t, triplets) -> "("^string_of_expr t^" ? "^sep_list " | " (fun (tag, (v, e)) -> tag^": "^string_of_expr e) triplets^")"
| EBinOp(a, op, b) -> "("^string_of_expr a^" "^string_of_binop op^" "^string_of_expr b^")"
| EUnOp(op, a) -> string_of_unop op^string_of_expr a
| ETypeAnnot(e, t) -> "("^string_of_expr e^": "^string_of_type t^")"

let string_of_program (d, e) =
  sep_list "\n" string_of_decl d ^ "\n" ^
  string_of_expr e

