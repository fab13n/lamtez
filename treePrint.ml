open Tree

let sep_list separator f = function
| [] -> ""
| a :: b -> List.fold_left (fun acc e -> acc^separator^f e) (f a) b

let rec string_of_type t = 
  let sot = string_of_type in
  match t with
  | TId s -> s
  | TFail -> "fail"
  | TLambda(_) as t ->
      let rec f = function TLambda(a, b) -> sot a^" -> "^f b | t -> sot t in "("^f t^")"
  | TTuple(list) -> "("^sep_list " * " sot list^")"
  | TApp(name, []) -> "'"^name
  | TApp(name, args) -> "("^name^" "^sep_list " " sot args^")"

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

let rec string_of_expr e = 
  let soe = string_of_expr in
  match e with 
  | EString s -> "\""^s^"\""
  | ENat n -> string_of_int n
  | EInt n -> (if n<=0 then "+" else "")^string_of_int n
  | ETez n -> Printf.sprintf "TZ%d.%02d" (n/100) (n mod 100)
  | ETime s -> s
  | ESig s -> "sig:"^s
  | EId s -> s
  | ELambda(_) ->
    let rec f = function 
      | ELambda(v, t, e) -> "("^v^": "^string_of_scheme t^") "^f e
      | e -> ": "^soe e in
    "(λ"^f e^")"
  | ELetIn(v, t, e0, e1) -> "let ("^v^": "^string_of_type t^") = "^soe e0^" in "^soe e1
  | EApp(_) as e -> let rec f = function EApp(a, b) -> f a^" "^soe b | e -> soe e in "("^f e^")"
  | ETuple(list) -> "(" ^ sep_list ", " soe list ^ ")"
  | ETupleGet(e0, tag) -> soe e0 ^"."^string_of_int tag
  | EProduct(pairs) -> "{"^sep_list ", " (fun (tag, e) -> tag^" "^soe e) pairs^"}"
  | EProductGet(e0, tag) -> soe e0^"."^tag
  | EProductSet(e0, tag, e1) -> soe e0^"."^tag^" <- "^soe e1
  | ESum(tag, e0) -> tag^" "^soe e0
  | ESumCase(e0, triplets) -> "("^soe e0^" ? "^sep_list " | " (fun (tag, (v, e)) -> tag^": "^soe e) triplets^")"
  | EBinOp(e0, op, e1) -> "("^soe e0^" "^string_of_binop op^" "^soe e1^")"
  | EUnOp(op, e0) -> string_of_unop op^soe e0
  | ETypeAnnot(e0, t) -> "("^soe e0^": "^string_of_type t^")"

let string_of_program (d, e) =
  sep_list "\n" string_of_decl d ^ "\n" ^
  string_of_expr e

