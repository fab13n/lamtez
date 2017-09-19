open Printf
open Utils
open Ast

let is_fresh_tvar = function TId(_, x) -> String.contains x '%' | _ -> false

let rec string_of_type t =
  let sot = string_of_type in
  match t with
  | TId(_, s) -> s
  | TFail -> "fail"
  | TLambda _ as t ->
      let rec f = function 
        | TLambda(_, a, b) -> sprintf "%s -> %s" (sot a) (f b)
        | t -> sot t in
      "("^f t^")"
  | TTuple(_, []) -> "unit"
  | TTuple(_, list) -> "("^sep_list " * " sot list^")"    
  | TApp(_, name, []) -> "'"^name
  | TApp(_, name, args) -> "('"^name^" "^sep_list " " sot args^")"

let string_of_decl_pair (tag, t) = tag^": "^string_of_type t

let string_of_type_decl d =
  let left =
    match d with DSum(_, n, p, _) | DProduct(_, n, p, _) | DAlias(_, n, p, _) | DPrim(_, n, p) ->
    "type "^sep_list " " (fun x->x) (n::p)
  in
  let right =
    match d with
    | DSum(_, _, _, pairs) -> "("^sep_list " + " string_of_decl_pair pairs^")"
    | DProduct(_, _, _, pairs) -> "("^sep_list " * " string_of_decl_pair pairs^")"
    | DAlias(_, _, _, t) -> string_of_type t
    | DPrim(_, _, _) -> "primitive"
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

let rec string_of_lit = function
  | LString(_, s) -> "\""^s^"\""
  | LNat(_, n) -> string_of_int n
  | LInt(_, n) -> (if n<=0 then "+" else "")^string_of_int n
  | LTez(_, n) -> Printf.sprintf "tz%d.%02d" (n/100) (n mod 100)
  | LTime(_, s) -> s
  | LSig(_, s) -> "sig:"^s
  | LKey(_, s) -> s

let string_of_collection_kind = function
  | CSet -> "set" | CList -> "list" | CMap -> "map" 

let rec string_of_pattern = function
  | PAny -> "_"
  | PId id -> id
  | PTuple list -> "("^sep_list ", " string_of_pattern list^")"
  | PProduct list -> 
    let rec f = function
    | (x, PId x') when x=x' -> x
    | (tag, p) -> tag^": "^string_of_pattern p in
    "{"^sep_list "; " f list^"}"

let rec string_of_expr =
  let soe = string_of_expr in
  let sos = string_of_scheme in
  function
  | ELit(_, c) -> string_of_lit c
  | EColl(_, kind, list) ->
    "("^string_of_collection_kind kind^" "^sep_list " " soe list^")"
  | EId(_, s) -> s
  | ELambda(_, _, _, _, tr) as e ->
    let type_annot = if is_fresh_tvar (snd tr) then "" else " :: "^sos tr in
    let rec f = function
      | ELambda(_, p, tp, e, te) ->
        let p = if is_fresh_tvar (snd tp) then (string_of_pattern p) 
          else string_of_pattern p^" :: "^sos tp in
        p^" "^f e
      | e -> type_annot^": "^soe e in
    "(λ"^f e^")"
  | ELet(_, p, t, e0, e1) ->
    if is_fresh_tvar (snd t)
    then "let "^string_of_pattern p^" = "^soe e0^"; "^soe e1
    else "let "^string_of_pattern p^" :: "^sos t^" = "^soe e0^"; "^soe e1
  | EApp _ as e -> let rec f = function EApp(_, a, b) -> f a^" "^soe b | e -> soe e in "("^f e^")"
  | ETuple(_, list) -> "(" ^ sep_list ", " soe list ^ ")"
  | ESequence(_, list) -> "(" ^ sep_list "; " soe list ^ ")"
  | ETupleGet(_, e0, tag) -> soe e0 ^"."^string_of_int tag
  | EProduct(_, pairs) -> "{"^sep_list ", " (fun (tag, e) -> tag^" "^soe e) pairs^"}"
  | EProductGet(_, e0, tag) -> soe e0^"."^tag
  | EProductSet(_, e0, tag, e1) -> soe e0^"."^tag^" <- "^soe e1
  | EStoreSet(_, v, e0, e1) -> "@"^v^" <- "^soe e0^"; "^soe e1
  | ESum(_, tag, ETuple(_, [])) -> tag
  | ESum(_, tag, e0) -> tag^" "^soe e0
  | ESumCase(_, e0, triplets) -> "(case "^soe e0^" | "^sep_list " | " (fun (tag, (v, e)) -> tag^": "^soe e) triplets^")"
  | EBinOp(_, e0, op, e1) -> "("^soe e0^" "^string_of_binop op^" "^soe e1^")"
  | EUnOp(_, op, e0) -> string_of_unop op^soe e0
  | ETypeAnnot(_, e0, t) -> "("^soe e0^": "^string_of_type t^")"

let string_of_store_decl (tag, t, v) =
  let d = "@"^(String.uncapitalize_ascii tag)^" :: "^string_of_type t in
  match v with None -> d^";" 
  | Some v -> d^" = "^string_of_expr v

let string_of_contract (d, s, e) =
  sep_list "\n" string_of_type_decl d ^ "\n" ^
  sep_list "\n" string_of_store_decl s ^ "\n" ^
  string_of_expr e
