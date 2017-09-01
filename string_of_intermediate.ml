(* Compile a type lamtez term into an intermediate representation where:
 * * Nodes are fully type-annotated;
 * * Labelled products and sums are replaced by indexed versions;
 * * Lambdas and applications are replaced by multi-arg versions,
 *   eta-expanding partially applied functions (TODO);
 * * TApp types are sorted between sums, products and primitives;
 *
 * sum and product type contents are lazy, because some inductive types
 * such as `list` have infinite expanded types.
 *)

open Printf
open Utils
open Intermediate

let rec string_of_etype =
  let t = string_of_etype in
  function
  | TPrim(name, []) -> name
  | TPrim(name, args) -> "("^name^sep_list " " t args^")"
  | TLambda(params, result) -> "("^sep_list ", " t params^" -> "^t result^")"
  | TProduct(Some("unit", []), lazy []) -> "unit"
  | TProduct(_, lazy []) -> "(*)"
  | TProduct(_, lazy list) -> "("^sep_list " * " t list^")"
  | TSum(_, lazy []) -> "(+)"
  | TSum(_, lazy list) -> "("^sep_list " + " t list^")"

let rec string_of_expr =
  let t = string_of_etype in
  let et = string_of_typed_expr in
  function
  | ELit s | EId s -> s
  | ELambda(params, body) ->
    "(\\"^sep_list " " (fun (v, vt) -> "["^v^":"^t vt^"]") params^" -> "^et body^")"
  | ELetIn(v, e0, e1) -> "let "^v^" = "^et e0^" in "^et e1
  | EApp(f, args) -> "("^sep_list " " et (f::args)^")"
  | EProduct x  -> "("^sep_list ", " et x^")"
  | ESum (i, n, x) -> sprintf "<%d|%d> %s" i n (et x)
  | EProductGet(x, i, n) -> sprintf "%s.<%d|%d>" (et x) i n
  | EProductSet(x, i, n, y) -> sprintf "%s.<%d|%d> <- %s" (et x) i n (et y)
  | EStoreSet(i, e0, e1) -> sprintf "@%d <- %s; %s" i (et e0) (et e1)
  | ESumCase(e, cases) ->
    let f (var, it, e_case) = "["^var^":"^t it^"] -> "^et e_case in
    "("^et e^" ? "^sep_list " | " f cases^")"

and string_of_typed_expr (e, t) = "["^string_of_expr e^":"^string_of_etype t^"]"

let rec string_of_untyped_expr e =
  let r (e, t) = string_of_untyped_expr e in
  match e with
  | ELit s | EId s -> s
  | ELambda(params, body) ->
    "\\"^sep_list " " fst params^" -> "^r body
  | ELetIn(v, e0, e1) -> "let "^v^" = "^r e0^" in "^r e1
  | EApp(f, args) -> "("^sep_list " " r (f::args)^")"
  | EProduct x  -> "("^sep_list ", " r x^")"
  | ESum (i, n, x) -> sprintf "<%d>%s" i (r x)
  | EProductGet(x, i, n) -> sprintf "%s.<%d>" (r x) i
  | EProductSet(x, i, n, y) -> sprintf "%s.<%d> <- %s" (r x) i (r y)
  | EStoreSet(i, x, y) -> sprintf "@%d <- %s; %s" i (r x) (r y)
  | ESumCase(e, cases) ->
    let f i (v, _, e_case) = sprintf "<%d>(%s): %s" i v (r e_case) in
    let cases = List.mapi f cases in
    "("^r e^" ? "^String.concat " | " cases^")"