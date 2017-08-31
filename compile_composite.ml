(* Sum/Product code generation
 *
 * Sums and products need to be encoded as nested two-element pairs,
 * and nested Left/Right alternatives respectively. This module performs
 * this encoding.
 *
 * The nesting pattern is determined by the `path` function, which takes
 * a number of cases and returns a corresponding list of paths, encoded
 * as boolean lists. This function's implementation can be changed at will,
 * provided of course that the same function is used for encoding and decoding.
 *
 * The current implementation generates paths as short as possible; other
 * possibilities include nesting always to the left, or always to the right,
 * or preferentially attribute shorter paths to the leftmost alternatives...
 *
 *)

let p2s = List.fold_left (fun acc b -> acc^if b then "T" else "F") ""
let pp2s pp = 
  let ss = List.map p2s pp in List.fold_left (fun acc s -> acc^" "^s) "" ss

(* `paths n` generates a list of n different paths, each different,
 * and none being prefix to another. A path is a list of booleans.
 * Paths are used to map sum types of arbitrary size to nested
 * Left/Right constructors, and pairs to CAR/CDR sequences.
 *)
let rec paths = function
  | 0 -> failwith "Invalid path request"
  | 1 -> [[]]
  | n ->
    let n_left = n/2 in
    let n_right = n - n_left in
    List.map (fun x -> false::x) (paths n_left) @
    List.map (fun x -> true::x) (paths n_right)

(* Returns the sequence of LEFT/RIGHT operators which will turn the top-of-stack
 * into the `i`th alternative out of `n`. *)
let sum i n =
  let p = List.nth (paths n) i in
  let l = List.map (fun b -> if b then "RIGHT" else "LEFT") p in
  List.fold_left (fun acc x-> acc^" "^x^";") "" l
  (* TODO List.rev? *)

(* Generates the nested `IF_LEFT{ }{ }` operators which will run the code in cases
 * on alternatives of the proper case. *)
let sum_case cases =
  let pp = paths (List.length cases) in
  (* print_endline (pp2s pp); *)
  let pp_n = List.map2 (fun a b -> a, b) pp cases in
  let rec build = function
    | [[], body] -> body
    | pp_n ->
      let pp_t, pp_f = List.partition (fun x -> List.hd (fst x)) pp_n in
      let trim = List.map (function (_::p, n) -> (p, n) | _ -> assert false) in
      "IF_LEFT { " ^ build (trim pp_f) ^ " } { " ^ build (trim pp_t) ^ " }" in
   build pp_n   

(* Turns the `n`  elements on the stack into a n-tuple.
 * First element of the tuple must be on top of stack, last on bottom. *)
let tuple n =
  let dip_pair = function
    | 0 -> "PAIR"
    | n -> "D"^String.make n 'I'^"P { PAIR }" in

  let rec step y =
    print_endline("step "^pp2s y);
    match y with
    | (false::x0) :: (true::x1) :: y when x0=x1 -> 0, x0::y
    | x :: y -> let n, y = step y in n+1, x::y
    | [] -> assert false in

  let rec f y =
    print_endline("f "^pp2s y);
    match y with
    | [[]] -> []
    | [_] -> assert false
    | y -> let n, y = step y in n :: f y in

  let rev_paths = List.map List.rev (paths n) in
  let code_list = List.map dip_pair (f rev_paths) in
  let code_str = String.concat "; " code_list in
  code_str

(* Retrieve the i-th element in an n elements product *)
let product_get i n =
  let p = List.nth (paths n) i in
  let x = List.fold_left (fun acc b -> acc^if b then "D" else "A") "" p in
  "C"^x^"R"

(* Generate the Michelson type corresponding to a product/sum. *)
let type_ t fields =
  let pp = paths (List.length fields) in
  let pp_n = List.map2 (fun a b -> a, b) pp fields in
  let rec build level = function
    | [[], field] -> field
    | pp_n ->
      let pp_t, pp_f = List.partition (fun x -> List.hd (fst x)) pp_n in
      let trim = List.map (function (_::p, n) -> (p, n) | _ -> assert false) in
      "("^t^" " ^ build (level) (trim pp_f) ^ " " ^ build (level+1) (trim pp_t) ^ ")" in
   build 0 pp_n   

let sum_type = type_ "or" and product_type = type_ "pair"

(* Generate a code transforming `f1 : tuple[i/n=f0] : _` into `tuple[i/n=f1] : _`. *)
let product_set i n =
  let path = List.nth (paths n) i in
  let rec f (undo, redo) = function
  | true -> "DUP; CAR; SWAP; CDR" :: undo, "SWAP; PAIR" :: redo
  | false -> "DUP; CDR; SWAP; CAR" :: undo, "PAIR" :: redo
  in 
  let undo, redo = List.fold_left f ([], []) path in
  Printf.sprintf "DIP { %s }; # open up product\n SWAP; DROP; # replace field %d/%d\n %s; # rebuild product\n"
    (String.concat "; " (List.rev undo)) i n (String.concat "; " (List.rev redo))

let show n =
  for i=1 to n do
    print_endline(string_of_int i^":"^pp2s (paths i))
  done
