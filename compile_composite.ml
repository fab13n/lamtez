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

open Printf

type code = string

let p2s = List.fold_left (fun acc b -> acc^if b then "T" else "F") ""
let pp2s pp = 
  let ss = List.map p2s pp in List.fold_left (fun acc s -> acc^" "^s) "" ss

let cc x = String.concat "; " (List.filter ((<>) "") x)

(* `paths n` generates a list of n different paths, each different,
 * and none being prefix to another. A path is a list of booleans.
 * Paths are used to map sum types of arbitrary size to nested
 * Left/Right constructors, and pairs to CAR/CDR sequences.
 *
 * All other functions in the module rely on `paths`, so changing
 * it changes the whole encoding/decoding algorithms. The current
 * implementation offers balanced encoding (making the longest path
 * as short as possible), but left-most or right-most encoding,
 * of the form `(pair a (pair b (pair c (...))))`
 * or `(pair (pair (pair (...))))` are also possible.
 *
 * Invariant: the resulting list of paths must be lexicographically
 * sorted with `false < true`. Other functions rely on this invariant.
 *)
let rec paths = function
  | 0 -> failwith "Invalid path request"
  | 1 -> [[]]
  | n ->
    let n_left = n/2 in
    let n_right = n - n_left in
    List.map (fun x -> false::x) (paths n_left) @
    List.map (fun x -> true::x) (paths n_right)

(* Generates a type corresponding to a product/sum.
 * Can be used to generate strings or other structures through maker functions.
 *)
let type_ make_node make_leaf fields =
  let pp = paths (List.length fields) in
  let pp_n = List.map2 (fun a b -> a, b) pp fields in
  let rec build = function
    | [[], field] -> make_leaf field
    | pp_n ->
      let pp_t, pp_f = List.partition (fun x -> List.hd (fst x)) pp_n in
      let trim = List.map (function (_::p, n) -> (p, n) | _ -> assert false) in
      make_node (build (trim pp_f)) (build (trim pp_t)) in
   build pp_n   

(* Generates a Michelson type of nested "or" (respectively "and") type combinators,
 * out of a list of basic Michelson types. For instance
 * `sum_type ["A"; "B"; "C"; "D"]` generates `"(or (or A B) (or C D))"` 
 *)
let sum_type, 
    product_type,
    product_data = 
  let make_node = sprintf "(%s %s %s)" and make_leaf x = x in
  type_ (make_node "or") make_leaf, 
  type_ (make_node "pair") make_leaf,
  type_ (make_node "Pair") make_leaf

let sum_data i n e =
  let path = List.nth (paths n) i in
  let rec fold b e = sprintf "(%s %s)" (if b then "Right" else "Left") e in
  List.fold_right fold path e


(* Returns the sequence of LEFT/RIGHT operators which will turn the top-of-stack
 * into the `i`th alternative out of `n`.
 * For instance 
 * `sum_make ["A"; "B"; "C"; "D"]` generates `"(or (or A B) (or C D))"` 
 *)
let sum_make i types =

  let module Tree = struct
    type t = Node of t * t | Leaf of string
    let t_of_types types = type_ (fun a b -> Node(a, b)) (fun x->Leaf x) types
    let rec string_of_t op = function
      | Leaf x -> x 
      | Node(a, b) -> "("^op^" "^string_of_t op a^" "^string_of_t op b^")"
  end in

  let n = List.length types in
  let path = List.nth (paths n) i in
  let rec f acc tree path = match tree, path with
    | Tree.Node(l, r), true  :: path' -> f (("RIGHT "^Tree.string_of_t "or" l)::acc) r path' 
    | Tree.Node(l, r), false :: path' -> f (("LEFT "^Tree.string_of_t "or" r)::acc) l path' 
    | Tree.Leaf _, [] -> acc
    | Tree.Leaf _, _::_ | Tree.Node _, [] -> assert false
  in
  let code = f [] (Tree.t_of_types types) path in
  cc code
  (* TODO List.rev? *)

(* Generates the nested `IF_LEFT{ }{ }` operators which will run the code in cases
 * on alternatives of the proper case. 
 *)
let sum_case cases =
  let pp = paths (List.length cases) in
  (* print_endline (pp2s pp); *)
  let pp_n = List.map2 (fun a b -> a, b) pp cases in
  let rec build = function
    | [[], body] -> body
    | pp_n ->
      let pp_t, pp_f = List.partition (fun x -> List.hd (fst x)) pp_n in
      let trim = List.map (function (_::p, n) -> (p, n) | _ -> assert false) in
      "IF_LEFT { " ^ build (trim pp_f) ^ " }\n{ " ^ build (trim pp_t) ^ " }\n" in
   build pp_n   

(* Generates code which:
 *  * if the top-of-stack is the i-th alternative out of n,
 *    extracts it from its LEFT/RIGHT boxes
 *  * otherwise, makes the contract fail
 *)
let sum_get i n =
  let a = Array.make n "FAIL" in
  a.(i) <- "";
  let code = sum_case (Array.to_list a) in
  Str.global_replace (Str.regexp "\n") " " code

(* Turns the `n`  elements on the stack into a n-tuple.
 * First element of the tuple must be on top of stack, last on bottom. 
 *)
let product_make = function 0 -> "" | n ->
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
  let code_str  = cc code_list in
  code_str

(* Generates code which takes a n-product on top of stack,
 * and returns its n-th element.
 *)
let product_get i n =
  if n=1 then "# NOOP (get from single-element product) \n" else begin
    let p = List.nth (paths n) i in
    let x = List.fold_left (fun acc b -> acc^if b then "D" else "A") "" p in
    "C"^x^"R"
  end

(* Generates code transforming `f1 : tuple[i/n=f0] : _` into `tuple[i/n=f1] : _`. *)
let product_set i n =
  if n=1 then "SWAP; DROP" else
    let path = List.nth (paths n) i in
    let rec f (undo, redo) = function
    | true -> "DUP; CAR; SWAP; CDR" :: undo, "PAIR" :: redo
    | false -> "DUP; CDR; SWAP; CAR" :: undo, "SWAP; PAIR" :: redo
    in 
    let undo, redo = List.fold_left f ([], []) path in
    Printf.sprintf "DIP { %s }; # open up product\n SWAP; DROP; # replace field %d/%d\n %s; # rebuild product\n"
      (cc (List.rev undo)) i n (cc (List.rev redo))

(* Generates code which splits a product, i.e. pushes all of its elements in order on the stack
 * (TODO first on top or first on bottom ?)
 *)
let product_split n =
  let part_and_trim x =
    let xT, xF = List.partition List.hd x in
    List.map List.tl xF, List.map List.tl xT in
  let rec f = function [[]] -> "" | pp -> 
    let pp_F, pp_T = part_and_trim pp in
    let code_F = f pp_F in
    let code_T = if pp_T = [[]] then "" else "DIP { "^f pp_T^" }" in
    cc ["DUP; CDR; SWAP; CAR"; code_T; code_F]
  in f (paths n)

let show n =
  for i=1 to n do
    print_endline(string_of_int i^":"^pp2s (paths i))
  done
