
exception Unsupported of string
exception Not_impl of string
exception Unsound of string
exception Typing of Ast.loc * string

let unsupported msg = raise (Unsupported msg)
let not_impl msg = raise (Not_impl msg)
let unsound msg = raise (Unsound msg)
let type_error loc msg = raise(Typing(loc, msg))

let sep_list sep f = function
| [] -> ""
| a::b -> List.fold_left (fun acc x -> acc^sep^f x) (f a) b

(* Combo of a fold_left with a map: the function f returns both
 * an accumulator and a transformed list element. *)
let list_fold_map f acc list =
  let acc, rev_list = List.fold_left
    (fun (acc, list') a -> let acc, b = f acc a in acc, b::list')
    (acc, []) list
  in
  acc, List.rev rev_list

(* Makes sure the two assoc lists have the same key set, perform a map2
 * on their elements, return the resulting assoc list.
 * Quadratic is the length of b, but assoc lists are supposed to be short.
 * ('k -> 'a -> 'b -> 'c) -> ('k*'a) list -> ('k->'b) list -> ('k->'c) list.
 *)
let list_assoc_map2 f a b =
  if List.sort compare (List.map fst a) <> List.sort compare (List.map fst b)
  then type_error Ast.noloc "different tag sets for composite type"; (* TODO location *)
  List.map (fun (k, va) -> k, f k va (List.assoc k b)) a
