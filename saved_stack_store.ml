module I = Intermediate

let tuples = ref [[]]

let reset() = tuples := [[]]

let add list = 
  tuples := !tuples @ [list];
  List.length !tuples - 1

let get n = match List.nth !tuples n with
  | [] -> I.TProduct(Some("unit", []), lazy []), []
  | list -> I.TProduct(None, lazy list), list

let get_all () =
  let pairs = List.mapi (fun i _ -> get i) !tuples in
  let prod_types = List.map fst pairs in
  I.TSum(None, lazy prod_types), prod_types
