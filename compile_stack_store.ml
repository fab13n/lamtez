module I = Intermediate

let tuples = ref []

let reset() = tuples := []

let add list = tuples := list :: !tuples

let get() = match !tuples with
  | [] -> I.TProduct(Some("unit", []), lazy [])
  | list ->
    let p_of_l l = I.TProduct(None, lazy l) in
    I.TSum(None, lazy (List.map p_of_l list))
  