let sep_list sep f = function
| [] -> ""
| a::b -> List.fold_left (fun acc x -> acc^sep^f x) (f a) b

exception Unsupported of string
exception Not_impl of string
exception Unsound of string
exception Typing of string

let unsupported msg = raise (Unsupported msg)
let not_impl msg = raise (Not_impl msg)
let unsound msg = raise (Unsound msg)
let type_error msg = raise (Typing msg)