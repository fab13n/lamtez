type code = string

val sum_make: int -> code list -> code
val sum_case: code list -> code
val sum_get : int -> int -> code
val sum_type: code list -> code

val product_make : int -> code
val product_get  : int -> int -> code
val product_set  : int -> int -> code
val product_split: int -> code
val product_type : code list -> code
