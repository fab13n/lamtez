type t

val empty: t

val scheme_of_evar: t -> Tree.evar -> (Tree.tvar list * Tree.typeT)
val instantiate_scheme: (Tree.tvar list * Tree.typeT) -> Tree.typeT
val instantiate_composite: Tree.tvar -> Tree.tvar list * (Tree.tag * Tree.typeT) list -> Tree.typeT * (Tree.tag * Tree.typeT) list

val sum_of_name: t -> Tree.tvar -> Tree.tvar list * (Tree.tag * Tree.typeT) list
val name_of_sum_tag: t -> string -> string

val product_of_name: t -> Tree.tvar -> Tree.tvar list * (Tree.tag * Tree.typeT) list
val name_of_product_tag: t -> Tree.tag -> Tree.tvar

val decl_of_name: t -> Tree.tvar -> Tree.declT

val add_sum: Tree.tvar -> Tree.tvar list -> (Tree.tag * Tree.typeT) list -> t -> t 
val add_product: Tree.tvar -> Tree.tvar list -> (Tree.tag * Tree.typeT) list -> t -> t 
val add_alias: Tree.tvar -> Tree.schemeT -> t -> t
val add_prim: Tree.tvar -> Tree.tvar list -> t -> t

val add_evar: Tree.tvar -> Tree.schemeT -> t -> t
val forget_evar: Tree.tvar -> t -> t

val unify: t -> Tree.typeT -> Tree.typeT -> (t * Tree.typeT)
val expand_type: t -> Tree.typeT -> Tree.typeT
val expand_scheme: t -> Tree.schemeT -> Tree.schemeT

val string_of_t: t -> string
