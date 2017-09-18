module A = Ast

type t

val empty: t

val scheme_of_evar: t -> A.evar -> (A.tvar list * A.etype)
val instantiate_scheme: (A.tvar list * A.etype) -> A.etype
val instantiate_composite: A.tvar -> A.tvar list * (A.tag * A.etype) list -> A.etype * (A.tag * A.etype) list

val sum_of_name: t -> A.tvar -> A.tvar list * (A.tag * A.etype) list
val name_of_sum_tag: t -> string -> string

val product_of_name: t -> A.tvar -> A.tvar list * (A.tag * A.etype) list
val name_of_product_tag: t -> A.tag -> A.tvar

val decl_of_name: t -> A.tvar -> A.decl

val add_sum: A.tvar -> A.tvar list -> (A.tag * A.etype) list -> t -> t
val add_product: A.tvar -> A.tvar list -> (A.tag * A.etype) list -> t -> t
val add_alias: A.tvar -> A.scheme -> t -> t
val add_prim: A.tvar -> A.tvar list -> t -> t

type bookmark_item
type bookmark = bookmark_item list
val bookmark_empty: bookmark
val add_evar: A.evar -> A.scheme -> t -> t
val push_evars: (A.evar*A.scheme) list -> t -> (t*bookmark)
val pop_evars: bookmark -> t -> t

val unify: t -> A.etype -> A.etype -> (t * A.etype)
val expand_type: t -> A.etype -> A.etype
val expand_scheme: t -> A.scheme -> A.scheme

val save_type: A.expr -> A.etype -> t -> t
val retrieve_type: t -> A.expr -> A.etype

val get_evars: t -> A.evar list

val string_of_t: t -> string

val _DEBUG_: bool ref
