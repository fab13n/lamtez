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

type tvar = string
type tname = string

type etype =
| TPrim of tname * etype list
| TLambda of etype list * etype
| TProduct of (tname * etype list) option * etype list Lazy.t
| TSum of (tname * etype list) option * etype list Lazy.t (* TODO name and args shouldn't be optional. *)

type evar = string

type collection_kind = Ast.collection_kind

type typed_expr = expr * etype

and expr =
| ELit of string
| EColl of collection_kind * typed_expr list
| EId of evar
| ELambda of (evar * etype) list * typed_expr
| ELet of (evar * typed_expr * typed_expr)
| EApp of typed_expr * typed_expr list
| EProduct of typed_expr list
| ESum of int * int * typed_expr
| EProductGet of typed_expr * int * int
| EProductSet of typed_expr * int * int * typed_expr
| EStoreSet of int * typed_expr * typed_expr
| ESumCase of typed_expr * (evar * etype * typed_expr) list

type store = (int * etype) list

type contract = {
  storage_type: etype;
  storage_init: typed_expr option;
  code:         typed_expr }
