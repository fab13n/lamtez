module I = Intermediate

type contract = {
  code: string;
  storage_init: string option;
  make_storage: string -> string;
}

val compile_etype: I.etype -> string
val compile_contract: I.contract -> contract
val compile_data: I.typed_expr -> string

val _DEBUG_: bool ref
