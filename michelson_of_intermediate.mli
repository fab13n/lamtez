module I = Intermediate

type stack

val compile_etype: I.etype -> string
val compile_typed_expr: stack -> I.typed_expr -> stack * string
val compile_contract: I.contract -> string * string option
