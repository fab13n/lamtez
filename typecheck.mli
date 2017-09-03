module Ctx = Typecheck_ctx
module A = Ast

type typed_contract ={
  ctx:          Ctx.t;
  storage_type: A.etype;
  param_type:   A.etype;
  result_type:  A.etype;
  storage_init: A.expr option;
  code:         A.expr;
}

val typecheck_expr:     Ctx.t -> A.expr -> (Ctx.t * A.etype)
val typecheck_contract: Ctx.t -> A.contract -> typed_contract
