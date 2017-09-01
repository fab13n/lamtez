module Ctx = Typecheck_ctx
module A = Ast

val typecheck_expr:     Ctx.t -> A.expr -> (Ctx.t * A.etype)
val typecheck_contract: Ctx.t -> A.contract -> (Ctx.t * A.etype * A.etype)
