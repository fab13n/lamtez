val typecheck_expr:     TypingContext.t -> Tree.exprT -> (TypingContext.t * Tree.typeT)
val typecheck_contract: TypingContext.t -> Tree.programT -> (TypingContext.t * Tree.typeT * Tree.typeT)
val retrieve_type:      TypingContext.t -> Tree.exprT -> Tree.typeT
