open Utils

module T = Typecheck
module Ctx = Typecheck_ctx
module IoA = Intermediate_of_ast
module MoI = Michelson_of_intermediate

let store_of_lexbuf 
  (a_contract: T.typed_contract) 
  (i_contract: Intermediate.contract)
  (m_contract: MoI.contract)
  (lexbuf: Lexing.lexbuf) =
  let ctx = a_contract.T.ctx in
  let e_store_fields = Parser.data_store Lexer.read lexbuf in
  let e_prod = Ast.EProduct(Ast.noloc, e_store_fields) in
  let ctx, t_prod = T.typecheck_expr ctx e_prod in
  let ctx, _ = Ctx.unify ctx t_prod a_contract.T.storage_type in
  let iet_prod = IoA.compile_expr ctx e_prod in
  let c_prod = MoI.compile_data iet_prod in
  let c_storage = m_contract.MoI.make_storage c_prod in
  c_storage

let parameter_of_lexbuf
  (a_contract: T.typed_contract) 
  (i_contract: Intermediate.contract)
  (lexbuf: Lexing.lexbuf) =
  let ctx = a_contract.T.ctx in
  let expr = Parser.data_parameter Lexer.read lexbuf in
  let ctx, etype = T.typecheck_expr ctx expr in
  let ctx, _ = Ctx.unify ctx etype a_contract.T.param_type in
  let iet = IoA.compile_expr ctx expr in
  MoI.compile_data iet
