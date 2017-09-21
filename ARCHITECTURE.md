contracts are compiled in 3 steps:

* A Menhir parser (`parser.mly`, `lexer.mll`) translates concrete
  syntax into an abstract syntax tree (`ast.ml`).

* Types are checked or inferred (`typecheck.ml`); the typing context,
  type declarations and types of expressions variables, are handled by
  `typecheck_ctx`, which also performs unification, and remembers the
  types of every subterm.

* AST, with the type annotations gathered in the typechecking context,
  are compiled (`intermediate_of_ast.ml`) into an intermediate tree representation
  (`intermediate.ml`). The difference between syntactic AST and intermediate trees are:

    * Intermediate trees are fully type-annoted;
    * sum and product types are structural, i.e. instead of naming labels, they're
	  referred to as label `i` out of `n` (tuples and labelled products thus become
	  undistinguishable);
	* lambda and application currying are removed;
	* no more polymorphic type schemes (present in ASTs in case they become practical
	  to compile to Michelson);
	* Irrefutable patterns are desugared;
	* no more distinction between primitives functions and operators.

* Michelson is generated out of the intermediate tree (`michelson_of_intermediate.ml`):

    * A count is kept of the depth at which each variable is stored on the stack,
      so that they can be retrieved on top-of-stack with a `DUU*P` opcode;
    * functions and primitives applications are compiled by first
      stacking the arguments, then calling the functions, which pops
      them from the stack and pushes a single value instead.
	* composite types are compiled into nested binary pairs and left/right alternatives
	  (`compile_composite.ml`.)
	* store updates are implemented through `PEEK` / `POKE` macros, which allow to bring
	  an element at an arbitrary depth to the top-of-stack (moving it rather than copying it,
	  contrary to `DUU*P`), and to push it back at an arbitrary depth. the store is therefore
	  brought from the bottom of the stack, the relevant field is updated, and the result is
	  pushed back to the bottom.
	* closures are implemented as a pair `(function, env_variables)`, their application
	  bundles environment and argument before passing that pair to the function, and the
	  function unwrap those on the stack before executing its actual code. It's by no mean
	  perfect: closures can't be used by primitives expecting purely combinatory functions,
	  and the environment types show in the resulting Michelson type, which makes two closures
	  with same argument and result types, but different environment incompatible. This could
	  be fixed by wrapping environments into ad-hoc sum types.
    * `contract-call`, the equivalent to `TRANSFER_TOKENS`, are treated in a special way, to
	  ensure that they're called on an empty stack: before `TRANSFER_TOKENs` is called, the
	  stack is saved in a dedicated field of the storage, and if the transfer doesn't fail,
	  it is restored after it returns. Since it requires to generate an ad-hoc field with
	  a global sum type in the storage, this operation is performed in two steps: all transfer
	  operations are patched after a first generation pass (by `patch_stack_store_operations`).

Michelson is currently generated directly as a string, which is messy; I plan to replace
it with a proper data structure, which includes comments (the generated code features some
comments, mainly about the stack's state, in order to help making sense out of the code).
