# Lamtez limitations

This file lists the current main limitations of Lamtez, the reason why
they subsist, and any migigation strategy I might have in mind to remove
or circumvent them.

## Function closures

Closures are functions which use variables defined outside of them, e.g.
`let n = 3; let closure = \(i :: nat): i+n`. They are one of the most basic
and useful idioms in functional programming.

Michelson lambdas cannot capture their environments, so they can't implement
proper closures natively. Our solution is to implement closures as
`(lambda × env)` pairs, and adapt function applications accordingly.
However, there's no way to pass such a closure to higher level operators `CREATE_CONTRACT`, `MAP` and `REDUCE`.

#### Mitigation:

* functions which don't need a closure will be compiled as straight lambdas 
  and operators will accept them, attempts to pass an actual closure will
  fail on typecheck.

* the type system will have to distinguish between the lambdas which are
  closures or pure functions; an alternative arrow `~>` might be needed to
  denote function arguments which only accept pure functions.

## Recursive functions

Michelson's type system closely ressembles that of the simply-typed lambda calculus, which means it can't accept recursion. Actually, the `List` type
cannot be encoded in Michelson, except maybe (?) through some loophole involving contract creations and immediate execution.

#### Mitigation:

The `LOOP` operator can replace tail-call recursion, i.e. recursion that doesn't grow a call stack. However, it has no natural syntax in a language
that is not stack based and does not fully support mutable variables.

An envisionned syntax, compiling to `LOOP`, would be something like:

    let loop <id*> = <body[id*]> while <condition[id*]> else <initial_value>

where `<body[id*]>` and `<condition[id*]>` could use identifiers in `<id*>`. 
Evaluation would start with `<id*> = <initial_value>`. As long as 
`<condition[id*]>` stays true with the id values of time _t_, those values
are replaced by the body at time _t+1_.

For instance, the following would store the factorial of `n` in `f`

    let fact = \(n :: nat):
      let loop (f, i) = (f*i, i-1) while n>0 else (1, n);
      f

To be usable, this would require the support of irrefutable patterns (writing 
`let (a, b) = my_pair;` instead of `let a=mypair.0; let b=mypair.1;`).

## Polymorphic functions

Although Michelson is not polymorphic, it would be possible to have polymorphic
functions inside a contract, as long as they don't show up as polymorphic in
the contract's type: one has to create as many copies of them as there are
use cases in the contract.

However, given the other severe limitations on lambdas in Tezos, this doesn't seem like something very useful.

## Partially applied functions

By encoding multi-parameter functions the Curry way (`f(x, y, z) = r` is 
encoded as `f = \x: (\y: (\z: r))`), one creates the possibility of only 
partially applying functions (here `let g = f 1 2; let n = g 3`).

This can be encoded through "eta-expansion" (rewriting `let g = f 1 2`
into `let g = \z: f 1 2 z`), but hasn't been done yet. Again, not sure how
useful are typical functional idioms in a language taht wouldn't allow recursion.

## Primitive shadowing

I haven't made up my mind about local variables shadowing primitives: the
classical way is to allow it silently, but maybe it's safer to refuse it?
For now, nothing is done, so attempting to shadow a primitive will raise
undefined behaviors.

## Crypto keys

Literal crypto keys are not implemented, that's an oversight.

