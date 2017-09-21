lamtez: a typed lambda-calculus compiling to Tezos Michelson VM
================================================================

Lamtez is Domain-Specific Language for smart contracts, and its compiler to
Michelson, [Tezos](http://www.tezos.ch)' virtual machine for smart contracts
execution.

It is released under the MIT license, with no guaranty of any kind (among other,
there's no proof that it compiles to sound nor correct Michelson code). I'm
interested in feedbacks anyway, if you experiment with it.

## Building

The compiler is written in OCaml; the build process relies on `ocamlbuild`,
and it depends on the parser generator [menhir](http://gallium.inria.fr/~fpottier/menhir/).
If [opam](https://opam.ocaml.org/) is installed on your system, `opam install
ocamlbuild menhir` should be enough to get a building environment. If you
compiled Tezos from sources, Lamtez requirements are a subset of Tezos'.

## Examples

If you would rather look at source code examples first, before reading the
fine manual, you can go and check
[EXAMPLES.md](https://github.com/fab13n/lamtez/blob/master/EXAMPLES.md). It reimplements
contract exmaples from [http://michelson-lang.com] and
[the Michelson specification](https://github.com/tezos/tezos/blob/master/src/proto/alpha/docs/language.md).

## Cheat sheet

For a quick summary of the language syntax and main features, a PDF two-pages
summary is available as https://github.com/fab13n/lamtez/raw/master/CHEAT-SHEET.pdf.

## General considerations on the language

The language is strongly influenced by ML dialects OCaml and Haskell: mostly
functional, relying heavily on sum-types and product-types, statically typed
with type inference. It also composes with some limitations in Michelson. Most
of the limitations in Michelson language follow from the following
assumptions:

* Most useful smart contracts will be rather simple, commpared to typical
  programs written be profesionnal developers in general-purpose languages;

* A very high level of confidence in contracts correctness will be required.
  Given how finding and exploiting bugs in smart contracts can be turned into
  tokens and actual money, every contract handling significant amounts of
  money will be thoroughly reviewed and attacked by black-het hackers, several
  of them smarter than the contract's author and white-hat reviewers.

* Tezos being self-amending, it's better to start with a very limited language
  and progressively add empirically needed features, rather than start with
  many bells and whistles: some of them might prove less secure than
  anticipated, or not as useful as it first seemed, but each of them making
  formal proofs more tedious or complicated to produce.

Michelson closely ressembles a simply-typed lambda calculus, without native
recursivity nor proper closures; drastic limitations also exist on the ability
for a contract to call other contracts.

Compared to hand-written Michelson, Lamtez contracts offer higher-level
features:

* Sum and product types of arbitrary size and with arbitrary field/case names.
  In Michelson, sums with more than two alternatives and products with more
  than two fields have to be encoded with nested alternatives and pairs, thus
  quickly becoming hard to read for humans.

* lexically scoped variables: keeping track of what is at which level of the
  stack is cumbersome when writing a program, and it makes reading someone
  else's contracts dreadful. Being able to name things rather than shuffling
  them on a stack greatly improves contract readability.

* Limited support for closures: a function can use variables declared outside
  of it. This feature is however currently limited, as it is tedious to
  abstract away the types of the variables captured by closures (this might
  change if closures prove to be very useful in typical smart contracts).

* type inference: as most ML dialects, lamtez uses a variant of the W
  algorithm to guess types with very little user annotations. However,
  contrary to ML, it expects the final contract not to be polymorphic, as
  Michelson doesn't support it. So you might get some "Add more type
  annotations" errors. Annotating function parameters is sufficient, although
  often not necessary, to ensure a monomorphic contract type. (inner
  polymorphic functions are technically possible, but NOT YET IMPLEMENTED)

* storage management: instead of manually managing the storage, variables
  prefixed with `@` are declared and stored in it, and can be updated
  in the contract through a simple and readable syntax (under some conditions).
  An option is provided to declare and extract an initial storage value
  from the contract source file.

* `TRANSFER_TOKEN`, the act of calling another contract, can only be
  done under very strict conditions in Michelson (the stack must be empty).
  This restriction is partially lifted in Lamtez: it will dedicate a field
  in the storage to save the stack before calling, and restore it after
  it returns.

(note: currently, the stack is saved rather naively: a big sum type is
reserved in the storage, one per invocation of `TRANSFER_TOKEN`, and
the whole stack is saved in it. First the  stack could be pruned before
saving, as some slots won't be used after the contract call anymore,
and two invocations with the same stack types above them should share
their slot)

Lamtez is mostly functional. It has two kinds of side effects: storage updates
and calls to other contracts. Normally, functional programming languages will
only let you touch side effects with a ten foot pole. They typically call that
pole a "monad"; wielding a monad towards unfamiliar developers scares them
about as much as doing so with an actual ten foot pole.

Lamtez doesn't explicitly supports monads, but it enforces some (coarser)
constraints about where side effects are accepted. Namely, these operations
can't happen in an inner function (we couldn't keep track of them without
monads then), nor in places where evaluation order isn't intuitively obvious:
not in tuples/products, not in function arguments.

Whitespaces are not significant except to separate tokens, indentation is not
significant, comments start with a `#` sign and run until the end of the
current line.

Lamtez is not proved correct in any way; the proper way to ensure any
correctness property is by working directly on the generated Michelson code.
It is annotated and commented, among other with the stack's state after each
instruction, in order to help analysis.

## Anatomy of a contract

A contract is composed of:

* a series of _type declarations_: it creates type structures, with
  arbitrary sizes, arbitrary labelled fields and alternative cases.

* a series of _stored variables_: those variables, starting with a
  `@` symbol, are kept between contract calls in the blockchain's
  storage. They can optionally be given an initial value; if all
  stored variables in the contract have an initial value, then one
  can extract a data initialization value from the contract, which
  can be directly passed to the tezos client.
  (In the future it will be possible to compile storage values from
  separate files; but the contract's type declarations are needed to
  properly encode sum and product values).

* a function, taking a parameter and returning a result. This function
  can also, under controlled conditions, perform two kinds of effects:
  calling other contracts, and updating the content of stored variables.


## Expression Syntax

### Functions and function applications

In languages inspired by lambda calculus, functions are introduced
with the `fun` keyword.

The complete syntax for a function is `fun x: body`. Parameters can be
annotated with types, through the `::` infix operator: `fun x :: nat:
body`. The result type can also be specified, although it can normally
be inferred by the compiler: `fun x :: nat :: unit: body`.

Lamtez supports multi argument functions, through currying (nested functions
returning functions, a standard idiom in λ-calcullus inspired languages) (NOT
YET IMPLEMENTED for user-defined functions; pass products instead, for now).

Functions are applied the ML/λ-calculus way, by putting the arguments after
the function, without parentheses nor separating commas, i.e. what's written
`f(x, y)` in C-inspired syntaxes is written `f x y`. Application is
left-associative, i.e. `f x y z` is read as `(((f x) y) z)`. Parentheses are
still needed for nested function applications, e.g `f(g(x), g(y))` in C would
give `f (g x) (g y)`.

Lamtez performs type inference, i.e. if there are enough hints in the code, it
will correctly guess the types which the user omitted to write. However,
unlike most other ML-family languages, polymorphism is not allowed, because
the underlying Michelson VM doesn't support it (TODO: inner lambdas could be
polymorphic, as long as it doesn't show on the outside type. Not sure hwo
useful that would be in practice). So if the type inference algorithm
determines that a function's best type is, say, `∀a: list a -> nat`, the
compiler will emit an error and demand more type annotations rather than
accepting

Examples:

    fun x: x
    fun x y: x + y
    fun x :: nat, y ::nat: x - y
    fun x :: nat, y: x * y
    fun parameter: ((), map-update parameter (Some self-amount) @store)

For instance, the simplest contract, identity, which does nothing, just takes
a unit parameter and returns a unit result, is written below:

    fun p :: unit: p

The barely more interesting one, which adds one to its parameter, is:

    fun p :: nat: p + 1

### Literals

Lamtez supports the same literals as Michelson:

* to distinguish naturals from positive integers, the later have to be
  prefixed with a `+` sign, so `42` is a natural number and `+42` is typed as
  an integer. Beware therefore that `f+1` is the application of function `f`
  to signed integer `+1`, and not an addition to number `f`.

* dates are represented with the ISO format, without surrounding quotes:
  `2017-08-22T22:00:00Z`, `2017-08-22T22:00:00+01:00`

* Tez amounts are represented with a `tz` prefix and optional cents: `tz1`,
  `tz1.00`, `tz.05` (TODO: support `_` characters). If there are cents, they
  must be two digits long: `tz0.`, `tz0.1` or `tz.100` are illegal.

* Signatures are represented with a `sig:` prefixing the base58 hash.

* Key hashes are written directly, without surrounding quotes; they are by
  their `tz1` followed by a base58 hash.

### Variables

Variable names must start with a lowercase letter or an underscore;
they are allowed to contain a `-`: this is currently used to sort
primitive functions into pseudo-namespaces. As a result, it's important to
leave spaces around `-` when used as a substraction infix operator.

Examples: `foo, bar0, contract-call, _foo, foo_bar, fooBar`

(In the future I might get rid of dashes in names, if there's a decent
namespace system instead)

### Let: local variables

ML-style local variables, `let x=a; b` evaluates `b` with `x` set to `a`.
Equivalent, execution-wise, to `(\x:b) a`.

Example:

    let x = 32;
    let y = 10;
    x + y

Lamtez being mostly functional, you can't update the value stored in a
variable; however, and as often done in ML dialect, you can shadow a variable
with a new variable of the same name:

    let x = 10;
    let x = 20;  # From here you can't refer to the first `x` variable anymore
    do_stuff_with x

### Tuples (unlabelled cartesian products)

Whereas Michelson supports pairs, Lamtez supports tuples of length bigger than
2 (and encodes them as nested pairs). Contrary to many ML dialects, tuples are
mandatorily surrounded with parentheses to avoid misleading precedence issues;
elements are separated with commas.

Elements are extracted from a tuple with the suffix `.n`, where `n` is a
litteral positive integer, 0-indexed. The extractor suffix binds tighter than
function application (same as most ML-family languages).

Tuples are encoded as balanced trees, i.e. so that the length of paths in
`n`-products grows as `log2(n)`. This can easily be changed if desired
(left-folded or right-folded accessors have `o(n)` access and update times,
but might lead to simpler proofs).

Example:

    let triplet = (32, 5, 5);
    triplet.0 + triplet.1 + triplet.2

### (labelled) Cartesian products

For larger composite structures, it's easier to refer to individual elements
by user-given names, rather than by number. This requires to declare a product
type before using it. Labels are like identifiers except that they start with
a capital letter.

Type declarations happen at the beginning of the contract (cf. infra);
labelled product types are sequences of labels and types separated by `*`
    symbols.

Litteral product types are sequences of labels and types, separated by commas
and surrounded by braces.

Access to product fields are made with a `.Label` suffix, which binds as
tightly as unlabelled product accessors.

Finally, one can generate a product from another: a product which is equal to
`p` except that field `F` has value `42` can be created through the syntax
`p.F<-42`.

Example:

    type coordinates = Latitude: int * Longitude: int

    let p = {Latitude: 43500, Longitude: 1500 };
    let i_miss_trigonometry = p.Latitude * p.Latitude + p.Longitude * p.Longitude;

    let p_2_degrees_north = p.Latitude <- p.Latitude+2;
    let p_south_west =
      (p.Latitude <- p.Latitude - 1)
      .Longitude <- p.Longitude + 1;

    (p, p_2_degrees_north, p_south_west)

### Sum types

Equivalent of labelled unions, they are a generalization of the
`Left|Right` Michelson operators with an arbitrary number of labels,
freely named.

Types have to be declared; they are declared the same way as products,
except that cases are separated with `+` instead of `*`.

A label can only belong to one sum type; for instance, it's illegal to
have both `type a = A: int + B: string` and `type b = A: int + C:
bool`.

Each case has one and only one associated value type. Make it a `unit`
if you don't use it, make it a tuple or a product if you need several
values.  Syntactically, unit arguments can be omitted, though.

Sum expressions are built with a label followed by an expression. It
binds as tightly as a function application.

Sum accessors, equivalent to ML's `match/with` or Michelson `IF_LEFT`,
are of the form `case expression | Label_0 v_0: e_0 |... | Label_n
v_n: e_n end`. the variables `v_n` can be omitted when they're not
used in the corresponding `e_n`. In sum cases, unit values can be
omitted too.

Booleans are encoded as `type bool = False unit | True unit`, so
if/then/else operations can be encoded as sum accessors, as shown
in the example below.

Option types `Some x + None`, binary alternatives `Left/Right` and
list constructors `Nil/Cons` are also predeclared as sum types.

Examples:

    type operation = Withdrawal tez + GetBalance unit + Deposit tez
    fun amount operation storage:
      case operation
      | Withdrawal a: (None, storage - a)
      | GetBalance:   (Some storage, storage)
      | Deposit:      (None, storage + a)
      end

    self-now > date ? True: "OK" | False: "Not yet"

Some syntax sugar is proposed for boolean cases, which allows to chain several
`if / then / else if * / else` statements:

* `if <cond>: <body0> end` is equivalent to
  `case <cond> | True: <body0> | False: () end`.

* `if <cond>: <body0> | else: <body1> end` is equivalent to
  `case <cond> | True: <body0> | False: <body1> end`.

* `if <cond_0>: <body_0> | ... | <cond_n>: <body_n> else: <body_e> end`
  is equivalent to nested if/then/elseif statements:

        case <cond_0>
        | True: <body_0>
        | False: case <cond_1>
             | True: <body_1>
             | False: case <cond_2>
                      | ...
                      | False: <body_e> end ... end


### Binary and unary operators

TODO


### Composite values

There are native syntaxes to enter lists, sets and maps:

    l = (list 1 2 3 4)
    s = (set "a" "b" "c" "d")
    m = (map 1 "one" 2 "two" 3 "three")

Lists can also be built out of `Cons` and `Nil` sum types.

### Type annotations

Expressions can be annotated with their types, with the `::` infix operator.
It serves several purposes: compiler-checked hint for contract readers,
helping the compiler resolve a polymorphic type, or helping it produce a more
precise error message when facing an unsound program.

### Storage

Michelson contracts have a storage value; it is stored on the blockchain,
passed as a parameter to contracts when they execute, and contracts return an
updated storage object which is stored back on the blockchain.

As non-trivial programs often store multiple values, the store is generally a
product type. Since Lamtez might need to store additional fields in the store,
contract developpers are expected to declare and use the field they need
through a dedicated `@` syntax:

* a sequence of `@name :: type` declarations after type declarations declare
  every storage field type and name;

* optionally, a value can be associated, e.g. `@n :: nat = 42`. If all stored
  values have such an initial value, a data initializer can be extracted from
  the contract, and passed to the tezos client.

* in the code, `@name` returns the current content of field `name`.

* fields can be updated with the syntax `@name <- expr`.

Storage fields cannot be updated anywhere: you can't update them inside
functions, in tuple or product elements, in function arguments.

If you want to update them inside a function, make the function return the
updated value and perform the update from outside:

    @n :: int

    let f = fun x :: int: @n <- x + 1; () # Illegal
    f 3

    let f = fun x :: int: x + 1;
    @n <- f 3 # Legal

Instead of performing storage updates in function arguments or products,
perform them before in a `let` expression.

### Loops

Loops are not very functional; however, in a languge that doesn't
fully support closures and doesn't support contract calls from inside
lambdas, access to the `LOOP` Michelson primitive is
necessary. Although this isn't implemented, my intention is to
introduce a syntax of the form `loop (<var*>) = (<expr*>) while
<condition> else (<expr*>)`:

* the `<expr*>` and `<var*>` lists have the same sizes;
* at step 0, the variables are assigned the values after the `else`;
* as long as `<condition>` is true, an iteration of the loop is performed:
    * the expressions before the `while` are evaluated, with the current
      assignments for `<var*>`;
    * the result is assigned to `<var*>`, before a new condition checking,
      and maybe iteration, is performed.

This feature would be much more practical to use with _irrefutable
patterns_, i.e. expressions of the form `let x, y = p; e(x, y)` as
shortcuts for `let x=p.0; let y=p.1; e(x, y)`. Tuples and products can
be destructured this way; sum types should not, as in most situations
there are several possible cases to take into account. This would make
the contract fail if the proper sum case isn't present, and we want
possible causes of failure to be highly visible. Hence there will
probably never be any support for syntaxes like `let Some x = expr0;
expr1`.

As an example, here's what factorial would look like with the loop operator:

    fun n: let (fact, _) = loop (acc, i) = (acc*i, i-1) while i > 0 else (1, n)

Some syntactic permissiveness might be granted for the order in which `loop`,
`while` and `else` elements are ordered:

    fun n: let (fact, _) = loop (acc, i) = (acc*i, i-1) while i > 0 else (1, n)
    fun n: let (fact, _) = while i > 0 loop (acc, i) = (acc*i, i-1) else (1, n)
    fun n: let (fact, _) = else (1, n) while i > 0 loop (acc, i) = (acc*i, i-1)

The first and second versions seem more naturally readable, the last
one follows "natural evaluation order" more closely.

It might also be sensible to accept `let loop (vars) = XXX while C else X0`
as a shortcut for `let (vars) = loop (vars) = XXX while C else X0`


### Type syntax

Types can be created at the beginning of the contract file. We've
already seen the syntax to create labelled product types `type name =
Label_0 field_type_0 * ... * Label_n field_type_n`, and sum types
`type name = Label_0: case_type_0 * ... * Label_n: case_type_n`. Type
aliases can also be created, with the notation `type name = type`.

Type can be polymorphic, i.e. take type parameters. Beware, however,
that since Michelson is not polymorphic, some valid Lamtez programs
will be rejected by the compiler. Type parameters are passed between
the name and the `=` sign. Lists are encoded that way in Lamtez.

Examples:

    type option a = None unit + Some a  # Actually predeclared
    type pair a b = (a * b)  # Actually predeclared
    type assoc_list k v = list (pair k v)


Type annotations can be the following:

* an identifier, i.e. the name of an alias, a sum type, a product type or a
  primitive.

* if an identifier is polymorphic, as the `option` example above, it must
  receive the corresponding number of parameters after it. For instance, `nat`
  is a valid type, so is `list int` or `list (pair string int)`, but `list` or
  `pair int` are not valid.

* Tuples are represented as types, separated with `*` and surrounded by
  parentheses, e.g. `(int * int)` or `(int*list a*tez)`.

* functions types are denoted `parameter_type -> result_type`. The arrow is
  right associative, and multi-parameter functions are encoded as curried
  (nested) lambda terms. For instance, a function from two ints to a string
  has type `int -> int -> string`.

### Contracts

A contract with parameter type `p`, and result type `r` is represented in a
file as a sequence of type declarations, then a sequence of store field
declarations, then an expression of type `p -> r`. The


Example:

    type operation = Withdrawal tez + GetBalance unit + Deposit tez

    @store :: tez

    fun amount operation:
      case operation
      | Withdrawal a: @store <- @store - a; None
      | GetBalance:   Some storage
      | Deposit:      @store <- @store + self-amount
      end

### Semantics

TODO

### Primitives

The primitives are listed here, with their corresponding Michelson
opcode as a title.

#### TRANSFER TOKENS

`contract-call` is the equivalent of `TRANSFER_TOKEN`, and as this
opcode, it can only be called within very specific constraints,
enforced by Michelson to make some classes of error harder to write:
It cannot be in a function, and no variable existing before the call
canbe used after.

    contract-call: ∀ param result: contract param result → param → tez  → result

#### Other primitives TODO

    type zero     = (+)
    type unit     = (*)
    type option a = None+Somea
    type bool     = False + True
    type list a   = Nil + Cons (a * (list a))
    type account  = (contract unit unit)

    val contract-call           :: ∀ param result:
        contract param result -> param -> tez -> result
    val contract-create         :: ∀ param storage result:
        key -> option key -> bool -> bool -> tez ->
        (param * storage) -> (result * storage) -> storage -> contract param result
    val contract-create-account :: key -> option key -> bool -> tez -> account
    val contract-get            :: key -> account
    val contract-manager        :: ∀ param storage: contract param storage -> key

    val crypto-check :: key -> sig -> string -> bool
    val crypto-hash  :: ∀ a: a -> string

    val fail :: fail

    val list-map    :: ∀ a b: (a -> b) -> list a -> list b
    val list-reduce :: ∀ a acc: (a -> acc -> acc) -> list a -> acc -> acc

    val map-empty  :: ∀ k v: map k v
    val map-get    :: ∀ k v: k -> map k v -> option v
    val map-map    :: ∀ k v0 v1: (k -> v0 -> v1) -> map k v0 -> map k v1
    val map-mem    :: ∀ k v: k -> map k v -> bool
    val map-reduce :: ∀ k v acc: (k -> v -> acc -> acc) -> map k v -> acc -> acc
    val map-update :: ∀ k v: k -> option v -> map k v -> map k v

    val self-amount         :: tez
    val self-balance        :: tez
    val self-contract       :: ∀ param result: contract param result
    val self-now            :: time
    val self-source         :: ∀ param result: contract param result
    val self-steps-to-quota :: nat

    val set-empty  :: ∀ elt: set elt
    val set-map    :: ∀ a b: (a -> b) -> set a -> set b
    val set-mem    :: ∀ elt: set elt -> elt -> bool
    val set-reduce :: ∀ elt acc: (elt -> acc -> acc) -> set elt -> acc -> acc
    val set-update :: ∀ elt: elt -> bool -> set elt
