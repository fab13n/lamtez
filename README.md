lamtez: a typed lambda-calculus compiling to Tezos' Michelson VM
================================================================

This is a toy project, primarily intended to become familiar again
with OCaml, and to dive into Michelson while having fun. It is
released under MIT license, with no guaranty of any kind (among other,
there's no proof that it compiles to sound nor correct Michelson
code).

I'm interested in feedbacks anyway, if you play with it.

## Language

Lamtez is a typed lambda calculus, with some Hindley-Milner type
inference, the corresponding type polymorphism, sum and product types,
and native support for Michelson types and primitives.

Whitespaces are not significant except to separate tokens, indentation
is not significant, comment start with a `#` sign and run until the
end of the current line.

### Expression Syntax

#### Functions

Functions are represented as lambdas, with the backslask `\` standing
for the lambda character, and a colon `:` between parameters and
body. Several variables can be passed as parameters (it's then
currified/uncurrified as needed). Parameters can be either simple
names (and their type is then inferred) or explicited with the syntax
`(name: type)`.

TODO: I probably can't have polymorphic functions, because they
wouldn't typecheck in Michelson. Otherwise, explicit `Forall`
operators will be needed.

Examples:
```
\x: x
\x y: x + y
\(x: nat) (y:nat): x - y
\(x: nat) y: x * y
\amount parameter storage: ((), map-update parameter (Some amount) storage)
```

#### Variables

Variable names must start with a lowercase letter or an underscore;
they are allowed to contain a `-` character (might be used later to
implement some form of modularity).

Examples: `foo, bar0, contract-call, _foo, foo_bar, fooBar`

#### Function application

Functions are applied by putting an argument directly on its
right. Function application is left-associative, unless parentheses
are used to force it otherwise.  Function application binds tighter
than most things, including infix operators.

Examples:
```
f x
f(x)
f x y
(f(x)y)
f x + f y # Same as f(x) + f(y)
f (x + y) (x + z)
(\x: x + 1) 2
```

#### Let/in: local variables

ML-style local variables, `let x=a in b` evaluates `b` with `x` set to `a`.
Equivalent, execution-wise, to `(\x:b) a`.

Example:
```
let x = 32 in
let y = 10 in
x + y
```
#### Tuples (unlabelled cartesian products)

Whereas Michelson on supports pairs, Lamtez supports tuples of length
bigger than 2 (and encodes them as nested pairs). Such tuples are
surrounded with parentheses, and elements are separated with commas.

Elements are extracted from a tuple with the suffix `.n`, where `n` is
a litteral positive integer, 0-indexed. The extractor suffix binds
tighter than function application.

Examples:
```
let triplet = (32, 5, 5) in
triplet.0 + triplet.1 + triplet.2
```

#### (labelled) Cartesian products

For larger composite structures, it's easier to refer to individual
elements by labels rather than by number. This requires to declare a
product type before using it.  Labels are like identifiers except that
they start with a capital letter.

Type declarations happen at the beginning of the contract (cf. infra);
labelled product types are sequences of labels and types separated by
`*` symbols.

Litteral product types are sequences of labels and types, separated by
commas and surrounded by braces.

Access to product fields are made with a `.Label` suffix, which binds
as tightly as unlabelled product accessors.

Example:
```
type coordinates = Latitude int * Longitude int

let p = {Latitude 43500, Longitude 1500 } in
p.Latitude * p.Latitude + p.Longitude * p.Longitude
```

#### Sum types

Equivalent of labelled unions, they are a generalization of the
`Left|Right` Michelson operators with an arbitrary number of labels,
freely named.

Types have to be declared; they are declared the same way as products,
except that cases are separated with `+` instead of `*`.

Compared to ML, each case has one and only one associated value
type. Make it a `unit` if you don't use it, make it a tuple or a
product if you need several values.

Sum expressions are built with a label followed by an expression. It
binds as tightly as a function application.

Sum accessors, equivalent to ML's `match/with` or Michelson
`IF_LEFT/IF_RIGHT`, are of the form `expression ? Label_0 v_0: e_0 |
... | Label_n v_n: e_n`. As in ML, an optional `|` is tolerated after
the `?`. the variables `v_n` can be omitted when they're not used in
the corresponding `e_n`.

Booleans are encoded as `type bool = False unit | True unit`, so
if/then/else operations should be encoded as sum accessors, as shown
in the example below.

Examples:
```
type operation = Withdrawal tez + GetBalance unit + Deposit tez
\amount operation storage:
  ( operation ?
  | Withdrawal a: (None, storage - a)
  | GetBalance: (Some storage, storage)
  | Deposit: (None, storage + a)
  )

now > date ? True: "OK" | False: "Not yet"
```

#### Binary and unary operators

TODO

#### Literals

Lamtez supports the same literals as Michelson:

* integers and naturals are represented the same way: `123`, `-8` 
  (TODO: support `_` characters)
* dates are represented with the ISO format, without surrounding quotes: 
  `2017-08-22T22:00:00Z`, `2017-08-22T22:00:00+01:00` 
* Tez amounts are represented with a `tz` prefix and optional cents: 
  `tz1`, `tz1.00`, `tz.05` (TODO: support `_` characters)
* Signatures are represented with a `sig:` prefixing the base58 hash TODO
* Keys are represented with a `key:` prefixing the base58 hash TODO

#### Type annotations

TODO

### Type syntax

Types can be created at the beginning of the contract file. We've
already seen the syntax to create labelled product types `type name =
Label_0 field_type_0 * ... * Label_n field_type_n`, and sum types
`type name = Label_0 case_type_0 * ... * Label_n case_type_n`. Type
aliases can also be created, with the notation `type name = type`.

Type can be polymorphic, i.e. take type parameters. Beware, however,
that since Michelson is not polymorphic, some valid Lamtez programs
will be rejected by the compiler. Type parameters are passed between
the name and the `=` sign. Lists are encoded that way in Lamtez.

Examples:
```
type list a = None unit + Some a
type pair a b = (a * b)
type assoc_list k v = list (pair k v)
```

Type annotations can be the following:

* an identifier, i.e. the name of an alias, a sum type, a product type
  or a primitive.
* if an identifier is polymorphic, as the `list` example above, it
  must receive the corresponding number of parameters after it. For
  instance, `nat` is a valid type, so is `list int` or `list (pair
  string int)`, but `list` or `pair int` are not valid.
* Tuples are represented as types, separated with `*` and surrounded by
  parentheses, e.g. `(int * int)` or `(int*list a*tez)`.
* functions types are denoted `parameter_type -> result_type`. The
  arrow is right associative, and multi-parameter functions are
  encoded as curried (nested) lambda terms. For instance, a function
  from two ints to a string has type `int -> int -> string`.

### Contracts

A contract with parameter type `p`, storage type `s` and result type
`r` is represented in a file as a sequence of type definitions,
followed by an expression of type `tez -> p -> s -> (r * s)`. The
first parameter, of type `tez`, is the amount received by the contract
when called.

Example:
```
type operation = Withdrawal tez + GetBalance unit + Deposit tez
\amount operation storage:
  ( operation ?
  | Withdrawal a: (None, storage - a)
  | GetBalance: (Some storage, storage)
  | Deposit: (None, storage + a)
  )
```

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

```
contract-call: ∀ param result: param → tez  → contract param result → result
```

It is admissible to update the storage before calling a contract: this
is done with teh `contract-call-with-storage` variant, which takes an
updated storage as parameter and restores it after the contract
succeeds.

```
contract-call-with-storage: ∀ param result storage: 
  param → tez  → contract param result → storage -> result
```

## Michelson limitations

Some limmitations are directly imported from Michelson. Here are
some of the things ML users might take for granted but won't get
from a language of the Michelson family:

* no generic types, hence no let-polymorphism. You might have to
  add some type hints in order to compile to Michelson.

* Lambdas are not closures, so no partial evaluation.

* Functions are not first-class types, so no currying. Bundle
  multiple parameters as tuples instead.

* `TRANSFER_TOKENS` must be called from anempty stack, out of
  a lambda, and without `DI*P`-protected values. So the variables
  defined before `contract-call` cannot be used after it.
