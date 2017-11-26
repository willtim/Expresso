# ☕ Expresso

A simple expressions language with polymorphic extensible row types.


## Introduction

Expresso is a minimal statically-typed functional programming language, designed with embedding and/or extensibility in mind.
Possible use cases for such a minimal language include configuration (à la Nix) or as a starting point for a custom external DSL.

Expresso has the following features:

- A small and simple implementation
- Statically typed with full type inference
- Structural typing with extensible records and variants
- Lazy evaluation
- Convenient use from Haskell (a type class for marshalling values)
- Nix-style lambda syntax
- Built-in support for ints, double, bools, chars, maybes and lists


## Installation

Expresso the library and executable (the REPL) is currently built and tested using cabal.


## Records

Expresso records are built upon row-types with row extension as the fundamental primitive. This gives a very simple and easy-to-use type system when compared to more advanced systems built upon concatenation as a primitive. However, even in this simple system, concatenation can be encoded quite easily using difference records.

Records can of course contain arbitrary types and be arbitrarily nested. They can also be compared for equality. The dot operator (select) is used to project out values.

    Expresso REPL
    Type :help or :h for a list of commands
    Loaded Prelude from /home/tim/Expresso/Prelude.x
    λ> {x = 1}.x
    1
    λ> {x = {y = "foo"}, z = [1,2,3]}.x.y
    "foo"
    λ> {x = 1, y = True} == {y = True, x = 1}
    True


### Record extension

Records are eliminated using selection `.` and introduced using extension `|`. For example, the record literal:

    {x = 1, y = True}

is really sugar for:

    {x = 1 | { y = True | {}}}

The row types use lacks constraints to prohibit overlapping field names. For example, the following is ill-typed:

    {x = 1, x = 2} -- DOES NOT TYPE CHECK!

    let r = {x = "foo"} in {x = "bar" | r} -- DOES NOT TYPE CHECK!

The lacks constraints are shown when printing out inferred row types via the REPL, for example:

    λ> :type r: {x = 1 | r}
    forall r1. (r1\x) => {r1} -> {x : Int | r1}

In the above output, the REPL reports that this lambda can take a record with underlying row-type `r1`, providing `r1` satisfies the constraint that it does not have a field `x`.

The type of a literal record is *closed*, in that the set of fields is fully known:

    λ> :type {x = 1}
    {x : Int}

However, we permit records with redundant fields as arguments to functions, by inferring *open* record types:

    λ> let sqmag = {x, y}: x*x + y*y
    λ> :type sqmag
    forall a1 r2. (Num a1, r2\x\y) => {x : a1, y : a1 | r2} -> a1

An open record type is indicated by a row-type in the tail of the record.

Note that the function definition for `sqmag` above makes use of field punning. We could have alternatively written:

    λ> let sqmag = r: r.x*r.x + r.y*r.y


### Record restriction

We can remove a field by using the restriction primitive `\`. For example, the following will type-check:

    {x = 1 | {x = 2}\x}

We can also use the following syntactic sugar, for such an override:

    {x := 1 | {x = 1}}


### Records as modules

Records can be used as a simple module system. For example, imagine a module `"List.x"` with derived operations on lists:

    let
        intercalate = xs: xss: concat (intersperse xs xss);
        ...

    -- Exports
    in { intercalate
       , ...
       }

Such a module can be imported using a `let` declaration:

    λ> let list = import "List.x"
    λ> :type list.intercalate
    forall a1. [a1] -> [[a1]] -> [a1]

Or simply:

    λ> let {..} = import "List.x"

The biggest limitation is that records with polymorphic functions cannot be passed as lambda arguments without Rank2 polymorphism. Records must also not refer to themselves, as Expresso does not support type-level recursion.


### Difference records and concatenation

To encode concatenation, we can use functions that extend records and compose them using straightforward function composition:

    let f = (r:{ x = "foo", y = True |r}) >> (r:{ z = "bar" |r})

Expresso has a special syntax for such "difference records":

    λ> let f = {| x = "foo", y = True |} >> {| z = "bar" |}
    λ> f {}
    {z = "bar", x = "foo", y = True}

Concatenation is asymmetric whenever we use overrides, for example:

     {| x = "foo" |} >> {| x := "bar" |} -- Type checks
     {| x = "foo" |} << {| x := "bar" |} -- DOES NOT TYPE CHECK!


## Variants

The dual of records are variants, which are also polymorphic and extensible since they use the same underlying row-types.
Variants are introduced via injection (the dual of record selection), for example:

    λ> Foo 1
    Foo 1

Unlike literal records, literal variants are *open*.

    λ> :type Foo 1
    forall r1. (r1\Foo) => <Foo : Int | r1>

Variants are eliminated using the case construct, for example:

    λ> case Foo 1 of { Foo x: x, Bar{x,y}: x+y }
    1

The above case expression eliminates a *closed* variant, meaning any value other than `Foo` or `Bar` with their expected payloads would lead to a type error. To eliminate an *open* variant, we use a syntax analogous to extension:

    λ> let f = x: case x of { Foo x: x, Bar{x,y}: x+y | otherwise: 42 }
    λ> f (Baz{})
    42

Here the unmatched variant is bound to a variable (i.e. `otherwise`) and can be either ignored or delegated to another function.

The dual of record restriction is variant embedding. This allows us to restrict the behaviour exposed by a case expression, by exploiting the non-overlapping field constraints.
For example, to prevent use of the `Bar` alternative of function `f` above, we can define a new function `g` as follows:

    λ> let g = x: f (<|Bar|> x)
    λ> :type g
    forall r1. (r1\Bar\Foo) => <Foo : Int | r1> -> Int

Embedding is used internally to implement overriding alternatives, for example:

    λ> let g = x: case x of { override Foo x: x + 1 | x': f x' }

is sugar for:

    λ> let g = x: case x of { Foo x: x + 1 | x': f (<|Foo|> x') }

    λ> :type g
    forall r1 r2. (r1\x\y, r2\Bar\Foo) => <Foo : Int, Bar : {x : Int, y : Int | r1} | r2> -> Int


## Lazy evaluation

Expresso uses lazy evaluation in the hope that it might lead to efficiency gains when working with large nested records.

    λ> :peek {x = "foo"}
    {x = <Thunk>}


## Turing equivalence?

Turing equivalence is introduced via a single `fix` primitive, which can be easily removed or disabled.
`fix` can be useful to achieve open recursive records and dynamic binding (à la Nix).

        λ> let r = mkOverridable (self: {x = "foo", y = self.x ++ "bar"})
        λ> r
        {override_ = <Lambda>, x = "foo", y = "foobar"}

        λ> override r {| x := "baz" |}
        {override_ = <Lambda>, x = "baz", y = "bazbar"}
