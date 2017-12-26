# ☕ Expresso

A simple expressions language with polymorphic extensible row types.


## Introduction

Expresso is a minimal statically-typed functional programming language, designed with embedding and/or extensibility in mind.
Possible use cases for such a minimal language include configuration (à la Nix), data exchange (à la JSON) or even a starting point for a custom external DSL.

Expresso has the following features:

- A small and simple implementation
- Statically typed with type inference
- Structural typing with extensible records and variants
- Lazy evaluation
- Convenient use from Haskell (a type class for marshalling values)
- Haskell-inspired syntax
- Type annotations to support first-class modules and schema validation use cases
- Built-in support for ints, double, bools, chars, maybes and lists

## Installation

Expresso the library and executable (the REPL) is currently built and tested using cabal.

## Functions

Expresso is a functional language and so we use lambda terms as our basic means of abstraction. To create a named function, we simply bind a lambda using let. I toyed with the idea of using Nix-style lambda syntax, e.g. `x: x` for the identity function, but many mainstream languages, not just Haskell, use an arrow to denote a lambda term. An arrow is also consistent with the notation we use for types.
Expresso therefore uses the arrow `->` to denote lambdas, with the parameters to bind on the left and the expression body on the right, for example `x -> x` for identity.

Note that multiple juxtaposed arguments is sugar for currying. For example:

    f x -> f x

is the same as:

    f -> x -> f x

The function composition operators are `>>` and `<<` for forwards and backwards composition respectively.


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

Note that records cannot refer to themselves, as Expresso does not support type-level recursion.

### Record extension

Records are eliminated using selection `.` and introduced using extension `|`. For example, the record literal:

    {x = 1, y = True}

is really sugar for:

    {x = 1 | { y = True | {}}}

The row types use lacks constraints to prohibit overlapping field names. For example, the following is ill-typed:

    {x = 1, x = 2} -- DOES NOT TYPE CHECK!

    let r = {x = "foo"} in {x = "bar" | r} -- DOES NOT TYPE CHECK!

The lacks constraints are shown when printing out inferred row types via the REPL, for example:

    λ> :type r -> {x = 1 | r}
    forall r. (r\x) => {r} -> {x : Int | r}

In the above output, the REPL reports that this lambda can take a record with underlying row-type `r`, providing `r` satisfies the constraint that it does not have a field `x`.

The type of a literal record is *closed*, in that the set of fields is fully known:

    λ> :type {x = 1}
    {x : Int}

However, we permit records with redundant fields as arguments to functions, by inferring *open* record types:

    λ> let sqmag = {x, y} -> x*x + y*y
    λ> :type sqmag
    forall a r. (Num a, r\x\y) => {x : a, y : a | r} -> a

An open record type is indicated by a row-type in the tail of the record.

Note that the function definition for `sqmag` above makes use of field punning. We could have alternatively written:

    λ> let sqmag = r -> r.x*r.x + r.y*r.y

### Record restriction

We can remove a field by using the restriction primitive `\`. For example, the following will type-check:

    {x = 1 | {x = 2}\x}

We can also use the following syntactic sugar, for such an override:

    {x := 1 | {x = 1}}

### First-class modules

Records can be used as a simple but powerful module system. For example, imagine a module `"List.x"` with derived operations on lists:

    let
        reverse     = foldl (xs x -> x :: xs) [];
        intercalate = xs xss -> concat (intersperse xs xss);
        ...

    -- Exports
    in { reverse
       , intercalate
       , ...
       }

Such a module can be imported using a `let` declaration:

    λ> let list = import "List.x"
    λ> :type list.intercalate
    forall a. [a] -> [[a]] -> [a]

Or simply:

    λ> let {..} = import "List.x"

Records with polymorphic functions can be passed as lambda arguments and remain polymorphic using *higher-rank polymorphism*. To accomplish this, we must provide Expresso with a suitable type annotation of the argument. For example:

    let f = (m : forall a. { reverse : [a] -> [a] |_}) ->
                {l = m.reverse [True, False], r = m.reverse "abc" }

The function `f` above takes a "module" `m` containing a polymorphic function `reverse`. We annotate `m` with a type by using a single colon `:` followed by the type we are expecting.
Note the underscore `_` in the tail of the record. This is a *type wildcard*, meaning we have specified a *partial type signature*. This type wildcard allows us to pass an arbitrary module containing a `reverse` function with this signature. To see the full type signature of `f`, we can use the Expresso REPL:

    λ> :t f
    forall r. (r\reverse) => (forall a. {reverse : [a] -> [a] | r}) ->
        {l : [Bool], r : [Char]}

Note that the `r`, representing the rest of the module fields, is a top-level quantifier. The type wildcard is especially useful here, as it allows us to avoid creating a top-level signature for the entire function and explicitly naming this row variable. More generally, type wildcards allow us to leave parts of a type signature unspecified.

Function `f` can now of course be applied to any module satisfying the type signature:

    λ> f (import "Prelude.x")
    {l = [False, True], r = "cba"}


### Difference records and concatenation

To encode concatenation, we can use functions that extend records and compose them using straightforward function composition:

    let f = (r -> { x = "foo", y = True | r}) >> (r -> { z = "bar" | r})

Expresso has a special syntax for such "difference records":

    λ> let f = {| x = "foo", y = True |} >> {| z = "bar" |}
    λ> f {}
    {z = "bar", x = "foo", y = True}

Concatenation is asymmetric whenever we use overrides, for example:

     {| x = "foo" |} >> {| x := "bar" |} -- Type checks
     {| x = "foo" |} << {| x := "bar" |} -- DOES NOT TYPE CHECK!

### The Unit type

The type `{}` is an example of a *Unit* type. It has only one inhabitant, the empty record `{}`:

    λ> :type {}
    {}


## Variants

The dual of records are variants, which are also polymorphic and extensible since they use the same underlying row-types.
Variants are introduced via injection (the dual of record selection), for example:

    λ> Foo 1
    Foo 1

Unlike literal records, literal variants are *open*.

    λ> :type Foo 1
    forall r. (r\Foo) => <Foo : Int | r>

Variants are eliminated using the case construct, for example:

    λ> case Foo 1 of { Foo x -> x, Bar{x,y} -> x+y }
    1

The above case expression eliminates a *closed* variant, meaning any value other than `Foo` or `Bar` with their expected payloads would lead to a type error. To eliminate an *open* variant, we use a syntax analogous to extension:

    λ> let f = x -> case x of { Foo x -> x, Bar{x,y} -> x+y | otherwise -> 42 }
    λ> f (Baz{})
    42

Here the unmatched variant is passed to a lambda (with `otherwise` as the parameter). The expression after the bar `|` typically either ignores the variant or delegates it to another function.

### Variant embedding

The dual of record restriction is variant embedding. This allows us to restrict the behaviour exposed by a case expression, by exploiting the non-overlapping field constraints.
For example, to prevent use of the `Bar` alternative of function `f` above, we can define a new function `g` as follows:

    λ> let g = x -> f (<|Bar|> x)
    λ> :type g
    forall r. (r\Bar\Foo) => <Foo : Int | r> -> Int

Embedding is used internally to implement overriding alternatives, for example:

    λ> let g = x -> case x of { override Foo x -> x + 1 | f }

is sugar for:

    λ> let g = x -> case x of { Foo x -> x + 1 | <|Foo|> >> f }

    λ> :type g
    forall r1 r2. (r1\x\y, r2\Bar\Foo) => <Foo : Int, Bar : {x : Int, y : Int | r1} | r2> -> Int

### The Void type

Internally, the syntax to eliminate a closed variant uses the empty variant type `<>`, also known as *Void*. The Void type has no inhabitants, but we can use it to define a function `absurd`:

    λ> :type absurd
    forall a. <> -> a

Absurd is an example of *Ex Falso Quodlibet* from classical logic (anything can be proven using a contradiction as a premise).

As an example of the above, the following closed case expression:

    case x of { Foo{} -> 1, Bar{} -> 2 }

is actually sugar for:

    case x of { Foo{} -> 1 | x' -> case x' of { Bar{} -> 2 | absurd } }


## A data-exchange format with schemas

We could use Expresso as a lightweight data-exchange format (i.e. JSON with types). But how might be validate terms against a schema?

A simple type annotation `<term> : <type>` , will not suffice for "schema validation". For example, consider this attempt at validating an integer against a schema that permits everything:

    1 : forall a. a        -- FAILS

The above fails to type check since the left-hand-side is inferred as the most general type (here a concrete int) and the right-hand-side must be less so.

Instead we need something like this:

    (id : forall a. a -> a) 1

A nice syntactic sugar for this is a *signature section*, although the version in Expresso is slightly different from the Haskell proposal. We write `(:T)` to mean `id : T -> T`, where any quantifiers are kept at the top-level. We can now use:

    (: forall a. a) 1

If we really do have places in our schema where we want to permit arbitrary data, we should use the equality constraint to guarantee the absence of partially-applied functions. For example:

    (: forall a. Eq a => { x : <Foo : Int, Bar : a> }) { x = Bar id }

would fail to type check. But the following succeeds:

    λ> (: forall a. Eq a => { x : <Foo : Int, Bar : a> }) { x = Bar "abc" }
    {x = Bar "abc"}


## Lazy evaluation

Expresso uses lazy evaluation in the hope that it might lead to efficiency gains when working with large nested records.

    λ> :peek {x = "foo"}
    {x = <Thunk>}


## Turing equivalence?

Turing equivalence is introduced via a single `fix` primitive, which can be easily removed or disabled.
`fix` can be useful to achieve open recursive records and dynamic binding (à la Nix).

    λ> let r = mkOverridable (self -> {x = "foo", y = self.x ++ "bar"})
    λ> r
    {override_ = <Lambda>, x = "foo", y = "foobar"}

    λ> override r {| x := "baz" |}
    {override_ = <Lambda>, x = "baz", y = "bazbar"}
