# Abstract / Design of Plutarch

This is meant to be a long-form stream-of-thought description of the design of Plutarch
and the reasoning behind it.

Plutarch is at its core an eDSL framework. The goal is to have some way of defining
_embedded_ definitions in Haskell that you can then introspect,
translating them into executable forms if so needed.
The type of the embedded definition should notably declare its _language_.
Does it use arbitrary polymorphism? Does it use integers? Does it use IO? Does it use non-linear functions?
Given these in the type, we should then be able to compose embedded definitions, resulting in a new
type that is morally the intersection of the constituents.

The core challenges are the following:
- [Avoiding duplication of top-level definitions](#avoiding-duplication-of-top-level-definitions)
- [Preserving type information](#preserving-type-information)
- [Supporting custom data types (and their optics/operations)][#supporting-custom-data-types]
- [Ergonomic syntax](#ergonomic-syntax)
- [Supporting embedding other languages](#supporting-indexed-languages)
  + Supporting de-Bruijn-indexed variables
  + Supporting linearity
  + Supporting singletons

We call the embedded definition a _term_.
We call the act of transforming a term into something usable _interpretation_.
It is also possible to do a _partial interpretation_, where only part of the language
of the term is _removed_ and possibly transformed into something else. For example,
you can transform a term that uses the lambda calculus into a term that uses the SKI
calculus, without affecting the other parts of the term.

Given this, it should be possible to write programs in Haskell for whatever platform
you target. It would be possible to make an interpreter for a term in the simply typed lambda
calculus that turns it into C code, a la [Compiling to Categories][compiling-to-categories].

How do we achieve such a design?

# Design decisions

## Avoiding duplication of top-level definitions

In Haskell-land:
```haskell
f :: A -> B

g :: (A, A) -> (B, B)
g (x, x) = (f x, f x)
```

The above when compiled by GHC does not duplicate `f`. In an eDSL, this would naively
be duplicated as `g` references the _AST_ of `f` in its definition, not its `name`.
This is a fundamental challenge of eDSLs in Haskell.
One possible solution is to refrain from referencing definitions directly, rather referencing
their names, then at the top-level map names to definitions.
This is quite manual.

The approach taken by Plutarch is to hoist embedded _closed_ terms to the top-level and deduplicate them.
This can be done by hashing the terms and using [stable names][stable-names]. Without using stable names, `f` would still
be hashed twice. In a large enough program, the interpretation (not the output) would be inefficient
due to the large amount of processing done on duplicated top-level terms, even though they are deduplicated later.
The approach taken in Plutarch 1 is to embed the processing of the terms in the definition of the term itself,
which is possible since there is only one possible interpretation.
If we are to allow arbitrary interpretations, the way to avoid this is to use stable names to detect
equivalent thunks to deduplicate the processing of the term in addition to the term itself.

## Preserving type information

Assume we are targetting a typed output format, for example, we are generating C code and
we need to know the sizes of the types involved. Given a term, often we can infer the types
involved, but to ensure that we always have type information, the concept of type information
must be made explicit. In general, to interpret a term of type `a`, we must also have the type
information for type `a`.

## Supporting custom data types

Toy eDSLs in Haskell often forgo data type support entirely. Indeed, you need nothing more than
support for products and sums, but this is hardly ergonomic.
Optimally we would want to support arbitrary data types, including matching and constructing them.
The trick used in Plutarch is to use a pattern reminiscent of HKDs of the following form:
`type PType = (PType -> Type) -> Type`
It is weirdly recursive (and indeed the definition as-is is illegal Haskell), but it turns
out to be surprisingly useful. Rather than doing `data Pair a b = MkPair a b`, you do
`data PPair a b f = MkPair (f a) (f b)`. `f` can be instantiated such that functions
like `pcon` and `pmatch` can exist.

## Ergonomic syntax

### Combinators and overloaded record dot

This is the approach uses in Plutarch 1. Application turns from `f x` into `f # x`,
abstraction from `\x y z -> w` into `plam \x y z -> w`, construction from `A x` to `pcon $ A x`,
`A $ B x` into `pcon $ A $$ B x`,
matching from `case x of A y -> z` into `pmatch x \case A y -> z`, and record access stays the same.

This seems usable to a large extent, but this doesn't work well with for example view-patterns,
nor nested pattern matching.

To a large extent it seems possible to aleviate this with optics.

### `proc`-notation / Arrow syntax

It should be possible to use Arrow notation to write terms, using a plugin like [`overloaded`][overloaded].
It would be best if the plugin could somehow supported qualified `proc`-notation, such that you can choose
the functions used for the desugaring. The type classes predefined in `overloaded` are not
generic enough, as you can't assign them arbitrary types. If they were, you'd run into the problem of
type inference struggling, hence why explicitly noting the "language" you're working with seems to be
the solution a la qualified `do`-notation.

You could possibly integrate the plugin into GHC itself as it's not Plutarch-specific.

### Converting Haskell definitions into terms using Template Haskell

This is similar to what [plutus-tx][plutus-tx] from the Cardano ecosystem does.
It is not clear (to me, Las) when a plugin is needed.
If you use the GHC Core from the definition, you would turn it into a term of a language
that mimics GHC Core. If you can somehow operate on the AST directly, without including
quoting the definition, you could interpret it in arbitrary languages constrained by what
Haskell features it uses.

In either case, there is the question of how to handle uses of external definitions in
the definition. If they are accessible, they could be translated into a term too.
For external definitions that are not INLINABLE, this is impossible.
Rather than using external Haskell definitions, it seems feasible to interpret terms
as Haskell definitions, use that in the definition, then the TH code could "uninterpret"
the term in the definition trivially, and reference it directly.

### Overloaded application / lambda abstractions

This would allow you to write terms in a "direct" style. However, it seems this would
be problematic wrt. type inference. Perhaps something like "qualified application/abstraction"
would fit, but what about when you want to embed Haskell-level applications? Perhaps something like
idiom brackets would fit better.

[compiling-to-categories]: http://conal.net/papers/compiling-to-categories/
[overloaded]: https://hackage.haskell.org/package/overloaded
[stable-names]: https://hackage.haskell.org/package/base-4.16.0.0/docs/src/GHC.StableName.html

## Supporting embedding other languages

Given example languages as the following:
```haskell
data Arith :: Language where
  Add :: t (Expr a) -> t (Expr a) -> Arith t (Expr a)
  Lit :: Int -> Arith t (Expr PInt)

data HasArith :: Language where
  HasArith :: t a -> Arith t a
```
We wish for `HasArith` to somehow support in its child node
the `Arith` language in addition to the existing languages.

We need not only this, but the ability to arbitrarily control how
term are annotated with languages, the ability to remove them,
concatenate them, and so on.

Through this, we can model linearly-captured variables for use in linear
lambda abstractions.

# Implementation

`Term` takes a list of languages and a tag.
Each language defines a list of constructors, each of a tag.
When you make a term, it only includes the language of the constructor you used.
Some languages support being added arbitrarily, others don't.
You can make terms from other terms by reordering the list of languages in the term.
The index of each language in the _language stack_ is distinct and used.
Each language must implement a type class to support the operations necessary.

Partial interpretation happens bottom-up as a fold. State gets pushed up along with the term,
the tag of the term must not change. Work on the same thunk is deduplicated if the thunk
is marked using a special marker function.

Final interpretation, turning the term into something that is not a term, is also done by a fold,
albeit no transformed term is bubbled up.

Deduplicating common top-level definitions at the final step happens by hashing everything,
and mapping uses of closed terms to the variable name assigned.
