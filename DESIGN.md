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

## Supporting custom (proper Haskell-level) data types

The goal is to be able to define data types the same way
you do it in Haskell.

This is still in-progress and is harder in the new design.
The old design was using a HKD-like construction,
but this is no longer possible since each subterm would
have a different type, meaning that you can not use the same
(functor-y) application for each subterm.
Seemingly a solution is to associate an index with each application,
but this seems horribly complex.

Possible solutions are using TH-magic to define the data types,
or having a magic SOP-like type and using newtypes over it,
with optics to operate over it.

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

```haskell
type Term :: [Language] -> Tag -> Type
```
The fundamental data type of importance.
The Term is not specialised to expressions, or any specific type
of AST node, instead it recognises that there are many types of AST
nodes beyond expressions. Not all languages are varants of the lambda calculus.
There are pure expressions, impure expressions, linearity, effects, variables,
type information, and more. Each of these can be represented as a tag.
The tag can be thought of as a _filter_ on the constructors possible,
the constructors of each constituent language.
Each index in the stack of languages is meaningful and distinct.
Languages can be _expansible_ and _contractible_.
To be expansible means to be addible unconditionally to the stack.
To be contractible means to be collapsible with another member of itself in the stack.
Both of these represent powers and freedoms that linearly bound variables do not have.
Necessarily, each member of the language stack is distinct and not necessarily unique.
We can have two instances of the same language, and explicitly choose which to use.
If contractible, we can interpret one in terms of the other (or equivalently, the opposite
way around). If expansible, we can pretend we use it when we don't.
This is similar to the structural rules of weakening and contraction.
Indeed, the stack of languages is itself _linear_. The languages are akin to the types
of the stack members in this eDSL at the type-level, each of which declares whether
it supports weakening and contraction. Notably, exchange is always supported.
In fact, we can arbitrarily reorder the members of the stack as fit.

Using a (constructor of a) language, morally similar to sending an effect
in an effect system, always appends an instance of the language to the stack.
Constructors have AST nodes as arguments, each of which has their own
(not necessarily unique) language stack. This is denoted by a list of stacks
in the type of the constructor. When "sent", the list is flattened, collapsing
it into one stack, but we retain the structure as run-time information to later
reconstruct.
Each embedded AST node can be of an _arbitrary_ language stack, enabling
embedding variables as languages. Indeed, linearly bound variables form their
own incontractible inexpansible language of variables. Linear lambdas prepend such
a language to the language stack of the body.

Given such a system, how do we interpret it? What is the meaning of a term
of a specific language stack? How do interpret only _part_ of the term, transforming
the languages in the stack? Can we, for example, turn HOAS into explicitly bound variables
without disturbing the other parts?
How do we share the work done on multiple appearances of the same node in the AST?
How do we recover the graph from the tree, while still enabling arbitrary interpretations?

The trick is to first notice that expansibility and contractibility isn't inherent.
They can be emulated as constructors of the language.
Then, because of linearity, interpretation becomes trivial:
Given a language `l` in a list of languages `ls`,
a term `Term ls tag` possibly holds a node of language `l`.
The interpretation function will be morally run only once (exceptions apply);
it will map a node of language `l` to a node of language `l'`.

What about interpreting multiple languages at once?
There is no such thing as a "multi-language node", so we necessarily
always handle a specific root language.
However, the node contains nested languages, some of which may be of interest.
We take this to the limit, and say that we can interpret `Term ls tag` into
`Term ls' tag`, with `Interpret ls ls'`, a list of interpreters, one for each
`l` & `l'` in `ls` & `ls'`.
Each interpreter must additionally map the nested languages from `ls` to `ls'` too.
A node can contain multiple subnodes, and nodes of different subsets of `ls`.
For each subnode, we choose a single interpretation function from `Interpret ls ls'`,
which transforms the node and its nested nodes/languages. If the node did not contain
some language, then it will not transform it either.

How do we recover the simple functionality of folding over a contractible language?
Contractibility itself represents a node, hence the interpreter will in that case
recurse without delegating the recursion elsewhere.
