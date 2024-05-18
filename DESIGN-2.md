We desire to build an eDSL in Haskell.

The eDSL has two parts:
- The underlying representation for terms, the tools to manipulate
  them, to create them, to interpret them.
- The user-facing interface for writing programs in it.

We embed it in Haskell, albeit many of the techniques mentioned here
could be used in other languages as well.

Consider first the untyped perspective.
We can model the representation as a constructor with arbitrary fields,
literals, subterms, or nothing.
For example, an addition program might look like the following:
```
lam (add (var 0) (var 0))
```
How we interpret it would be up to us.
In many ways it's an extensible IR.

Let us first solve the first part, as the second part is mostly independent of this first one.

# FIXME
---
An "obvious" approach for Haskellers might be the tagless final approach,
yet that is not what we attempt to do here.
In the tagless final approach, the constructor above would be replaced by function
calls.
This is quite efficient, and should be just as powerful, but we wish
to inspect the _concrete_ AST later, such that we can deduplicate terms
efficiently.
---

# The Term language

Each constructor takes some amount of (sub)nodes and produces a node.

We wish to _type_ these constructors accurately, such that only correct ASTs can be produced.
