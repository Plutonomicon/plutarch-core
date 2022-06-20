# Overview

A specification is a mathematical (unordered) set of diagrams (unrelated to category theory).

There are some core operations defined over diagrams, from the EPSL type class.

Diagrams denote what transactions should be accepted.
Diagrams are of a specific protocol `p`.
Diagrams form a monoid.
The empty diagram matches no transactions.
The monoidal operation combines the predicates.
Any inputs of `p` in the transaction should be in the diagram, and vice versa.
Any mint of `p` in the transaction should be in the diagram, and vice versa.

The value of inputs and outputs must match exactly.

Given the properties of the specification language,
we have the property, that two transactions with the same validity range that only
interact with disjoint protocols, can be merged (if the signatures can be redone),
such that the merged transaction has the same effect on the protocol state of all
involved protocols.

## Predicates

### `requireInput`

The input (of another protocol) in question **must** be in the transaction.

### `requireOwnInput`

The input (of `p`) in question **must** be in the transaction.

### `createOwnOutput`

The output (of `p`) must exist.

### `witnessOutput`

The output (of another protocol) must exist.

### `createOutput`

The output (of another ptocol) must be created.
Another diagram of a different protocol can not share
the same created output with `createOutput`.

### `mintOwn`

The token name (of `p`) and amount must be exactly present
in the transaction.
No more or no less must be minted.

### `witnessMint`


