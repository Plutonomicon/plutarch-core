# Plutarch

We want an extensible AST.
"Embedded definitions" are definitions
where the meaning is expressed as an AST, not as code that does something.

What is an extensible AST?
What is an AST?
An AST has syntax nodes and leaves.
An extensible AST means we can define new syntax nodes and leaves.
An extensible AST means we can operate over a term of a partially known AST.

What is a node?
A node takes subnodes and possibly extra data.
What subnodes are valid? As expressive as needed, but as restrictive as needed.
Imagine we have a node that can only be used a finite number of times.
This is also a valid node.
Imagine we have a node that only takes subnodes that represent expressions of specific types.
This is also a valid node.
