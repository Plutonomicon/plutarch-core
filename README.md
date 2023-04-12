### Contributing

`nix develop -f shell.nix -c cabal repl`

`nix run .#regen` to fix formatting and `plutarch-core.nix`

### Status

Plutarch (2) is currently very much still a WIP.

The first backend that will be focused on is likely Untyped Plutus Core, due to
demand from users.

A C backend will likely be the next.

### About

Plutarch (2) aims to be an eDSL framework.
Given a task, it is practice to make an ad-hoc eDSL for that task,
Accelerate, Clash, Plutarch 1, etc.

Approaches like Compiling with Categories exist, but this still falls short.
We lack _interoperability_, and _freedom_.

An eDSL often has functions, but not always. It will very often
not support the full feature set of Haskell (and if it did, you could instead
translate STG to your backend!).
We wish to type these limitations.

Plutarch (2) is the (WIP) result of over a year of research and pondering,
aiming to solve all these issues.

There are many small novel contributions, albeit the biggest one is `Term`.
It looks like `Free`, but without `Pure`.
It supports reordering, and _partial_ reinterpretation (!), without sacrificing
support for **linearity**.
It is very powerful.

Other small ideas include eDSL-level optimisations, top-level common expression elimination
through hashing, avoiding redoing work through sharing thunks, supporting normal ADTs
through Generics and a recursive HKD-like construction, each of which might be of
independent interest too.

### Contact, support, further information

We have a channel in the following Discord (unfortunately, but we're using GH anyway...)
guild for Plutonomicon: https://discord.gg/722KnTC8jF
However, this is mostly Cardano-related, so you might feel out of place.

Feel free to ask questions via GH issues, or even send me an e-mail.
