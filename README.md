### Contributing

`nix develop -f shell.nix -c cabal repl`

`nix run .#regen` to fix formatting and `plutarch-core.nix`

### About

Plutarch (2) is an eDSL framework for Haskell, that essentially gives you
embedded data types.
That is:
- You can declare embedded data types.
- You can interpret these data types in many ways (they are like HKDs).
- You can support arbitrary data types by mapping them onto "core" data types
  using "representations" (see `EIsRepr`).

The rest is mostly tooling around this. For example, optics, common
backend tooling, example backends.

AFAICT the techniques employed in Plutarch 2 are novel, but I might be wrong.
Notably, we don't use TH magic. It's all pure Haskell, with many quantified constraints.

The core design of Plutarch 2 has been settled.
That is, `Plutarch.Core` and `Plutarch.EType` are unlikely to change.
One missing feature is supporting arbitrary data kinds at the type-level,
however, it is not yet clear if this is possible without type-level generic `to` and `from`.

I originally designed Plutarch 1 for generating [UPLC](https://well-typed.com/blog/2022/08/plutus-cores/) for Cardano.
Plutarch 2 is generic, and isn't Cardano-specific in any way. This repository contains no references to anything
Cardano-related besides this README.

### Contact, support, further information

We have a channel in the following Discord (unfortunately, but we're using GH anyway...)
guild for Plutonomicon: https://discord.gg/722KnTC8jF
However, this is mostly Cardano-related, so you might feel out of place.

Feel free to ask questions via GH issues, or even send me an e-mail.
