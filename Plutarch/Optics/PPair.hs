module Plutarch.Optics.PPair where

import Fresnel.Lens

import Plutarch.Core

pfst_ ::
  (ESOP edsl, IsEType edsl a, IsEType edsl a', IsEType edsl b) =>
  Lens
    (Term edsl (EPair a b))
    (Term edsl (EPair a' b))
    (Term edsl a)
    (Term edsl a')
pfst_ =
  lens
    (\tp -> ematch tp \(EPair a _) -> a)
    (\ts a' -> ematch ts \(EPair _ b) -> econ $ EPair a' b)

psnd_ ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  Lens
    (Term edsl (EPair a b))
    (Term edsl (EPair a b'))
    (Term edsl b)
    (Term edsl b')
psnd_ =
  lens
    (\tp -> ematch tp \(EPair _ b) -> b)
    (\ts b' -> ematch ts \(EPair a _) -> econ $ EPair a b')