module Plutarch.Optics.PPair where

import Plutarch.Core

import Plutarch.CPS.Optics.Lens

pfst ::
  (ESOP edsl, IsEType edsl a, IsEType edsl a', IsEType edsl b) =>
  CLens
    r
    (Term edsl (EPair a b))
    (Term edsl (EPair a' b))
    (Term edsl a)
    (Term edsl a')
pfst =
  clens
    (\tp -> return $ ematch tp \(EPair a _) -> a)
    (\ts a' -> return $ ematch ts \(EPair _ b) -> econ $ EPair a' b)

psnd ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  CLens
    r
    (Term edsl (EPair a b))
    (Term edsl (EPair a b'))
    (Term edsl b)
    (Term edsl b')
psnd =
  clens
    (\tp -> return $ ematch tp \(EPair _ b) -> b)
    (\ts b' -> return $ ematch ts \(EPair a _) -> econ $ EPair a b')
