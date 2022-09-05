module Plutarch.Optics.PPair where

import Plutarch.Core

import Plutarch.CPS.Optics.Lens

pfst ::
  (PSOP edsl, IsPType edsl a, IsPType edsl a', IsPType edsl b) =>
  CLens
    r
    (Term edsl (PPair a b))
    (Term edsl (PPair a' b))
    (Term edsl a)
    (Term edsl a')
pfst =
  clens
    (\tp -> return $ pmatch tp \(PPair a _) -> a)
    (\ts a' -> return $ pmatch ts \(PPair _ b) -> pcon $ PPair a' b)

psnd ::
  (PSOP edsl, IsPType edsl a, IsPType edsl b, IsPType edsl b') =>
  CLens
    r
    (Term edsl (PPair a b))
    (Term edsl (PPair a b'))
    (Term edsl b)
    (Term edsl b')
psnd =
  clens
    (\tp -> return $ pmatch tp \(PPair _ b) -> b)
    (\ts b' -> return $ pmatch ts \(PPair a _) -> pcon $ PPair a b')
