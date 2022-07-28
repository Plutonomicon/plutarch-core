{-# LANGUAGE AllowAmbiguousTypes #-}

module Plutarch.Optics.PEither where

import Plutarch.CPS.Profunctor
import Plutarch.CPS.Prism

import Plutarch.Core

_PLeft ::
  forall edsl a a' b.
  (ESOP edsl, IsEType edsl a, IsEType edsl a', IsEType edsl b) =>
  CPSPrism
    (Term edsl (EEither a b))
    (Term edsl (EEither a' b))
    (Term edsl a)
    (Term edsl a')
_PLeft = cpsPrism pleft _

t :: (ESOP edsl, IsEType edsl a, IsEType edsl  b) => Term edsl (EEither a b) -> (forall c. (Term edsl (EEither a b) -> Term edsl c) -> (Term edsl a -> Term edsl c) -> (IsEType edsl c => Term edsl c))
t te l r = ematch te \case
  ELeft a -> r a
  ERight b -> l $ pright b

type PEither a b = forall edsl c. IsEType edsl c => (a -> Term edsl c) -> (b -> Term edsl c) -> Term edsl c