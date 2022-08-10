{-# LANGUAGE AllowAmbiguousTypes #-}

module Plutarch.Optics.PEither where

import Plutarch.CPS.Optics.Prism

import Control.Monad.Cont
import Plutarch.Core

_PLeft ::
  (ESOP edsl, IsEType edsl a, IsEType edsl a', IsEType edsl b, IsEType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (EEither a b))
    (Term edsl (EEither a' b))
    (Term edsl a)
    (Term edsl a')
_PLeft =
  cprism
    (return . pleft)
    ( \te -> cont \f -> ematch te \case
        ELeft a -> f . Right $ a
        ERight b -> f . Left $ pright b
    )

_PRight ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b', IsEType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (EEither a b))
    (Term edsl (EEither a b'))
    (Term edsl b)
    (Term edsl b')
_PRight =
  cprism
    (return . pright)
    ( \te -> cont \f -> ematch te \case
        ELeft a -> f . Left $ pleft a
        ERight b -> f . Right $ b
    )
