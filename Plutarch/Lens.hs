module Plutarch.Lens where

import GHC.Generics

import Plutarch.Core
import Plutarch.EType (type (/$))

data PLens edsl a b
  = PLens
  { plget :: Term edsl b -> Term edsl a
  , plset :: Term edsl a -> Term edsl b -> Term edsl b
  }

_0 :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => PLens edsl a (EPair a b)
_0
  = PLens
  { plget = \tp -> ematch tp \(EPair a _) -> a
  , plset =
      \ta tp -> 
        ematch tp \(EPair _ b) ->
            econ $ EPair ta b
  }

_1 :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => PLens edsl b (EPair a b)
_1
  = PLens
  { plget = \tp -> ematch tp \(EPair _ b) -> b
  , plset =
      \tb tp -> 
        ematch tp \(EPair a _) ->
            econ $ EPair a tb
  }

data PMaybe a ef
  = PJust (ef /$ a)
  | PNothing
  deriving stock Generic
  deriving anyclass EIsNewtype

data PPrism edsl a b
  = PPrism
  { ppget :: Term edsl b -> Term edsl (PMaybe a)
  , ppset :: Term edsl a -> Term edsl b
  }

_ELeft :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => PPrism edsl a (EEither a b)
_ELeft =
  PPrism
  { ppget =
    \te ->
      ematch te \case
        ELeft a -> econ $ PJust a
        ERight _ -> econ PNothing
  , ppset = \ta -> econ $ ELeft ta
  }

_ERight :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => PPrism edsl b (EEither a b)
_ERight =
  PPrism
  { ppget =
    \te ->
      ematch te \case
        ELeft _ -> econ PNothing
        ERight b -> econ $ PJust b
  , ppset = \tb -> econ $ ERight tb
  }