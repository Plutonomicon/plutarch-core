module Plutarch.Experimental (EEq (..), ESingle) where

import Plutarch.Core (EHasRepr (..), EHs, EReprPrimitive)
import Plutarch.EType (EType, type (/$))

data EEq (x :: a) (y :: a) ef where
  ERefl :: EEq x x ef
instance EHasRepr (EEq x y) where type EReprSort _ = EReprPrimitive

type ESingle :: forall (a :: EType). EHs a -> EType
newtype ESingle (x :: EHs a) ef = ESingle (ef /$ a)
instance EHasRepr (ESingle x) where type EReprSort _ = EReprPrimitive

_x :: ESingle a ef
_x = ESingle undefined
