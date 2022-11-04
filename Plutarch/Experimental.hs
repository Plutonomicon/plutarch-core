module Plutarch.Experimental (PEq (..), PSingle) where

import Plutarch.Repr (PHasRepr (PReprSort))
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.PType (PType, type (/$), PHs)

data PEq (x :: a) (y :: a) ef where
  PRefl :: PEq x x ef
instance PHasRepr (PEq x y) where type PReprSort _ = PReprPrimitive

type PSingle :: forall (a :: PType). PHs a -> PType
newtype PSingle (x :: PHs a) ef = PSingle (ef /$ a)
instance PHasRepr (PSingle x) where type PReprSort _ = PReprPrimitive

_x :: PSingle a ef
_x = PSingle undefined
