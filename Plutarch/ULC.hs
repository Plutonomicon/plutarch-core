module Plutarch.ULC (ULC (..), compile) where

import Plutarch.Core
import Plutarch.EType

newtype Lvl = Lvl Int

data ULC
  = App ULC ULC
  | Lam ULC
  | Var Lvl
  | Error

newtype ULCImpl (a :: EType) = ULCImpl {runImpl :: Lvl -> ULC}

class Top (a :: EType)
instance Top a

data Arrow (a :: EType) (b :: EType) (f :: ETypeF)

class (forall a b. EConstructable edsl (EPair a b), EUntyped edsl, ELC edsl, EPartial edsl) => EULC edsl

instance EDSL ULCImpl where
  type IsEType ULCImpl = Top

instance ELC ULCImpl where
  type EArrow ULCImpl = Arrow
  elam f = ULCImpl \i -> Lam (runImpl (f $ ULCImpl \_ -> Var i) i)
  ULCImpl f # ULCImpl g = ULCImpl \lvl -> f lvl `App` g lvl

instance EUntyped ULCImpl where
  eunsafeCoerce (ULCImpl f) = ULCImpl f

instance EPartial ULCImpl where
  eerror = ULCImpl . pure $ Error

instance EConstructable ULCImpl (EPair a b) where
  pcon (EPair x y) = ULCImpl \lvl -> Lam $ Var lvl `App` runImpl x lvl `App` runImpl y lvl

instance EULC ULCImpl

compile :: forall a. (forall edsl. EULC edsl => edsl a) -> ULC
compile term = runImpl term (Lvl 0)
