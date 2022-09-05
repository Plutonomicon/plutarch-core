module Plutarch.ULC (ULC (..), compile) where

import Plutarch.Core
import Plutarch.PType

newtype Lvl = Lvl Int

data ULC
  = App ULC ULC
  | Lam ULC
  | Var Lvl
  | Error

newtype ULCImpl (a :: PType) = ULCImpl {runImpl :: Lvl -> ULC}

class Top (a :: PType)
instance Top a

data Arrow (a :: PType) (b :: PType) (f :: ETypeF)

class (forall a b. PConstructable edsl (PPair a b), EUntyped edsl, ELC edsl, EPartial edsl) => EULC edsl

instance EDSL ULCImpl where
  type IsPType ULCImpl = Top

instance ELC ULCImpl where
  type EArrow ULCImpl = Arrow
  elam f = ULCImpl \i -> Lam (runImpl (f $ ULCImpl \_ -> Var i) i)
  ULCImpl f # ULCImpl g = ULCImpl \lvl -> f lvl `App` g lvl

instance EUntyped ULCImpl where
  eunsafeCoerce (ULCImpl f) = ULCImpl f

instance EPartial ULCImpl where
  eerror = ULCImpl . pure $ Error

instance PConstructable ULCImpl (PPair a b) where
  pcon (PPair x y) = ULCImpl \lvl -> Lam $ Var lvl `App` runImpl x lvl `App` runImpl y lvl

instance EULC ULCImpl

compile :: forall a. (forall edsl. EULC edsl => edsl a) -> ULC
compile term = runImpl term (Lvl 0)
