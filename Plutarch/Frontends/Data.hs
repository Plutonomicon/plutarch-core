module Plutarch.Frontends.Data (
  PVoid,
  PLet(..),
  PDelay(..),
  type (#=>)(..),
  type (#->)(..),
  PAny(..),
  PForall(..),
  PSome(..),
  PFix(..),
  PUnit(..),
  PPair(..),
  PEither(..),
)

import Plutarch.PType (PHs, PType, type (/$), PTypeF)
import Plutarch.Core (PHasRepr, PReprPrimitive, PReprSort)

data PVoid ef
instance PHasRepr PVoid where type PReprSort _ = PReprPrimitive

-- | Pffects of `pcon` are effects of the argument.
data PLet a ef = PLet (ef /$ a)

instance PHasRepr (PLet a) where type PReprSort _ = PReprPrimitive

-- | `pcon` has no effects.
data PDelay a ef = PDelay (ef /$ a)

instance PHasRepr (PDelay a) where type PReprSort _ = PReprPrimitive

-- | '=>' embedded into an eDSL.
data (#=>) (a :: Constraint) (b :: PType) ef = PConstrained (a => ef /$ b)

instance PHasRepr (a #=> b) where type PReprSort _ = PReprPrimitive

infixr 0 #=>

-- | '->' embedded into an eDSL.
data (#->) a b ef = PLam ((ef /$ a) -> (ef /$ b)) deriving stock (Generic)

instance PHasRepr (a #-> b) where type PReprSort _ = PReprPrimitive

infixr 0 #->

data PAny ef = forall a. PAny (Proxy a) (ef /$ a)
instance PHasRepr PAny where type PReprSort _ = PReprPrimitive

newtype PForall (f :: PHs a -> PType) ef = PForall (forall (forallvar :: PHs a). PfC ef forallvar => ef /$ f forallvar)
instance PHasRepr (PForall ef) where type PReprSort _ = PReprPrimitive

data PSome (f :: PHs a -> PType) ef = forall (x :: PHs a). PSome (PfC ef x => ef /$ f x)
instance PHasRepr (PSome ef) where type PReprSort _ = PReprPrimitive

newtype PFix f ef = PFix (ef /$ f (PFix f))
instance PHasRepr (PFix f) where type PReprSort _ = PReprPrimitive

data PUnit (ef :: PTypeF) = PUnit deriving stock (Generic)
instance PHasRepr PUnit where type PReprSort _ = PReprPrimitive

data PPair a b ef = PPair (ef /$ a) (ef /$ b) deriving stock (Generic)
instance PHasRepr (PPair a b) where type PReprSort _ = PReprPrimitive

data PEither a b ef = PLeft (ef /$ a) | PRight (ef /$ b) deriving stock (Generic)
instance PHasRepr (PEither a b) where type PReprSort _ = PReprPrimitive
