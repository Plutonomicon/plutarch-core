module Plutarch.Frontends.Data (
  PVoid,
  PLet (..),
  PDelay (..),
  type (#=>) (..),
  type (#->) (..),
  PAny (..),
  PForall (..),
  PSome (..),
  PFix (..),
  PUnit (..),
  PPair (..),
  PEither (..),
  PSOP,
) where

import Data.Kind (Constraint)
import Data.Proxy (Proxy)
import GHC.Generics (Generic)
import Plutarch.Core (IsPType, PConstructable, PConstructable', PDSLKind)
import Plutarch.Generics (PIsSOP)
import Plutarch.PType (PHs, PPType, PType, PTypeF, PfC, type (/$))
import Plutarch.Repr (PHasRepr, PReprSort)
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.Repr.SOP (PSOPed)

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

type PSOP :: PDSLKind -> Constraint
type PSOP edsl =
  ( PConstructable edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable' edsl (PPair a b)
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructable' edsl (PEither a b)
  , forall a. PIsSOP edsl a => PConstructable' edsl (PSOPed a)
  , IsPType edsl PPType
  )
