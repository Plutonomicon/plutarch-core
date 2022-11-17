{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Frontends.Data (
  PVoid,
  IsPTypeSOP (..),
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
  IsPTypeSOPData (..),
  PConstructorInfo (..),
) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import Generics.SOP (
  All2,
  ConstructorName,
  DatatypeName,
  FieldName,
  K (K),
  ModuleName,
  NP,
  POP,
  SListI,
  constructorInfo,
  constructorName,
  datatypeName,
  moduleName,
 )
import Generics.SOP.Dict (Dict)
import Generics.SOP.GGP (gdatatypeInfo)
import Generics.SOP.NP (liftA_NP)
import Plutarch.Core (IsPType, IsPTypePrim, IsPTypePrimData, PConstructable, PConstructablePrim, PDSLKind)
import Plutarch.PType (PCode, PGeneric, PHs, PPType, PType, PTypeF, PfC, type (/$))
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

data PConstructorInfo ps :: Type where
  PConstructor :: SListI ps => PConstructorInfo ps
  PInfix :: PConstructorInfo '[a, b]
  PRecord :: SListI ps => NP (K FieldName) ps -> PConstructorInfo ps

data IsPTypeSOPData pss = IsPTypeSOPData ModuleName DatatypeName (NP (K ConstructorName) pss) (NP PConstructorInfo pss)

class IsPTypeSOP edsl a where
  isPTypeSOP ::
    Proxy edsl ->
    Proxy a ->
    (PGeneric a => IsPTypeSOPData (PCode a) -> POP (IsPTypePrimData edsl) (PCode a) -> b) ->
    b

type family OpaqueEf :: PTypeF where

instance (PGeneric a, All2 (IsPType edsl) (PCode a)) => IsPTypeSOP edsl a where
  isPTypeSOP _ _ x =
    let i = gdatatypeInfo (Proxy @(a OpaqueEf))
     in -- names = liftA_NP (\con -> K (constructorName con)) $ constructorInfo i

        x (IsPTypeSOPData (moduleName i) (datatypeName i) undefined undefined) undefined

type PSOP :: PDSLKind -> Constraint
type PSOP edsl =
  ( PConstructablePrim edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructablePrim edsl (PPair a b)
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructablePrim edsl (PEither a b)
  , forall a. IsPTypeSOP edsl a => PConstructablePrim edsl (PSOPed a)
  , IsPTypePrim edsl PPType
  )
