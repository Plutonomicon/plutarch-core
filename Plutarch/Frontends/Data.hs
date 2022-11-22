{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

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
  All,
  All2,
  ConstructorInfo (Constructor, Infix, Record),
  ConstructorName,
  DatatypeName,
  FieldInfo (FieldInfo),
  FieldName,
  K (K),
  ModuleName,
  NP (Nil, (:*)),
  POP (POP),
  SOP,
  constructorInfo,
  constructorName,
  cpara_SList,
  datatypeName,
  moduleName,
 )
import Generics.SOP.GGP (GCode, gdatatypeInfo, gfrom, gto)
import Generics.SOP.NP (liftA_NP)
import Plutarch.Core (
  IsPType,
  IsPTypeData,
  IsPTypePrim,
  PConcrete,
  PConcreteEf,
  PConstructablePrim,
  PDSLKind,
  isPType,
 )
import Plutarch.PType (PCode, PGeneric, PHs, PPType, PType, PTypeF, Pf', PfC, pgfrom, pgto, type (/$))
import Plutarch.Repr (PHasRepr, PReprSort)
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.Repr.SOP (PSOPed)
import Unsafe.Coerce (unsafeCoerce)

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
  PConstructor :: PConstructorInfo ps
  PInfix :: PConstructorInfo '[a, b]
  PRecord :: NP (K FieldName) ps -> PConstructorInfo ps

data IsPTypeSOPData edsl p = IsPTypeSOPData
  { moduleName :: ModuleName
  , name :: DatatypeName
  , constructorNames :: NP (K ConstructorName) (PCode p)
  , constructorInfo :: NP PConstructorInfo (PCode p)
  , typeInfo :: POP (IsPTypeData edsl) (PCode p)
  , to :: SOP (Pf' (PConcreteEf edsl)) (PCode p) -> PConcrete edsl p
  , from :: PConcrete edsl p -> SOP (Pf' (PConcreteEf edsl)) (PCode p)
  }

class IsPTypeSOP edsl a where
  isPTypeSOP ::
    Proxy edsl ->
    Proxy a ->
    (PGeneric a => IsPTypeSOPData edsl a -> b) ->
    b

type family OpaqueEf :: PTypeF where

-- TODO: implement safely
coercer :: Proxy p -> NP (K a) (GCode (p OpaqueEf)) -> NP (K a) (PCode p)
coercer _ x = unsafeCoerce x

-- TODO: implement safely
coercer2 :: Proxy p -> NP PConstructorInfo (GCode (p OpaqueEf)) -> NP PConstructorInfo (PCode p)
coercer2 _ x = unsafeCoerce x

newtype T1 (edsl :: PDSLKind) (ps :: [PType]) = T1 (NP (IsPTypeData edsl) ps)
unT1 :: T1 edsl ps -> NP (IsPTypeData edsl) ps
unT1 (T1 x) = x

newtype T2 (edsl :: PDSLKind) (pss :: [[PType]]) = T2 (POP (IsPTypeData edsl) pss)
unT2 :: T2 edsl pss -> POP (IsPTypeData edsl) pss
unT2 (T2 x) = x

instance (PGeneric a, All2 (IsPType edsl) (PCode a)) => IsPTypeSOP edsl a where
  isPTypeSOP _ _ x =
    case gdatatypeInfo (Proxy @(a OpaqueEf)) of
      i ->
        let names = liftA_NP (\con -> K (constructorName con)) $ constructorInfo i
            info = liftA_NP f (constructorInfo i)
            f :: ConstructorInfo as -> PConstructorInfo as
            f (Constructor _) = PConstructor
            f (Infix _ _ _) = PInfix
            f (Record _ fields) = PRecord (liftA_NP (\(FieldInfo n) -> K n) fields)
            prog1 :: IsPType edsl p => T1 edsl ps -> T1 edsl (p ': ps)
            prog1 (T1 prev) = T1 (isPType :* prev)
            prog2 :: forall ps pss. All (IsPType edsl) ps => T2 edsl pss -> T2 edsl (ps ': pss)
            prog2 (T2 (POP prev)) =
              let next :: T1 edsl ps
                  next = cpara_SList (Proxy @(IsPType edsl)) (T1 Nil) prog1
               in T2 (POP (unT1 next :* prev))
            t :: T2 edsl (PCode a)
            t =
              cpara_SList
                (Proxy @(All (IsPType edsl)))
                (T2 $ POP Nil)
                prog2
            d = IsPTypeSOPData
              do moduleName i
              do datatypeName i
              do coercer (Proxy @a) names
              do coercer2 (Proxy @a) info
              do unT2 t
              do gto . pgto (Proxy @a) (Proxy @(PConcreteEf edsl))
              do pgfrom (Proxy @a) (Proxy @(PConcreteEf edsl)) . gfrom
         in x d

type PSOP :: PDSLKind -> Constraint
type PSOP edsl =
  ( PConstructablePrim edsl PUnit
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructablePrim edsl (PPair a b)
  , forall a b. (IsPType edsl a, IsPType edsl b) => PConstructablePrim edsl (PEither a b)
  , forall a. IsPTypeSOP edsl a => PConstructablePrim edsl (PSOPed a)
  , IsPTypePrim edsl PPType
  )
