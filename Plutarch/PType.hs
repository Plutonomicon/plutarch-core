{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.PType (
  PGeneric,
  PCode,
  pgto,
  pgfrom,
  PTypeF (MkPTypeF),
  PType,
  PPType (PPType),
  Pf,
  Pf' (..),
  PfC,
  PHs,
  PHs',
  PHsW,
  type (/$),
) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import Generics.SOP (All2, I, SOP, Top)
import Generics.SOP.GGP (GCode, GDatatypeInfo, GFrom, GTo)
import Plutarch.Internal.Witness (witness)
import Plutarch.Reduce (NoReduce, Reduce)
import Unsafe.Coerce (unsafeCoerce)

-- PType

-- What is an PType? It's a type that represents higher HKDs,
-- in the sense that their elements are applied to a type-level function,
-- but the core difference is that the following type is made legal:
-- `data A f = A (Pf f A)` which is isomorphic to `data A f = A (f A)`.
-- Simple HKDs don't allow this, as you'd have to do `data A f = A (f (A Identity))`
-- or similar, which doesn't convey the same thing.
-- This form of (higher) HKDs is useful for eDSLs, as you can replace the
-- the fields with eDSL terms.

data PTypeF = MkPTypeF
  { _constraint :: forall (a :: Type). a -> Constraint
  , _concretise :: (PTypeF -> Type) -> Type
  }

-- | Higher HKD
type PType = PTypeF -> Type

newtype PPType (ef :: PTypeF) = PPType PType

type PHs' a = a (MkPTypeF Top PHsW)

type PHs :: PType -> Type
type family PHs (a :: PType) = r | r -> a where
  PHs PPType = PType
  PHs a = PHs' a

type PHsW :: PType -> Type
newtype PHsW a = PHsW (NoReduce (PHs a)) deriving stock (Generic)

type family Pf (f :: PTypeF) (x :: PType) :: Type where
  forall (_constraint :: forall (a :: Type). a -> Constraint) (concretise :: PType -> Type) (x :: PType).
    Pf (MkPTypeF _constraint concretise) x =
      Reduce (concretise x)

type (/$) ef a = Pf ef a
infixr 0 /$

newtype Pf' ef a = Pf' (ef /$ a)

type family PfC (f :: PTypeF) :: PHs a -> Constraint where
  forall (constraint :: forall (a :: Type). a -> Constraint) (_concretise :: PType -> Type).
    PfC (MkPTypeF constraint _concretise) =
      constraint

class
  ( Generic (a ef)
  , GFrom (a ef)
  , GTo (a ef)
  , GDatatypeInfo (a ef)
  , All2 Top (PCode a) -- DO NOT REMOVE! Will cause unsound behavior otherwise. See `unsafeCoerce` below.
  ) =>
  PGeneric' a ef
instance
  ( Generic (a ef)
  , GFrom (a ef)
  , GTo (a ef)
  , GDatatypeInfo (a ef)
  , All2 Top (PCode a)
  ) =>
  PGeneric' a ef

type PGeneric :: PType -> Constraint
class (forall ef. PGeneric' a ef) => PGeneric a
instance (forall ef. PGeneric' a ef) => PGeneric a

data Dummy (a :: PType) deriving stock (Generic)

type ToPType :: [Type] -> [PType]
type family ToPType as where
  ToPType '[] = '[]
  ToPType (a ': as) = UnDummy a ': ToPType as

type ToPType2 :: [[Type]] -> [[PType]]
type family ToPType2 as where
  ToPType2 '[] = '[]
  ToPType2 (a ': as) = ToPType a ': ToPType2 as

type UnDummy :: Type -> PType
type family UnDummy a where
  UnDummy (Dummy a) = a

type DummyInst :: PType -> Type
type DummyInst a = a (MkPTypeF Top Dummy)

-- FIXME: This doesn't work if the data type definition matches
-- on the `ef` using a type family.
type family PCode (a :: PType) :: [[PType]] where
  PCode a = ToPType2 (GCode (DummyInst a))

pgfrom :: forall a ef. PGeneric a => Proxy a -> SOP I (GCode (a ef)) -> SOP (Pf' ef) (PCode a)
-- This could be done safely, but it's a PITA.
-- Depends on `All` constraint above.
pgfrom = let _ = witness (Proxy @(PGeneric a)) in unsafeCoerce

pgto :: forall a ef. PGeneric a => Proxy a -> SOP (Pf' ef) (PCode a) -> SOP I (GCode (a ef))
-- This could be done safely, but it's a PITA.
-- Depends on `All` constraint above.
pgto = let _ = witness (Proxy @(PGeneric a)) in unsafeCoerce
