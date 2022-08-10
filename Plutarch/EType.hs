{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.EType (
  EGeneric,
  egto,
  egfrom,
  ETypeF (MkETypeF),
  EType,
  EEType (EEType),
  Ef,
  Ef' (..),
  EfC,
  EHs,
  EHsW,
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

-- EType

-- What is an EType? It's a type that represents higher HKDs,
-- in the sense that their elements are applied to a type-level function,
-- but the core difference is that the following type is made legal:
-- `data A f = A (Ef f A)` which is isomorphic to `data A f = A (f A)`.
-- Simple HKDs don't allow this, as you'd have to do `data A f = A (f (A Identity))`
-- or similar, which doesn't convey the same thing.
-- This form of (higher) HKDs is useful for eDSLs, as you can replace the
-- the fields with eDSL terms.

data ETypeF = MkETypeF
  { _constraint :: forall (a :: Type). a -> Constraint
  , _concretise :: (ETypeF -> Type) -> Type
  }

-- | Higher HKD
type EType = ETypeF -> Type

newtype EEType (ef :: ETypeF) = EEType EType

type EHs :: EType -> Type
type family EHs (a :: EType) = r | r -> a where
  EHs EEType = (ETypeF -> Type)
  EHs a = a (MkETypeF Top EHsW)

type EHsW :: EType -> Type
newtype EHsW a = EHsW (NoReduce (EHs a)) deriving stock (Generic)

type family Ef (f :: ETypeF) (x :: EType) :: Type where
  forall (_constraint :: forall (a :: Type). a -> Constraint) (concretise :: EType -> Type) (x :: EType).
    Ef (MkETypeF _constraint concretise) x =
      Reduce (concretise x)

type (/$) ef a = Ef ef a
infixr 0 /$

newtype Ef' ef a = Ef' (ef /$ a)

type family EfC (f :: ETypeF) :: EHs a -> Constraint where
  forall (constraint :: forall (a :: Type). a -> Constraint) (_concretise :: EType -> Type).
    EfC (MkETypeF constraint _concretise) =
      constraint

class
  ( Generic (a ef)
  , GFrom (a ef)
  , GTo (a ef)
  , GDatatypeInfo (a ef)
  , All2 Top (ECode a) -- DO NOT REMOVE! Will cause unsound behavior otherwise. See `unsafeCoerce` below.
  ) =>
  EGeneric' a ef
instance
  ( Generic (a ef)
  , GFrom (a ef)
  , GTo (a ef)
  , GDatatypeInfo (a ef)
  , All2 Top (ECode a)
  ) =>
  EGeneric' a ef

type EGeneric :: EType -> Constraint
class (forall ef. EGeneric' a ef) => EGeneric a
instance (forall ef. EGeneric' a ef) => EGeneric a

data Dummy (a :: EType) deriving stock (Generic)

type ToEType :: [Type] -> [EType]
type family ToEType as where
  ToEType '[] = '[]
  ToEType (a ': as) = UnDummy a ': ToEType as

type ToEType2 :: [[Type]] -> [[EType]]
type family ToEType2 as where
  ToEType2 '[] = '[]
  ToEType2 (a ': as) = ToEType a ': ToEType2 as

type UnDummy :: Type -> EType
type family UnDummy a where
  UnDummy (Dummy a) = a

type DummyInst :: EType -> Type
type DummyInst a = a (MkETypeF Top Dummy)

-- FIXME: This doesn't work if the data type definition matches
-- on the `ef` using a type family.
type family ECode (a :: EType) :: [[EType]] where
  ECode a = ToEType2 (GCode (DummyInst a))

egfrom :: forall a ef. EGeneric a => Proxy a -> SOP I (GCode (a ef)) -> SOP (Ef' ef) (ECode a)
-- This could be done safely, but it's a PITA.
-- Depends on `All` constraint above.
egfrom = let _ = witness (Proxy @(EGeneric a)) in unsafeCoerce

egto :: forall a ef. EGeneric a => Proxy a -> SOP (Ef' ef) (ECode a) -> SOP I (GCode (a ef))
-- This could be done safely, but it's a PITA.
-- Depends on `All` constraint above.
egto = let _ = witness (Proxy @(EGeneric a)) in unsafeCoerce
