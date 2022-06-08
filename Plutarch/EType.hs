{-# LANGUAGE UndecidableInstances #-}

module Plutarch.EType (EType' (MkEType'), ETypeF, UnEType', EType, Ef, ToETypeF) where
  
import Data.Kind (Type)
import Plutarch.Reduce (Reduce)
import GHC.Generics
import Data.Type.Bool (type (&&))

-- EType

-- What is an EType? It's a type that represents higher HKDs,
-- in the sense that their elements are applied to a type-level function,
-- but the core difference is that the following type is made legal:
-- `data A f = A (Hf f a)` which is isomorphic to `data A f = A (f A)`.
-- Simple HKDs don't allow this, as you'd have to do `data A f = A (f (A Identity))`
-- or similar, which doesn't convey the same thing.
-- This form of (higher) HKDs is useful for eDSLs, as you can replace the
-- the fields with eDSL terms.

newtype EType' = MkEType' EType deriving stock Generic

type family IsValidEType (x :: Type) :: Bool where
  IsValidEType (ETypeF -> Type) = 'True
  IsValidEType (x -> y) = IsValidEType x && IsValidEType y
  IsValidEType _ = 'False

type ETypeF = EType' -> Type

type family UnEType' (u :: EType') :: EType where
  UnEType' (MkEType' x) = x
--
-- | Higher HKD
type EType = ETypeF -> Type

type Ef (f :: ETypeF) (x :: EType) = Reduce (f (MkEType' x))

type ToETypeF :: (EType -> Type) -> ETypeF
newtype ToETypeF (f :: EType -> Type) (x :: EType') = ToETypeF (f (UnEType' x)) deriving stock Generic
