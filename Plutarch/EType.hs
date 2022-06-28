{-# LANGUAGE UndecidableInstances #-}

module Plutarch.EType (
  EIfNewtype,
  EIsNewtype (..),
  ENewtype (..),
  type MkENewtype,
  ERepr,
  EReprAp,
  ETypeRepr,
  pattern MkETypeRepr,
  coerceERepr,
  EDSLKind,
  ETypeF (MkETypeF),
  EType,
  Ef,
  EfC,
  EHs,
  type (/$),
) where

import Data.Coerce (Coercible)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Generics.SOP (Top)
import Plutarch.Reduce (NoReduce, Reduce)

-- EType

-- What is an EType? It's a type that represents higher HKDs,
-- in the sense that their elements are applied to a type-level function,
-- but the core difference is that the following type is made legal:
-- `data A f = A (Hf f a)` which is isomorphic to `data A f = A (f A)`.
-- Simple HKDs don't allow this, as you'd have to do `data A f = A (f (A Identity))`
-- or similar, which doesn't convey the same thing.
-- This form of (higher) HKDs is useful for eDSLs, as you can replace the
-- the fields with eDSL terms.

data ETypeF = MkETypeF
  { _constraint :: EType -> Constraint
  , _concretise :: EType -> Type
  }

-- | Higher HKD
type EType = ETypeF -> Type

type EDSLKind = ETypeRepr -> Type

type family Ef (f :: ETypeF) (x :: EType) :: Type where
  Ef (MkETypeF _constraint concretise) x = Reduce (concretise x)

type (/$) ef x = Ef ef x
infix 0 /$

type family EfC (f :: ETypeF) :: EType -> Constraint where
  EfC (MkETypeF constraint _concretise) = constraint

newtype ENewtype (a :: EType) f = ENewtype (a f)
type MkENewtype a = MkETypeRepr (ENewtype a)

class KnownBool (EIsNewtype' a) => EIsNewtype (a :: EType) where
  type EIsNewtype' a :: Bool
  type EIsNewtype' _ = True

type EIfNewtype a = (EIsNewtype a, EIsNewtype' a ~ True)

newtype ETypeRepr = MkETypeRepr EType

type family EReprHelper (b :: Bool) (a :: EType) where
  EReprHelper True a = ENewtype a
  EReprHelper False a = a

type family EReprAp (a :: ETypeRepr) :: EType where
  EReprAp (MkETypeRepr a) = a

type ERepr :: EType -> ETypeRepr
type ERepr a = MkETypeRepr (EReprHelper (EIsNewtype' a) a)

data Dict :: Constraint -> Type where
  Dict :: c => Dict c

-- FIXME replace with generic-singletons
data SBool :: Bool -> Type where
  STrue :: SBool 'True
  SFalse :: SBool 'False

class KnownBool (b :: Bool) where
  knownBool :: SBool b

instance KnownBool 'True where
  knownBool = STrue

instance KnownBool 'False where
  knownBool = SFalse

h :: Proxy a -> SBool b -> Dict (Coercible (EReprHelper b a) a)
h _ STrue = Dict
h _ SFalse = Dict

g :: forall a. EIsNewtype a => Proxy a -> Dict (Coercible (EReprAp (ERepr a)) a)
g p =
  let _ = EHs' -- FIXME: Remove, -Wunused-top-binds is broken
   in h p (knownBool :: SBool (EIsNewtype' a))

coerceERepr :: forall a b. EIsNewtype a => Proxy a -> (Coercible (EReprAp (ERepr a)) a => b) -> b
coerceERepr p f = case g p of Dict -> f

type EHs' :: EType -> Type
type EHs (a :: EType) = a (MkETypeF Top EHs')
newtype EHs' (a :: EType) = EHs' (NoReduce (EHs a))
