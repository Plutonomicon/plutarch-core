{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Core (
  PGeneric,
  Compile,
  CompileAp,
  PRepr,
  PDSLKind (..),
  UnPDSLKind,
  Term (Term),
  ClosedTerm,
  PHasRepr (..),
  PIsRepr (..),
  IsPType,
  isPType,
  PReprPrimitive,
  PReprSOP,
  PHs,
  PConcrete,
  PConstructable' (..),
  PConstructable (..),
  PDSL (..),
  unTerm,
  PEmbeds,
  pembed,
  PAp,
  papr,
  papl,
) where

import Data.Functor.Compose (Compose)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Stack (HasCallStack)
import GHC.TypeLits (Symbol)
import Plutarch.PType (
  PGeneric,
  PHs,
  PPType,
  PType,
  PTypeF,
  pattern MkETypeF,
 )
import Plutarch.Reduce (NoReduce)

newtype PDSLKind = PDSLKind (PType -> Type)

type family UnPDSLKind (edsl :: PDSLKind) :: PType -> Type where
  UnPDSLKind ( 'PDSLKind edsl) = edsl

newtype PReprKind = PReprKind Type

{- | A "representation" of a type. This defines how a user-visible type
 is mapped onto a type in the backend.
-}
class PIsRepr (r :: PReprKind) where
  type PReprApply r (a :: PType) :: PType
  type PReprC r (a :: PType) :: Constraint
  type PReprIsPType r (a :: PType) (edsl :: PDSLKind) (x :: PHs a) :: Constraint
  prfrom :: (PHasRepr a, PReprSort a ~ r) => a ef -> PReprApply r a ef
  prto :: (PHasRepr a, PReprSort a ~ r) => PReprApply r a ef -> a ef
  prIsPType ::
    forall edsl a (x :: PHs a) y.
    (PHasRepr a, PReprSort a ~ r, PReprIsPType r a edsl x) =>
    Proxy r ->
    Proxy edsl ->
    Proxy x ->
    (forall a' (x' :: PHs a'). IsPType' edsl x' => Proxy x' -> y) ->
    y

data PReprPrimitive'

-- | The "identity" representation.
type PReprPrimitive = 'PReprKind PReprPrimitive'

instance PIsRepr PReprPrimitive where
  type PReprApply PReprPrimitive a = a
  type PReprC PReprPrimitive _ = ()
  type PReprIsPType PReprPrimitive _ edsl x = IsPType' edsl x
  prfrom = id
  prto = id
  prIsPType _ _ x f = f x

data PReprSOP'

-- | Representation as a SOP. Requires 'PGeneric'.
type PReprSOP = 'PReprKind PReprSOP'

newtype PSOPed (a :: PType) ef = PSOPed (a ef)

type family Unimplemented (t :: Symbol) :: Constraint where

instance PIsRepr PReprSOP where
  type PReprApply PReprSOP a = PSOPed a
  type PReprC PReprSOP a = PGeneric a
  type PReprIsPType _ _ _ _ = Unimplemented "It is not yet clear how to handle this" -- Known x => IsPType' edsl x
  prfrom = PSOPed
  prto (PSOPed x) = x
  prIsPType _ _ _ _ = error "unimplemented"

class (PIsRepr (PReprSort a), PReprC (PReprSort a) a) => PHasRepr (a :: PType) where
  type PReprSort a :: PReprKind
  type PReprSort _ = PReprSOP

instance PHasRepr PPType where
  type PReprSort _ = PReprPrimitive

type PRepr :: PType -> PType
type family PRepr a where
  PRepr a = PReprApply (PReprSort a) a

type NoTypeInfo :: forall k. PHs k -> Constraint
class NoTypeInfo a
instance NoTypeInfo a

class Monad (PEffect edsl) => PDSL (edsl :: PDSLKind) where
  type PEffect edsl :: Type -> Type
  type IsPType' edsl :: forall (a :: PType). PHs a -> Constraint
  type IsPType' _ = NoTypeInfo

type role Term nominal nominal
newtype Term (edsl :: PDSLKind) (a :: PType) where
  Term :: {unTerm :: UnPDSLKind edsl (PRepr a)} -> Term edsl a

type ClosedTerm (c :: PDSLKind -> Constraint) (a :: PType) = forall edsl. c edsl => Term edsl a

type IsPTypeWrapper :: Bool -> PDSLKind -> forall (a :: PType). PHs a -> Constraint
class IsPTypeWrapper typeorval edsl x where
  isPTypeWrapper :: Proxy typeorval -> Proxy edsl -> Proxy x -> (forall a' (x' :: PHs a'). IsPType' edsl x' => Proxy x' -> y) -> y

instance (PHasRepr a, IsPType' edsl @PPType (PRepr a)) => IsPTypeWrapper 'True edsl (a :: PType) where
  isPTypeWrapper _ _ _ f = f (Proxy @(PRepr a))

instance (PHasRepr a, PReprIsPType (PReprSort a) a edsl x) => IsPTypeWrapper 'False edsl (x :: PHs a) where
  isPTypeWrapper _ edsl x f = prIsPType (Proxy @(PReprSort a)) edsl x f

type family TypeOrVal (a :: PType) :: Bool where
  TypeOrVal PPType = 'True
  TypeOrVal _ = 'False

type IsPType :: PDSLKind -> forall (a :: PType). PHs a -> Constraint
class PDSL edsl => IsPType edsl (x :: PHs a) where
  isPType ::
    forall y.
    Proxy edsl ->
    Proxy x ->
    (forall a' (x' :: PHs a'). IsPType' edsl x' => Proxy x' -> y) ->
    y
instance (PDSL edsl, IsPTypeWrapper (TypeOrVal a) edsl x) => IsPType edsl (x :: PHs a) where
  isPType = isPTypeWrapper (Proxy @(TypeOrVal a))

type CoerceTo :: forall a. forall (b :: Type) -> a -> b
type family CoerceTo (b :: Type) (x :: a) :: b where
  CoerceTo _ x = x

type H1 :: PDSLKind -> forall (a :: Type) -> a -> Constraint
type family H1 (edsl :: PDSLKind) (a :: Type) (x :: a) :: Constraint where
  H1 edsl PType x = IsPType edsl x
  forall (edsl :: PDSLKind) (a :: PType) (_ef :: PTypeF) (x :: a _ef).
    H1 edsl (a _ef) x =
      IsPType edsl (CoerceTo (PHs a) x)

type H2 :: PDSLKind -> forall (a :: Type). a -> Constraint
class H1 edsl a x => H2 edsl (x :: a)
instance H1 edsl a x => H2 edsl (x :: a)

type family Helper (edsl :: PDSLKind) :: PTypeF where
  Helper edsl = MkETypeF (H2 edsl) (Compose NoReduce (Term edsl))

type PConcrete (edsl :: PDSLKind) (a :: PType) = a (Helper edsl)

class (PDSL edsl, IsPType' edsl a) => PConstructable' edsl (a :: PType) where
  pconImpl :: HasCallStack => PConcrete edsl a -> UnPDSLKind edsl a
  pmatchImpl :: forall b. (HasCallStack, IsPType edsl b) => UnPDSLKind edsl a -> (PConcrete edsl a -> Term edsl b) -> Term edsl b
  pcaseImpl :: forall b. (HasCallStack, IsPType edsl b) => UnPDSLKind edsl a -> (PConcrete edsl a -> PEffect edsl (Term edsl b)) -> PEffect edsl (Term edsl b)

-- | The crux of what an eDSL is.
class IsPType edsl a => PConstructable edsl (a :: PType) where
  pcon :: HasCallStack => PConcrete edsl a -> Term edsl a
  pmatch ::
    forall b.
    (HasCallStack, IsPType edsl b) =>
    Term edsl a ->
    (PConcrete edsl a -> Term edsl b) ->
    Term edsl b
  pcase ::
    forall b.
    (HasCallStack, IsPType edsl b) =>
    Term edsl a ->
    (PConcrete edsl a -> PEffect edsl (Term edsl b)) ->
    PEffect edsl (Term edsl b)

-- duplicate IsPType' constraint because otherwise GHC complains
instance (PHasRepr a, IsPType' edsl (PRepr a), PConstructable' edsl (PRepr a)) => PConstructable edsl a where
  pcon x = Term $ pconImpl (prfrom x)
  pmatch (Term t) f = pmatchImpl t \x -> f (prto x)
  pcase (Term t) f = pcaseImpl t \x -> f (prto x)

class PDSL edsl => PAp (f :: Type -> Type) edsl where
  papr :: HasCallStack => f a -> Term edsl b -> Term edsl b
  papl :: HasCallStack => Term edsl a -> f b -> Term edsl a

class PAp m edsl => PEmbeds (m :: Type -> Type) edsl where
  pembed :: HasCallStack => m (Term edsl a) -> Term edsl a

type CompileAp variant output =
  forall a m.
  (PHasRepr a, HasCallStack, Applicative m, (forall edsl. variant edsl => IsPType edsl a)) =>
  (forall edsl. (variant edsl, PAp m edsl) => Term edsl a) ->
  m output

type Compile variant output =
  forall a m.
  (PHasRepr a, HasCallStack, Monad m, (forall edsl. variant edsl => IsPType edsl a)) =>
  (forall edsl. (variant edsl, PEmbeds m edsl) => Term edsl a) ->
  m output
