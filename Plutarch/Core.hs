{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Core (
  PDSL (..),
  PDSLKind (..),
  UnPDSLKind,
  Term (..),
  ClosedTerm,
  unTerm,
  PConcrete,
  PConcreteEf,
  IsPType (..),
  isPTypeQuantified,
  IsPTypeData (IsPTypeData),
  PConstructable (..),
  PConstructablePrim (..),
  PAp (..),
  PEmbeds (..),
  Compile,
  CompileTy,
  CompileAp,
  IsPTypePrim (..),
  withIsPType,
  PPure (..),
  PSubDSL (..),
  TermIO,
  PAll,
) where

import Data.Functor.Compose (Compose)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Records (HasField (getField))
import GHC.Stack (HasCallStack)
import Generics.SOP (All)
import Plutarch.Internal.WithDictHack (unsafeWithDict)
import Plutarch.PType (
  MkPTypeF,
  PHs,
  PType,
  PTypeF,
 )
import Plutarch.Reduce (NoReduce)
import Plutarch.Repr (PIsRepr, PRepr, PReprC, PReprSort, prfrom, prto)

newtype PDSLKind = PDSLKind (PType -> Type)

type family UnPDSLKind (e :: PDSLKind) :: PType -> Type where
  UnPDSLKind ('PDSLKind e) = e

type NoTypeInfo :: forall k. PHs k -> Constraint
class NoTypeInfo a
instance NoTypeInfo a

-- FIXME: support untyped languages, i.e., forall x. IsPType e x
class Monad (PIO e) => PDSL (e :: PDSLKind) where
  -- FIXME: possibly add boolean parameter to indicate purity
  data PIO e :: Type -> Type
  data IsPTypePrimData e :: forall (a :: PType). PHs a -> Type
  punsafePerformIO :: IsPType e a => TermIO e a -> Term e a

type TermIO e a = PIO e (Term e a)

class PPure e where
  pperformIO :: IsPType e a => TermIO e a -> Term e a

class PSubDSL e cs where
  psubDSL :: (forall e'. PAll e' cs => (forall b. Term e b -> Term e' b) -> Term e' a) -> Term e a

type IsPTypePrim :: PDSLKind -> forall (a :: PType). PHs a -> Constraint
class IsPTypePrim (e :: PDSLKind) (x :: PHs a) where
  isPTypePrim :: IsPTypePrimData e x

type role Term nominal nominal
newtype Term (e :: PDSLKind) (a :: PType) where
  Term :: UnPDSLKind e (PRepr a) -> Term e a

unTerm :: Term e a -> UnPDSLKind e (PRepr a)
unTerm (Term t) = t

class c e => PImplements e c
instance c e => PImplements e c

type PAll e cs = All (PImplements e) cs

type ClosedTerm (cs :: [PDSLKind -> Constraint]) (a :: PType) = forall e. PAll e cs => Term e a

type IsPTypeData :: PDSLKind -> forall (a :: PType). PHs a -> Type
newtype IsPTypeData e x = IsPTypeData (IsPTypePrimData e (PRepr x))

type IsPType :: PDSLKind -> forall (a :: PType). PHs a -> Constraint
-- FIXME: remove GiveRepr superclass, should be unnecessary, maybe GHC bug?
class IsPType e (x :: PHs a) where
  isPType :: IsPTypeData e x
instance
  ( IsPTypePrim e (PRepr x)
  ) =>
  IsPType e (x :: PHs a)
  where
  isPType = IsPTypeData isPTypePrim

withIsPType :: forall e x a. IsPTypeData e x -> (IsPType e x => a) -> a
withIsPType x = unsafeWithDict (Proxy @(IsPType e x)) x

isPTypeQuantified ::
  forall e f y.
  (forall x. IsPType e x => IsPType e (f x)) =>
  Proxy e ->
  Proxy f ->
  IsPTypeData e y ->
  IsPTypeData e (f y)
isPTypeQuantified _ _ y = withIsPType y $ isPType @e @_ @(f y)

type PConcreteEf :: PDSLKind -> PTypeF
type PConcreteEf e = MkPTypeF (IsPType e) (Compose NoReduce (Term e))

type PConcrete :: PDSLKind -> PType -> Type
type PConcrete e a = a (PConcreteEf e)

class (PDSL e, IsPTypePrim e a) => PConstructablePrim e (a :: PType) where
  pconImpl :: HasCallStack => PConcrete e a -> UnPDSLKind e a
  pmatchImpl :: forall b. (HasCallStack, IsPType e b) => UnPDSLKind e a -> (PConcrete e a -> Term e b) -> Term e b
  pcaseImpl :: forall b. (HasCallStack, IsPType e b) => UnPDSLKind e a -> (PConcrete e a -> PIO e (Term e b)) -> PIO e (Term e b)

-- | The crux of what an eDSL is.
class IsPType e a => PConstructable e (a :: PType) where
  pcon :: HasCallStack => PConcrete e a -> Term e a
  pmatch ::
    forall b.
    (HasCallStack, IsPType e b) =>
    Term e a ->
    (PConcrete e a -> Term e b) ->
    Term e b
  pcase ::
    forall b.
    (HasCallStack, IsPType e b) =>
    Term e a ->
    (PConcrete e a -> PIO e (Term e b)) ->
    PIO e (Term e b)

instance (PIsRepr (PReprSort a), PReprC (PReprSort a) a, PConstructablePrim e (PRepr a)) => PConstructable e a where
  pcon x = Term $ pconImpl (prfrom x)
  pmatch (Term t) f = pmatchImpl t \x -> f (prto x)
  pcase (Term t) f = pcaseImpl t \x -> f (prto x)

class PDSL e => PAp (f :: Type -> Type) e where
  papr :: HasCallStack => f a -> Term e b -> Term e b
  papl :: HasCallStack => Term e a -> f b -> Term e a

class PAp m e => PEmbeds (m :: Type -> Type) e where
  pembed :: HasCallStack => m (Term e a) -> Term e a

type CompileTy variant output =
  forall a (x :: PHs a).
  Proxy x ->
  (forall e. variant e => IsPType e x) =>
  output

type CompileAp variant output =
  forall a m.
  Proxy a ->
  (HasCallStack, Applicative m, (forall e. variant e => IsPType e a)) =>
  (forall e. (variant e, PAp m e) => Term e a) ->
  m output

type Compile variant output =
  forall a m.
  Proxy a ->
  (HasCallStack, Monad m, (forall e. variant e => IsPType e a)) =>
  (forall e. (variant e, PEmbeds m e) => Term e a) ->
  m output

instance
  ( PConstructable e r
  , IsPType e a
  , HasField name (PConcrete e r) (Term e a)
  ) =>
  HasField name (Term e r) (Term e a)
  where
  getField x = pmatch x \x' -> getField @name x'
