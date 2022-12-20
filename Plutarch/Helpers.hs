{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Plutarch.Helpers (
  IsPType1,
  IsPType2,
  IsPType3,
  PConstructable1,
  PConstructable2,
  PConstructable3,
  plet,
  pbind,
  (#),
  plam,
  T,
  pany,
  type ($),
  ($$),
) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Stack (HasCallStack, withFrozenCallStack)
import Plutarch.Core (IsPType, PConcrete, PConstructable, PDSLKind, PEffect, Term, pcase, pcon, pmatch)
import Plutarch.Frontends.Data (PAny (PAny), PLet (PLet), type (#->) (PLam))
import Plutarch.Frontends.LC (PLC)
import Plutarch.PType (PType)
import Plutarch.TermCont (TermCont, tcont)

type IsPType1 :: PDSLKind -> (PType -> PType) -> Constraint
type IsPType1 e f = forall a. IsPType e a => IsPType e (f a)
type IsPType2 :: PDSLKind -> (PType -> PType -> PType) -> Constraint
type IsPType2 e f = forall a b. (IsPType e a, IsPType e b) => IsPType e (f a b)
type IsPType3 :: PDSLKind -> (PType -> PType -> PType -> PType) -> Constraint
type IsPType3 e f = forall a b c. (IsPType e a, IsPType e b, IsPType e c) => IsPType e (f a b c)

type PConstructable1 :: PDSLKind -> (PType -> PType) -> Constraint
type PConstructable1 e f = forall a. IsPType e a => PConstructable e (f a)
type PConstructable2 :: PDSLKind -> (PType -> PType -> PType) -> Constraint
type PConstructable2 e f = forall a b. (IsPType e a, IsPType e b) => PConstructable e (f a b)
type PConstructable3 :: PDSLKind -> (PType -> PType -> PType -> PType) -> Constraint
type PConstructable3 e f = forall a b c. (IsPType e a, IsPType e b, IsPType e c) => PConstructable e (f a b c)

plet :: forall e a. (HasCallStack, PConstructable e (PLet a)) => Term e a -> TermCont e (Term e a)
plet x = tcont \f -> pmatch (pcon $ PLet x) \(PLet y) -> f y

pbind :: forall e a. (HasCallStack, IsPType e a, PConstructable e (PLet a)) => Term e a -> PEffect e (Term e a)
pbind x = pcase (pcon $ PLet x) \(PLet y) -> pure y

(#) :: (HasCallStack, PLC e, IsPType e a, IsPType e b) => Term e (a #-> b) -> Term e a -> Term e b
(#) f x = pmatch f (\(PLam f') -> f' x)

infixl 8 #

plam' :: forall edsl a b. (HasCallStack, PConstructable edsl (a #-> b)) => (Term edsl a -> Term edsl b) -> Term edsl (a #-> b)
plam' f = pcon $ (PLam f :: PConcrete edsl (a #-> b))

class PLamN (a :: Type) (b :: PType) (edsl :: PDSLKind) | a -> b, edsl b -> a where
  plam :: forall c. (HasCallStack, PConstructable edsl (c #-> b)) => (Term edsl c -> a) -> Term edsl (c #-> b)

instance {-# OVERLAPPABLE #-} (a' ~ Term edsl a) => PLamN a' a edsl where
  plam = withFrozenCallStack plam'

instance (PConstructable edsl (a #-> b), a' ~ Term edsl a, PLamN b' b edsl) => PLamN (a' -> b') (a #-> b) edsl where
  plam f = withFrozenCallStack $ plam' $ \x -> plam (f x)

type T :: forall (e :: PDSLKind). PType -> Type
type family T (a :: PType) where
  T @e a = Term e a

pany :: PConstructable e PAny => Term e a -> Term e PAny
pany x = pcon $ PAny Proxy x

($$) :: PConstructable edsl a => (Term edsl a -> b) -> PConcrete edsl a -> b
f $$ x = f (pcon x)
infixr 0 $$

type f $ x = f x
infixr 0 $
