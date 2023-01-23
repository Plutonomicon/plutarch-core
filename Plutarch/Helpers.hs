{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Plutarch.Helpers (
  DerivePReprPrimitive,
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
  PForall (..),
  PForallClass,
  PForallF (..),
  PForallF',
  pforall,
) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality (pattern Refl)
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack, withFrozenCallStack)
import GHC.TypeLits (Nat, type (-))
import Generics.SOP (NP (Nil, (:*)))
import Plutarch.Core (IsPType, PConcrete, PConstructable, PDSL, PDSLKind, PIO, Term, pcase, pcon, pmatch)
import Plutarch.Frontends.Data (PAny (PAny), PForall1 (PForall1), PLet (PLet), PSOP, type (#->) (PLam))
import Plutarch.Frontends.LC (PLC, PPolymorphic)
import Plutarch.Internal.CoerceTo (Coerce, CoerceTo)
import Plutarch.PType (PHs, PHs' (PHs'), PPType, PType, PTypeF, UnPHs, pHs_inverse, type (/$))
import Plutarch.Repr (PHasRepr, PReprSort)
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.TermCont (TermCont, tcont)
import Unsafe.Coerce (unsafeCoerce)

type IsPType1 :: forall a. PDSLKind -> (PHs a -> PType) -> Constraint
type IsPType1 e f = forall x. IsPType e x => IsPType e (f x)
type IsPType2 :: PDSLKind -> (PType -> PType -> PType) -> Constraint
type IsPType2 e f = forall a b. (IsPType e a, IsPType e b) => IsPType e (f a b)
type IsPType3 :: PDSLKind -> (PType -> PType -> PType -> PType) -> Constraint
type IsPType3 e f = forall a b c. (IsPType e a, IsPType e b, IsPType e c) => IsPType e (f a b c)

type PConstructable1 :: PDSLKind -> (PHs a -> PType) -> Constraint
type PConstructable1 e f = forall x. IsPType e x => PConstructable e (f x)
type PConstructable2 :: PDSLKind -> (PType -> PType -> PType) -> Constraint
type PConstructable2 e f = forall a b. (IsPType e a, IsPType e b) => PConstructable e (f a b)
type PConstructable3 :: PDSLKind -> (PType -> PType -> PType -> PType) -> Constraint
type PConstructable3 e f = forall a b c. (IsPType e a, IsPType e b, IsPType e c) => PConstructable e (f a b c)

type PForallF' :: forall (a :: PType) (b :: Type). (PHs a -> b) -> PHs a -> PType
type family PForallF' (f :: PHs a -> b) (x :: PHs a) :: PType where
  PForallF' @_ @(PTypeF -> Type) f x = f x
  PForallF' @_ @(b -> c) f x = PForall @(UnPHs b) (CoerceTo (PHs (UnPHs b) -> c) (f x))
type PForallF :: forall (a :: PType) (b :: Type). (PHs a -> b) -> PHs a -> PType
newtype PForallF (f :: PHs a -> b) (x :: PHs a) (ef :: PTypeF) = PForallF (ef /$ PForallF' f x)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)
newtype PForall (f :: PHs a -> b) ef = PForall (ef /$ PForall1 (PForallF f))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

type ArgTypesFor :: Type -> [PType]
type family ArgTypesFor fk where
  ArgTypesFor PType = '[]
  ArgTypesFor (a -> fk') = UnPHs a ': ArgTypesFor fk'

type ApplyTypeArgs' :: forall fk xsk. fk -> NP PHs' xsk -> PType
type family ApplyTypeArgs' f xs where
  ApplyTypeArgs' @PType f _ = f
  ApplyTypeArgs' @(a -> _) f ('PHs' x ':* xs) = ApplyTypeArgs' (f (CoerceTo a x)) xs

type ApplyTypeArgs :: forall fk. fk -> NP PHs' (ArgTypesFor fk) -> PType
type ApplyTypeArgs f xs = ApplyTypeArgs' f xs

type TermApplyTypeArgs :: forall fk. PDSLKind -> fk -> NP PHs' (ArgTypesFor fk) -> Type
newtype TermApplyTypeArgs e f xs = TermApplyTypeArgs (Term e (ApplyTypeArgs f xs))

red ::
  forall (e :: PDSLKind) (fk :: Type) (a :: PType) (f :: PHs a -> fk) (x :: PHs a) (xs :: NP PHs' (ArgTypesFor fk)).
  TermApplyTypeArgs e f (CoerceTo (NP PHs' (ArgTypesFor (PHs a -> fk))) ('PHs' x ':* xs)) ->
  TermApplyTypeArgs e (f x) xs
-- FIXME: Don't use `unsafeCoerce`. (Is this even possible?)
red = unsafeCoerce -- (TermApplyTypeArgs x) = TermApplyTypeArgs x

type ApplyTypeArgsC :: forall fk. (PType -> Constraint) -> fk -> NP PHs' (ArgTypesFor fk) -> Constraint
class c (ApplyTypeArgs f xs) => ApplyTypeArgsC c f xs
instance c (ApplyTypeArgs f xs) => ApplyTypeArgsC c f xs

type IsPTypeAll' :: forall xsk. PDSLKind -> NP PHs' xsk -> Constraint
type family IsPTypeAll' e xs where
  IsPTypeAll' @'[] _ _ = () :: Constraint
  IsPTypeAll' e ('PHs' x ':* xs) = (IsPType e x, IsPTypeAll' e xs)

type IsPTypeAll :: forall xsk. PDSLKind -> NP PHs' xsk -> Constraint
class IsPTypeAll' e xs => IsPTypeAll e xs
instance IsPTypeAll' e xs => IsPTypeAll e xs

{-
type IsPTypeN :: forall fk. PDSLKind -> (PType -> fk) -> Constraint
type IsPTypeN e (f :: PType -> fk) = forall (xs :: NP PHs' (ArgTypesFor (PType -> fk))). IsPTypeAll e xs => ApplyTypeArgsC (IsPType e) f xs

type PConstructableN :: forall fk. PDSLKind -> (PType -> fk) -> Constraint
type PConstructableN e (f :: PType -> fk) = forall (xs :: NP PHs' (ArgTypesFor (PType -> fk))). IsPTypeAll e xs => ApplyTypeArgsC (IsPType e) f xs
-}

class PForallClass (f :: PHs a -> fk) e where
  pforall' ::
    -- NB!!! If you change the type,
    -- change the type of `pforall` too.
    -- `unsafeCoerce` is used.
    (PPolymorphic e, PSOP e) =>
    ( forall xs.
      IsPTypeAll e xs =>
      TermApplyTypeArgs e f xs
    ) ->
    Term e (PForall f)

instance (IsPType e a, PConstructable1 e (PForallF f)) => PForallClass (f :: PHs a -> PTypeF -> Type) e where
  pforall' x =
    case pHs_inverse @a of
      Refl -> pcon $ PForall $ pcon $ PForall1 (case red x of TermApplyTypeArgs redx -> pcon $ PForallF redx)

class
  ( PForallClass @b' @fk (Coerce f x) e
  , IsPType e (PForall (Coerce f x :: PHs b' -> fk))
  ) =>
  CC (f :: PHs a -> b -> fk) b' e (x :: PHs a)
instance
  ( PForallClass @b' @fk (Coerce f x) e
  , IsPType e (PForall (Coerce f x :: PHs b' -> fk))
  ) =>
  CC (f :: PHs a -> b -> fk) b' e (x :: PHs a)

instance
  ( forall (x :: PHs a). IsPType e x => CC f b' e x
  , b ~ PHs b'
  , IsPType e a
  ) =>
  PForallClass (f :: PHs a -> b -> c -> fk) e
  where
  pforall' x =
    case (pHs_inverse @a, pHs_inverse @b') of
      (Refl, Refl) -> pcon $ PForall $ pcon $ PForall1 $ pcon $ PForallF $ pforall' $ red x

type ConstructNPFromVars :: forall (bs :: [PType]). forall (as :: [PType]) -> NP PHs' bs -> NP PHs' as
type family ConstructNPFromVars as xs where
  ConstructNPFromVars '[] _ = 'Nil
  ConstructNPFromVars (_ ': as) (x ':* xs) = (x ':* ConstructNPFromVars as xs)

type family NthType (fk :: Type) (n :: Nat) :: PType where
  NthType (a -> _) 0 = UnPHs a
  NthType (_ -> b) n = NthType b (n - 1)
  NthType _ _ = PPType

newtype PForall'_function f e
  = PForall'_function
      ( (PForallClass f e, PPolymorphic e, PSOP e) =>
        ( forall xs.
          IsPTypeAll e xs =>
          TermApplyTypeArgs e f xs
        ) ->
        Term e (PForall f)
      )

newtype PForall_function (f :: PType -> fk) e
  = PForall_function
      ( (PForallClass f e, PPolymorphic e, PSOP e) =>
        ( forall (x0 :: PType) (x1 :: PHs (NthType fk 0)) (x2 :: PHs (NthType fk 1)) (x3 :: PHs (NthType fk 2)) (x4 :: PHs (NthType fk 3)) (x5 :: PHs (NthType fk 4)) (x6 :: PHs (NthType fk 5)) (x7 :: PHs (NthType fk 6)) (x8 :: PHs (NthType fk 7)) (x9 :: PHs (NthType fk 8)).
          IsPTypeAll e (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'PHs' x3 ':* 'PHs' x4 ':* 'PHs' x5 ':* 'PHs' x6 ':* 'PHs' x7 ':* 'PHs' x8 ':* 'PHs' x9 ':* 'Nil)) =>
          Term e (ApplyTypeArgs f (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'PHs' x3 ':* 'PHs' x4 ':* 'PHs' x5 ':* 'PHs' x6 ':* 'PHs' x7 ':* 'PHs' x8 ':* 'PHs' x9 ':* 'Nil)))
        ) ->
        Term e (PForall f)
      )

pforall ::
  forall fk (f :: PType -> fk) (e :: PDSLKind).
  (PForallClass f e, PPolymorphic e, PSOP e) =>
  ( forall -- TODO: fix asymptotics, below is O(n^2) for n variables
           (x0 :: PType) (x1 :: PHs (NthType fk 0)) (x2 :: PHs (NthType fk 1)) (x3 :: PHs (NthType fk 2)) (x4 :: PHs (NthType fk 3)) (x5 :: PHs (NthType fk 4)) (x6 :: PHs (NthType fk 5)) (x7 :: PHs (NthType fk 6)) (x8 :: PHs (NthType fk 7)) (x9 :: PHs (NthType fk 8)).
    IsPTypeAll e (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'PHs' x3 ':* 'PHs' x4 ':* 'PHs' x5 ':* 'PHs' x6 ':* 'PHs' x7 ':* 'PHs' x8 ':* 'PHs' x9 ':* 'Nil)) =>
    Term e (ApplyTypeArgs f (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'PHs' x3 ':* 'PHs' x4 ':* 'PHs' x5 ':* 'PHs' x6 ':* 'PHs' x7 ':* 'PHs' x8 ':* 'PHs' x9 ':* 'Nil)))
  ) ->
  Term e (PForall f)
-- TODO: Fix GHC.
-- Given a metavariable a :: k, if there is only one constructor C possible for k,
-- then GHC should lazily expand a to C a', where a' is a new metavariable.
-- This would mean you can prove `Any @() ~ '()`. While it seems bad, I'm unconvinced
-- it has any practical detriments.
PForall_function pforall = unsafeCoerce (PForall'_function pforall' :: PForall'_function f e)

plet :: forall e a. (HasCallStack, PConstructable e (PLet a)) => Term e a -> TermCont e (Term e a)
plet x = tcont \f -> pmatch (pcon $ PLet x) \(PLet y) -> f y

pbind :: forall e a. (HasCallStack, PDSL e, IsPType e a, PConstructable e (PLet a)) => Term e a -> PIO e (Term e a)
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

data DerivePReprPrimitive (ef :: PTypeF)
instance PHasRepr DerivePReprPrimitive where type PReprSort _ = PReprPrimitive
