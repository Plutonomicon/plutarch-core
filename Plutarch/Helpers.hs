{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
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
  PForallN (..),
  PForallNClass,
  PForallNF (..),
  PForallNF',
  pforall,
) where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack, withFrozenCallStack)
import Plutarch.Core (PDSL, IsPType, PConcrete, PConstructable, PDSLKind, PEffect, Term, pcase, pcon, pmatch)
import Plutarch.Frontends.Data (PForall (PForall), PAny (PAny), PLet (PLet), type (#->) (PLam), PSOP)
import Plutarch.Frontends.LC (PLC, PPolymorphic)
import Plutarch.Repr (PHasRepr)
import Plutarch.PType (PHsEf, PType, PPType, PHs' (PHs'), type (/$), UnPHs, PHs, PTypeF)
import Plutarch.TermCont (TermCont, tcont)
import Plutarch.Internal.CoerceTo (CoerceTo)
import Generics.SOP (NP ((:*), Nil), I (I))
import Unsafe.Coerce (unsafeCoerce)

type IsPType1 :: forall a. PDSLKind -> (PHs a -> PType) -> Constraint
type IsPType1 e f = forall x. IsPType e x => IsPType e (f x)
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

type PForallNF' :: forall (a :: PType) (b :: Type). (PHs a -> b) -> PHs a -> PType
type family PForallNF' (f :: PHs a -> b) (x :: PHs a) :: PType where
  PForallNF' f x = f x
  -- TODO: remove CoerceTo by making GHC realise that `b` can't be `PPType``.
  -- (Currently it technically can, but an extra clause that turns that into an
  -- error is trivial to implement).
  PForallNF' @_ @(b -> c) f x = PForallN @(UnPHs b) (CoerceTo (PHs (UnPHs b) -> c) (f x))
type PForallNF :: forall (a :: PType) (b :: Type). (PHs a -> b) -> PHs a -> PType
newtype PForallNF (f :: PHs a -> b) (x :: PHs a) (ef :: PTypeF) = PForallNF (ef /$ PForallNF' f x)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)
newtype PForallN (f :: PHs a -> b) ef = PForallN (ef /$ PForall (PForallNF f))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

type ArgTypesFor :: Type -> [PType]
type family ArgTypesFor fk where
  ArgTypesFor PType = '[]
  ArgTypesFor (PType -> fk')  = PPType ': ArgTypesFor fk'
  ArgTypesFor (a _ -> fk')  = a ': ArgTypesFor fk'

type ApplyTypeArgs' :: forall fk xsk. fk -> NP PHs' xsk -> PType
type family ApplyTypeArgs' f xs where
  ApplyTypeArgs' @PType f _ = f
  ApplyTypeArgs' @(PType -> _) f ('PHs' x ':* xs) = ApplyTypeArgs' (f x) xs
  ApplyTypeArgs' @(a PHsEf -> _) f ('PHs' x ':* xs) = ApplyTypeArgs' (f (CoerceTo (a PHsEf) x)) xs

type ApplyTypeArgs :: forall fk. fk -> NP PHs' (ArgTypesFor fk) -> PType
type ApplyTypeArgs f xs = ApplyTypeArgs' f xs

type TermApplyTypeArgs :: forall fk. PDSLKind -> fk -> NP PHs' (ArgTypesFor fk) -> Type
newtype TermApplyTypeArgs e f xs = TermApplyTypeArgs (Term e (ApplyTypeArgs f xs))

red ::
  forall e fk (f :: PType -> fk) x xs.
  TermApplyTypeArgs e f ('PHs' x ':* xs) ->
  TermApplyTypeArgs e (f x) xs
red (TermApplyTypeArgs x) = TermApplyTypeArgs x

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

type IsPTypeN :: forall fk. PDSLKind -> (PType -> fk) -> Constraint
type IsPTypeN e (f :: PType -> fk) = forall (xs :: NP PHs' (ArgTypesFor (PType -> fk))). IsPTypeAll e xs => ApplyTypeArgsC (IsPType e) f xs

type PConstructableN :: forall fk. PDSLKind -> (PType -> fk) -> Constraint
type PConstructableN e (f :: PType -> fk) = forall (xs :: NP PHs' (ArgTypesFor (PType -> fk))). IsPTypeAll e xs => ApplyTypeArgsC (IsPType e) f xs

class PForallNClass (f :: PType -> fk) e where
  pforall' ::
    -- NB!!! If you change the type,
    -- change the type of `pforall` too.
    -- `unsafeCoerce` is used.
    (PPolymorphic e, PSOP e) =>
    (forall xs.
      IsPTypeAll e xs =>
      TermApplyTypeArgs e f xs
    ) ->
    Term e (PForallN f)

instance (PConstructable1 e (PForallNF f)) => PForallNClass (f :: PType -> PType) e where
  pforall' x = impl2 x where
    helper ::
      forall (x :: PType).
      (IsPType e x) =>
      Term e (f x) ->
      Term e (PForallNF f x)
    helper x = pcon $ PForallNF x
    impl ::
      forall x.
      (IsPType e x) =>
      (forall xs.
        IsPTypeAll e xs =>
        TermApplyTypeArgs e f ('PHs' x ':* xs)
      ) ->
      Term e (PForallNF f x)
    impl x = case red x of
      TermApplyTypeArgs redx -> helper redx
    helper2 ::
      (forall (x :: PType). IsPType e x => Term e (PForallNF f x)) ->
      Term e (PForallN f)
    helper2 x = pcon $ PForallN $ pcon $ PForall x
    impl2 ::
      (forall x xs.
        (IsPType e x, IsPTypeAll e xs) =>
        TermApplyTypeArgs e f ('PHs' x ':* xs)
      ) ->
      Term e (PForallN f)
    impl2 x = helper2 (impl x)

instance
  ( forall (x :: PType). IsPType e x => IsPType e (PForallN (f x))
  , forall x. IsPType e x => PForallNClass (f x) e
  ) => PForallNClass (f :: PType -> PType -> fk) e where
  pforall' ::
    (PPolymorphic e, PSOP e) =>
    (forall xs.
      IsPTypeAll e xs =>
      TermApplyTypeArgs e f xs
    ) ->
    Term e (PForallN f)
  pforall' x = impl2 x where
    impl ::
      forall x.
      (IsPType e x) =>
      (forall xs.
        IsPTypeAll e xs =>
        TermApplyTypeArgs e f ('PHs' x ':* xs)
      ) ->
      Term e (PForallNF f x)
    impl x = pcon $ PForallNF $ pforall' $ red x
    impl2 ::
      (forall x xs.
        (IsPType e x, IsPTypeAll e xs) =>
        TermApplyTypeArgs e f ('PHs' x ':* xs)
      ) ->
      Term e (PForallN f)
    impl2 x = pcon $ PForallN $ pcon $ PForall (impl x)

type ConstructNPFromVars :: forall (bs :: [PType]). forall (as :: [PType]) -> NP PHs' bs -> NP PHs' as
type family ConstructNPFromVars as xs where
  ConstructNPFromVars '[] _ = 'Nil
  ConstructNPFromVars (a ': as) (x ':* xs) = (x ':* ConstructNPFromVars as xs)

newtype PForall'function f e = PForall'function
  (
    (PForallNClass f e, PPolymorphic e, PSOP e) =>
    (forall xs.
      IsPTypeAll e xs =>
      TermApplyTypeArgs e f xs
    ) ->
    Term e (PForallN f)
  )

pforall ::
  forall fk (f :: PType -> fk) (e :: PDSLKind).
  (PForallNClass f e, PPolymorphic e, PSOP e) =>
  (forall (x0 :: PType) x1 x2. -- FIXME: fix types of x1 x2
    IsPTypeAll e (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'Nil)) =>
    Term e (ApplyTypeArgs f (ConstructNPFromVars (ArgTypesFor (PType -> fk)) ('PHs' x0 ':* 'PHs' x1 ':* 'PHs' x2 ':* 'Nil)))
  ) ->
  Term e (PForallN f)
-- FIXME: Fix GHC.
-- Given a metavariable a :: k, if there is only one constructor C possible for k,
-- then GHC should lazily expand a to C a', where a' is a new metavariable.
-- This would mean you can prove `Any @() ~ '()`. While it seems bad, I'm unconvinced
-- it has any practical detriments.
pforall = unsafeCoerce (PForall'function pforall' :: PForall'function f e)

plet :: forall e a. (HasCallStack, PConstructable e (PLet a)) => Term e a -> TermCont e (Term e a)
plet x = tcont \f -> pmatch (pcon $ PLet x) \(PLet y) -> f y

pbind :: forall e a. (HasCallStack, PDSL e, IsPType e a, PConstructable e (PLet a)) => Term e a -> PEffect e (Term e a)
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
