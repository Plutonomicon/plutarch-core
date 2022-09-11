{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Optics.Fix(
  pfix,
  PFixable,
  pconstrained,
  ptraverse,
  PTraversible,
  ) where

import Data.Function
import Data.Profunctor

import Generics.SOP

import Plutarch.Core
import Plutarch.Cont
import Plutarch.CPS.Optics.Traversal
import Generics.SOP.GGP
import Data.Kind

class
  ( PConstructable edsl (PFix a)
  , PConstructable edsl (a (PFix a))
  ) => PFixable edsl a
instance
  ( PConstructable edsl (PFix a)
  , PConstructable edsl (a (PFix a))
  ) => PFixable edsl a

-- | Not a 'Plutarch.CPS.Optics.Traversal.CTraversal', but can be used to construct one.
pfix ::
  (
    PFixable edsl a,
    PFixable edsl b,
    PConstructable edsl r,
    Applicative f
  ) =>
  (
    forall ra rb.
    (
      PConstructable edsl (a ra),
      PConstructable edsl (b rb)
    ) =>
    (Term edsl    ra    -> PCont edsl r (f (Term edsl    rb  ))) ->
     Term edsl (a ra  ) -> PCont edsl r (f (Term edsl (b rb  )))
  ) ->
     Term edsl (PFix a) -> PCont edsl r (f (Term edsl (PFix b)))
pfix f =
  pmatchCont \(PFix a) ->
    fmap (pcon . PFix)
      <$> fix
        (f .
          dimap
            (\fa -> pmatch fa \(PFix a') -> a')
            (fmap (fmap (pcon . PFix)))
        )
        a

class (forall r. PGeneric (a r)) => PGeneric1 a
instance (forall r. PGeneric (a r)) => PGeneric1 a

class
  ( AllZip2 (Fixer c (Term edsl ra) (Term edsl rb)) (GCode (PConcrete edsl (a ra))) (GCode (PConcrete edsl (b rb)))
  , SListI2 (GCode (PConcrete edsl (b rb)))
  ) => PConstrained' edsl c a b ra rb
instance
  ( AllZip2 (Fixer c (Term edsl ra) (Term edsl rb)) (GCode (PConcrete edsl (a ra))) (GCode (PConcrete edsl (b rb)))
  , SListI2 (GCode (PConcrete edsl (b rb)))
  ) => PConstrained' edsl c a b ra rb

class
  ( PFixable edsl a
  , PFixable edsl b
  , (forall ra rb. PConstrained' edsl c a b ra rb)
  , PGeneric1 a
  , PGeneric1 b
  ) => PConstrainedFixable edsl c a b
instance
  ( PFixable edsl a
  , PFixable edsl b
  , PGeneric1 a
  , PGeneric1 b
  , (forall ra rb. PConstrained' edsl c a b ra rb)
  ) => PConstrainedFixable edsl c a b



pconstrained ::
  forall edsl f a b r (c :: Type -> Type -> Constraint).
  ( PConstrainedFixable edsl c a b
  , PConstructable edsl r
  , Applicative f
  ) =>
  Proxy c ->
  (forall a' b'. c a' b' => a' -> PCont edsl r (f b')) ->
  Term edsl (PFix a) ->
  PCont edsl r (f (Term edsl (PFix b)))
pconstrained _ f =
  pfix fixer
  where
    fixer ::
      forall ra rb.
      ( PConstructable edsl (a ra)
      , PConstructable edsl (b rb)
      , AllZip2 (Fixer c (Term edsl ra) (Term edsl rb)) (GCode (PConcrete edsl (a ra))) (GCode (PConcrete edsl (b rb)))
      , SListI2 (GCode (PConcrete edsl (b rb)))
      ) =>
      (Term edsl ra -> PCont edsl r (f (Term edsl rb))) ->
      Term edsl (a ra) ->
      PCont edsl r (f (Term edsl (b rb)))
    fixer r =
      pmatchCont $
        fmap (fmap (pcon . gto) . hsequence')
        . hsequence'
        . htrans
          (Proxy @(Fixer c (Term edsl ra) (Term edsl rb)))
          (Comp . fmap (Comp . fmap I) . fixerTrans @c r f . unI)
        . gfrom

class Fixer c a b a' b' where
  fixerTrans ::
    (a -> PCont edsl r (f b)) ->
    (c a' b' => a' -> PCont edsl r (f b')) ->
    a' ->
    PCont edsl r (f b')

instance Fixer c a b a b where
  fixerTrans f _ = f

instance (c a' b') => Fixer c a b a' b' where
  fixerTrans _ f = f

class (forall a b. PConstrainedFixable edsl (PTraverse (Term edsl a) (Term edsl b)) (t a) (t b)) => PTraversible edsl t 
instance (forall a b. PConstrainedFixable edsl (PTraverse (Term edsl a) (Term edsl b)) (t a) (t b)) => PTraversible edsl t 

ptraverse ::
    forall edsl a b t r.
  ( PTraversible edsl t
  , PConstructable edsl r
  ) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PFix (t a)))
    (Term edsl (PFix (t b)))
    (Term edsl a)
    (Term edsl b)
ptraverse =
  ctraversal
    \f -> pconstrained (Proxy @(PTraverse (Term edsl a) (Term edsl b))) (return . ptraverse' f)

class PTraverse a b a' b' where
  ptraverse' ::
    Applicative f =>
    (a -> f b) ->
    a' ->
    f b'

instance PTraverse a b a b where
  ptraverse' = ($)

instance PTraverse a b a' a' where
  ptraverse' _ = pure