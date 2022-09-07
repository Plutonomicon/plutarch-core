{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Optics.Fix(pfix, pconstrained) where

import Data.Function
import Data.Profunctor

import Generics.SOP

import Plutarch.Core
import Plutarch.Cont
import Plutarch.CPS.Optics.Traversal
import Generics.SOP.GGP
import Plutarch.PType

-- | Not a 'Plutarch.CPS.Optics.Traversal.CTraversal', but can be used to construct one.
pfix ::
  (
    PConstructable edsl (PFix a),
    PConstructable edsl (a (PFix a)),
    PConstructable edsl (PFix b),
    PConstructable edsl (b (PFix b)),
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

class (IsPCodeOf edsl tss (GCode (PConcrete edsl (a r)))) => IsPCodeOf' edsl tss a r 
instance (IsPCodeOf edsl tss (GCode (PConcrete edsl (a r)))) => IsPCodeOf' edsl tss a r 

pconstrained ::
  forall edsl f a b r c (ap :: [[PType]]) (bp :: [[PType]]).
  ( PConstructable edsl (PFix a)
  , PConstructable edsl (a (PFix a))
  , PGeneric1 a
  , (forall r'. IsPCodeOf' edsl ap a r')
  , PConstructable edsl (PFix b)
  , PConstructable edsl (b (PFix b))
  , PConstructable edsl r
  , PGeneric1 b
  , (forall r'. IsPCodeOf' edsl bp b r')
  , (forall ra rb. AllZip2 (Fixer c ra rb) ap bp)
  , SListI2 bp
  , Applicative f
  ) =>
  Proxy c ->
  (forall a' b'. c a' b' => Term edsl a' -> PCont edsl r (f (Term edsl b'))) ->
  Term edsl (PFix a) ->
  PCont edsl r (f (Term edsl (PFix b)))
pconstrained _ f =
  pfix fixer
  where
    fixer ::
      forall ra rb.
      ( PConstructable edsl (a ra)
      , PConstructable edsl (b rb)
      , AllZip2 (Fixer c ra rb) ap bp
      ) =>
      (Term edsl ra -> PCont edsl r (f (Term edsl rb))) ->
      Term edsl (a ra) ->
      PCont edsl r (f (Term edsl (b rb)))
    fixer r =
      pmatchCont $
        fmap (fmap (pcon . gto . sopFrom @edsl @bp) . hsequence')
        . hsequence'
        . htrans (Proxy @(Fixer c ra rb)) (fixerTrans @c @ra @rb r f)
        . sopTo @edsl @ap
        . gfrom

class Fixer c ra rb a b where
  fixerTrans ::
    (Term edsl ra -> PCont edsl r (f (Term edsl rb))) ->
    (c a b => Term edsl a -> PCont edsl r (f (Term edsl b))) ->
    Term edsl a ->
    (PCont edsl r :.: f :.: Term edsl) b

instance {-# OVERLAPS #-} Fixer c ra rb ra rb where
  fixerTrans r _ = Comp . fmap Comp . r

instance {-# OVERLAPPABLE #-} (c a b) => Fixer c ra rb a b where
  fixerTrans _ f = Comp . fmap Comp . f