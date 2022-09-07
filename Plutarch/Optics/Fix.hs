{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Optics.Fix(pfix) where

import Data.Function
import Data.Profunctor

import Control.Monad.Trans.Cont

import Generics.SOP
import qualified GHC.Generics as GHC

import Plutarch.Core
import Plutarch.Cont
import Plutarch.CPS.Optics.Traversal
import Generics.SOP.GGP
import Data.Kind
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

-- pconstrained ::
--   (
--     _
--   ) =>
--   x ->
--   Term edsl (PFix a) ->
--   PCont edsl r (f (Term edsl (PFix b))) 
-- pconstrained f =
--   pfix \r ->
--     pmatchCont (_ . from)

pconstrained ::
  forall edsl f a b (c :: PType -> PType -> Constraint) (ap :: [[PType]]) (bp :: [[PType]]) r.
  ( PConstructable edsl a
  , GHC.Generic (PConcrete edsl a)
  , GFrom (PConcrete edsl a)
  , IsPCodeOf edsl ap (GCode (PConcrete edsl a))
  , PConstructable edsl b
  , GHC.Generic (PConcrete edsl b)
  , GTo (PConcrete edsl b)
  , IsPCodeOf edsl bp (GCode (PConcrete edsl b))
  , SListI2 bp
  , AllZip2 c ap bp
  , IsPType  edsl r
  , Applicative f
  ) =>
  Proxy c ->
  (forall x y. c x y => Term edsl x -> f (Term edsl y)) ->
  Term edsl a ->
  PCont edsl r (f (Term edsl b))
pconstrained _ f =
  pmatchCont $
    return
      . fmap (pcon . gto . sopFrom @edsl @bp)
      . hsequence'
      . htrans (Proxy @c) (Comp . f)
      . sopTo @edsl @ap
      . gfrom 

class (forall r. PGeneric (a r)) => PGeneric1 a
instance (forall r. PGeneric (a r)) => PGeneric1 a

class (IsPCodeOf edsl tss (GCode (PConcrete edsl (a r)))) => IsPCodeOf' edsl tss a r 
instance (IsPCodeOf edsl tss (GCode (PConcrete edsl (a r)))) => IsPCodeOf' edsl tss a r 

pconstrained' ::
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
  , SListI2 bp
  , Applicative f
  ) =>
  Proxy c ->
  (_ -> _) ->
  Term edsl (PFix a) ->
  PCont edsl r (f (Term edsl (PFix b)))
pconstrained' _ f =
  pfix fixer
  where
    fixer ::
      forall ra rb.
      ( PConstructable edsl (a ra)
      , PConstructable edsl (b rb)
      ) =>
      (Term edsl ra -> PCont edsl r (f (Term edsl rb))) ->
      Term edsl (a ra) ->
      PCont edsl r (f (Term edsl (b rb)))
    fixer r =
      pmatchCont $
        return
          . fmap (pcon . gto . sopFrom @edsl @bp)
          . hsequence'
          . _
          . sopTo @edsl @ap
          . gfrom
