{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

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
    (Term edsl    ra    -> Cont (Term edsl r) (f (Term edsl    rb  ))) ->
     Term edsl (a ra  ) -> Cont (Term edsl r) (f (Term edsl (b rb  )))
  ) ->
     Term edsl (PFix a) -> Cont (Term edsl r) (f (Term edsl (PFix b)))
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
--   Cont (Term edsl r) (f (Term edsl (PFix b))) 
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
  Cont (Term edsl r) (f (Term edsl b))
pconstrained _ f =
  pmatchCont $
    return
      . fmap (pcon . gto . sopFrom @edsl @bp)
      . hsequence'
      . htrans (Proxy @c) (Comp . f)
      . sopTo @edsl @ap
      . gfrom

pconstrained' :: _ => _
pconstrained' f =
  pfix \r -> _