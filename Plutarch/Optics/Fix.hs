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
import Generics.SOP.NS
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


-- ptraverse ::
--   _ =>
--   CTraversal
--     (Term edsl r)
--     (Term edsl (PFix (t a)))
--     (Term edsl (PFix (t b)))
--     (Term edsl a)
--     (Term edsl b)
-- ptraverse = ctraversal
--   (\f -> pfix _) 

g ::
  forall edsl a b (c :: PType -> PType -> Constraint).
  ( GHC.Generic (PConcrete edsl a)
  , GFrom (PConcrete edsl a)
  , PIsSOP edsl a
  , GHC.Generic (PConcrete edsl b)
  , GTo (PConcrete edsl b)
  , PIsSOP edsl b
  , PConstructable edsl b
  , _
  ) =>
  Proxy c ->
  (forall x y. c x y => Term edsl x -> Term edsl y) ->
  Term edsl a ->
  Term edsl b
g p f a =
  pmatch a \c ->
    case esop (Proxy @edsl) (Proxy @a) of
      PIsSumR _ _ from' ->
        case esop (Proxy @edsl) (Proxy @b) of
          PIsSumR _ to' _ ->
            pcon . gto . to' . htrans (Proxy @(ConstrainedOn edsl c)) f . from' . gfrom $ c

class ConstrainedOn edsl c ta tb
instance (c a b, ta ~ Term edsl a, tb ~ Term edsl b) => ConstrainedOn edsl c ta tb