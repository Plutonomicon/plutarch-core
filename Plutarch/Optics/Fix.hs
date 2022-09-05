{-# LANGUAGE PartialTypeSignatures #-}

module Plutarch.Optics.Fix(pfix) where

import Data.Function
import Data.Profunctor

import Control.Monad.Trans.Cont

import Plutarch.Core
import Plutarch.Cont

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