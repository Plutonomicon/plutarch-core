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
    EConstructable edsl (EFix a),
    EConstructable edsl (a (EFix a)),
    EConstructable edsl (EFix b),
    EConstructable edsl (b (EFix b)),
    EConstructable edsl r,
    Applicative f
  ) =>
  (
    forall ra rb.
    (
      EConstructable edsl (a ra),
      EConstructable edsl (b rb)
    ) =>
    (Term edsl    ra    -> Cont (Term edsl r) (f (Term edsl    rb  ))) ->
     Term edsl (a ra  ) -> Cont (Term edsl r) (f (Term edsl (b rb  )))
  ) ->
     Term edsl (EFix a) -> Cont (Term edsl r) (f (Term edsl (EFix b)))
pfix f =
  pmatchCont \(EFix a) ->
    fmap (econ . EFix)
      <$> fix
        (f .
          dimap
            (\fa -> ematch fa \(EFix a') -> a')
            (fmap (fmap (econ . EFix)))
        )
        a