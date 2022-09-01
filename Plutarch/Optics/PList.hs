module Plutarch.Optics.PList where

import Control.Monad.Trans.Cont
import Plutarch.CPS.Optics.Traversal
import Plutarch.Core
import Plutarch.Cont
import Plutarch.PList
import Plutarch.Optics.Fix
import Control.Applicative

plist ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl b
  , IsEType edsl r
  , EConstructable edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF b))
  , EConstructable edsl r
  ) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PList a))
    (Term edsl (PList b))
    (Term edsl a)
    (Term edsl b)
plist =
  ctraversal
    \f -> pmatchCont (\(PList as) -> fmap (econ . PList) <$> plist' f as)

plist' ::
  (
    EConstructable edsl (EFix (PListF a)),
    EConstructable edsl (PListF a (EFix (PListF a))),
    EConstructable edsl (EFix (PListF b)),
    EConstructable edsl r,
    EConstructable edsl (PListF b (EFix (PListF b))),
    Applicative f
  ) =>
  (Term edsl a -> f (Term edsl b)) ->
  Term edsl (EFix (PListF a)) ->
  Cont (Term edsl r) (f (Term edsl (EFix (PListF b))))
plist' f =
  pfix
    (\r -> pmatchCont \case
      PNil -> return $ pure (econ PNil)
      PCons a as -> fmap econ . liftA2 PCons (f a) <$> r as
    )