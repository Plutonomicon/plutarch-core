module Plutarch.Optics.PList where

import Control.Monad.Trans.Cont
import Plutarch.CPS.Optics.Traversal
import Plutarch.Core
import Plutarch.Cont
import Plutarch.PList
import Plutarch.Optics.Fix
import Control.Applicative

plist ::
  ( PSOP edsl
  , IsPType edsl a
  , IsPType edsl b
  , IsPType edsl r
  , PConstructable edsl (PFix (PListF a))
  , PConstructable edsl (PFix (PListF b))
  , PConstructable edsl r
  ) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PList a))
    (Term edsl (PList b))
    (Term edsl a)
    (Term edsl b)
plist =
  ctraversal
    \f -> pmatchCont (\(PList as) -> fmap (pcon . PList) <$> plist' f as)

plist' ::
  (
    PConstructable edsl (PFix (PListF a)),
    PConstructable edsl (PListF a (PFix (PListF a))),
    PConstructable edsl (PFix (PListF b)),
    PConstructable edsl r,
    PConstructable edsl (PListF b (PFix (PListF b))),
    Applicative f
  ) =>
  (Term edsl a -> f (Term edsl b)) ->
  Term edsl (PFix (PListF a)) ->
  PCont edsl r (f (Term edsl (PFix (PListF b))))
plist' f =
  pfix
    (\r -> pmatchCont \case
      PNil -> return $ pure (pcon PNil)
      PCons a as -> fmap pcon . liftA2 PCons (f a) <$> r as
    )
