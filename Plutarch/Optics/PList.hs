module Plutarch.Optics.PList where

import Control.Applicative
import Control.Monad.Cont
import Plutarch.CPS.Optics.Traversal
import Plutarch.Core
import Plutarch.PList

plist'' ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl b
  , IsEType edsl r
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  , IsEType edsl (EFix (PListF b))
  , EConstructable edsl (EFix (PListF b))
  ) =>
  Term edsl (EFix (PListF a)) ->
  Cont
    (Term edsl r)
    (FunList (Term edsl a) (Term edsl b) (Term edsl (EFix (PListF b))))
plist'' fl = cont \f ->
  ematch fl \(EFix l) -> ematch l \case
    PNil -> f . pure . econ . EFix . econ $ PNil
    PCons x xs ->
      runCont
        (plist'' xs)
        (f . liftA2 (\x' -> econ . EFix . econ . PCons x') (single x))

plist' ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl b
  , IsEType edsl r
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  , IsEType edsl (EFix (PListF b))
  , EConstructable edsl (EFix (PListF b))
  ) =>
  Term edsl (PList a) ->
  Cont
    (Term edsl r)
    (FunList (Term edsl a) (Term edsl b) (Term edsl (PList b)))
plist' fl = fmap (econ . PList) <$> plist'' (ematch fl unPList)

plist ::
  ( ESOP edsl
  , IsEType edsl a
  , IsEType edsl b
  , IsEType edsl r
  , IsEType edsl (EFix (PListF a))
  , EConstructable edsl (EFix (PListF a))
  , IsEType edsl (EFix (PListF b))
  , EConstructable edsl (EFix (PListF b))
  ) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PList a))
    (Term edsl (PList b))
    (Term edsl a)
    (Term edsl b)
plist = traversal plist'

