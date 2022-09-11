module Plutarch.Optics.PList where

import Plutarch.CPS.Optics.Traversal
import Plutarch.Core
import Plutarch.PList
import Plutarch.Optics.Fix
import Plutarch.CPS.Profunctor
import Plutarch.Cont

plist
  ::
  ( PTraversible edsl PListF
  , PConstructable edsl (PList a)
  , PConstructable edsl (PList b)
  , PConstructable edsl r) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PList a))
    (Term edsl (PList b))
    (Term edsl a)
    (Term edsl b)
plist =
  cdimap (pmatchCont (\(PList as) -> return as)) (return . pcon . PList)
    . plist'

plist'
  ::
  ( PTraversible edsl PListF
  , PConstructable edsl r) =>
  CTraversal
    (Term edsl r)
    (Term edsl (PFix (PListF a)))
    (Term edsl (PFix (PListF b)))
    (Term edsl a)
    (Term edsl b)
plist' = ptraverse