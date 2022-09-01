module Plutarch.Optics.PEither where

import Plutarch.CPS.Optics.Prism

import Plutarch.Core
import Plutarch.Cont

_PLeft ::
  (ESOP edsl, IsEType edsl a, IsEType edsl a', IsEType edsl b, IsEType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (EEither a b))
    (Term edsl (EEither a' b))
    (Term edsl a)
    (Term edsl a')
_PLeft =
  cprism
    (return . pleft)
    (pmatchCont \case
      ELeft a -> return $ Right a
      ERight b -> return $ Left (pright b)
    )

_PRight ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b', IsEType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (EEither a b))
    (Term edsl (EEither a b'))
    (Term edsl b)
    (Term edsl b')
_PRight =
  cprism
    (return . pright)
    (pmatchCont \case
        ELeft a -> return $ Left (pleft a)
        ERight b -> return $ Right b
    )
