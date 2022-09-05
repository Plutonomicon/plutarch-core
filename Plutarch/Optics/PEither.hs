module Plutarch.Optics.PEither where

import Plutarch.CPS.Optics.Prism

import Plutarch.Core
import Plutarch.Cont

_PLeft ::
  (PSOP edsl, IsPType edsl a, IsPType edsl a', IsPType edsl b, IsPType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (PEither a b))
    (Term edsl (PEither a' b))
    (Term edsl a)
    (Term edsl a')
_PLeft =
  cprism
    (return . pleft)
    (pmatchCont \case
      PLeft a -> return $ Right a
      PRight b -> return $ Left (pright b)
    )

_PRight ::
  (PSOP edsl, IsPType edsl a, IsPType edsl b, IsPType edsl b', IsPType edsl r) =>
  CPrism
    (Term edsl r)
    (Term edsl (PEither a b))
    (Term edsl (PEither a b'))
    (Term edsl b)
    (Term edsl b')
_PRight =
  cprism
    (return . pright)
    (pmatchCont \case
        PLeft a -> return $ Left (pleft a)
        PRight b -> return $ Right b
    )
