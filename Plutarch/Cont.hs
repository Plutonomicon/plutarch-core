module Plutarch.Cont(PCont, pmatchCont) where

import Control.Monad.Trans.Cont

import Plutarch.Core

type PCont edsl r = Cont (Term edsl r)

pmatchCont ::
  (
    PConstructable edsl a,
    IsPType edsl r
  ) =>
  (PConcrete edsl a -> PCont edsl r b) ->
  Term edsl a ->
  PCont edsl r b
pmatchCont cnt t = cont \c -> pmatch t \con -> runCont (cnt con) c