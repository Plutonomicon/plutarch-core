module Plutarch.Cont(pmatchCont) where
  
import Control.Monad.Trans.Cont

import Plutarch.Core

pmatchCont ::
  (
    PConstructable edsl a,
    IsPType edsl r
  ) =>
  (PConcrete edsl a -> Cont (Term edsl r) b) ->
  Term edsl a ->
  Cont (Term edsl r) b
pmatchCont cnt t = cont \c -> pmatch t \con -> runCont (cnt con) c