module Plutarch.Cont(pmatchCont) where
  
import Control.Monad.Trans.Cont

import Plutarch.Core

pmatchCont ::
  (
    EConstructable edsl a,
    IsEType edsl r
  ) =>
  (EConcrete edsl a -> Cont (Term edsl r) b) ->
  Term edsl a ->
  Cont (Term edsl r) b
pmatchCont cnt t = cont \c -> ematch t \con -> runCont (cnt con) c