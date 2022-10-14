module Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce)) where

import Plutarch.Core (IsPType, PDSL, Term)

class PDSL edsl => PUntyped edsl where
  punsafeCoerce :: (IsPType edsl a, IsPType edsl b) => Term edsl a -> Term edsl b
