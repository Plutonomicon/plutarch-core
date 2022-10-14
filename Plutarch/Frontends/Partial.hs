module Plutarch.Frontends.Partial (PPartial (perror)) where

import Plutarch.Core (IsPType, PDSL, PEffect, Term)

class PDSL edsl => PPartial edsl where
  -- \| In a strict backend, this will cause the computation to fail early,
  -- in a lazy backend, it might fail later or never.
  perror :: IsPType edsl a => PEffect edsl (Term edsl a)
