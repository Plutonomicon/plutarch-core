module Plutarch.Frontends.Harvard (PHarvard) where

import Plutarch.Core (PConstructable, PDSL)
import Plutarch.Frontends.Data (PAny, PSOP)
import Plutarch.Frontends.LC (PLC, PPolymorphic)
import Plutarch.Frontends.Untyped (PUntyped)

-- | A Harvard machine.
-- See https://en.wikipedia.org/wiki/Harvard_architecture
class
  ( PDSL e
  ) =>
  PHarvard e
