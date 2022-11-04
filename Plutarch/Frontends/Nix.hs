{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Frontends.Nix (PNix) where
    
import Plutarch.Core (PDSL, PConstructable)
import Plutarch.Frontends.LC (PLC, PPolymorphic)
import Plutarch.Frontends.Untyped (PUntyped)
import Plutarch.Frontends.Data (PAny, PSOP)

class
  ( PDSL e
  , PUntyped e
  , PLC e
  -- , PPolymorphic e
  , PConstructable e PAny
  , PSOP e
  ) => PNix e where
