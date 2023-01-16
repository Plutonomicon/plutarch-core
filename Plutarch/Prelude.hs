module Plutarch.Prelude (
  type (/$),
  type ($),
  ($$),
  PHasRepr (..),
  PConstructable,
  IsPType,
  PReprNewtype,
  PForall1 (..),
  PSome1 (..),
  PUnit (..),
  type (#->) (..),
  type (#=>) (..),
  Term,
  pcon,
  pmatch,
  Generic,
  plam,
  (#),
  PHs,
  PType,
  PTypeF,
  Constraint,
  Type,
  PPType,
  IsPType1,
  IsPType2,
  IsPType3,
  T,
  pany,
  PDSL,
) where

import Data.Kind (Constraint, Type)
import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.Frontends.Data
import Plutarch.Helpers
import Plutarch.PType
import Plutarch.Repr
import Plutarch.Repr.Newtype
