module Plutarch.Prelude (
  type (/$),
  type ($),
  ($$),
  PHasRepr (..),
  PConstructable,
  IsPType,
  PReprSOP,
  PForall (..),
  PSome (..),
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
  PPType,
  IsPType1,
  IsPType2,
  IsPType3,
) where

import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.Frontends.Data
import Plutarch.Helpers
import Plutarch.PType

($$) :: PConstructable edsl a => (Term edsl a -> b) -> PConcrete edsl a -> b
f $$ x = f (pcon x)
infixr 0 $$

type f $ x = f x
infixr 0 $
