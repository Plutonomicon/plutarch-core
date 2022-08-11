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
  econ,
  ematch,
  Generic,
  elam,
  (#),
  PHs,
  PType,
  PPType,
) where

import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.PType

($$) :: PConstructable edsl a => (Term edsl a -> b) -> PConcrete edsl a -> b
f $$ x = f (econ x)
infixr 0 $$

type f $ x = f x
infixr 0 $
