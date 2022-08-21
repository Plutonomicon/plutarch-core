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
) where

import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.Lam
import Plutarch.PType

($$) :: PConstructable edsl a => (Term edsl a -> b) -> PConcrete edsl a -> b
f $$ x = f (pcon x)
infixr 0 $$

type f $ x = f x
infixr 0 $
