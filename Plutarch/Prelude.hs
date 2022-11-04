module Plutarch.Prelude (
  type (/$),
  type ($),
  ($$),
  PHasRepr (..),
  PConstructable,
  IsPType,
  PReprNewtype,
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
  T,
  pany,
) where

import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.Frontends.Data
import Plutarch.Helpers
import Plutarch.PType
import Plutarch.Repr
import Plutarch.Repr.Newtype

($$) :: PConstructable edsl a => (Term edsl a -> b) -> PConcrete edsl a -> b
f $$ x = f (pcon x)
infixr 0 $$

type f $ x = f x
infixr 0 $
