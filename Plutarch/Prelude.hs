module Plutarch.Prelude (
  type (/$),
  type ($),
  ($$),
  EHasRepr (..),
  EConstructable,
  IsEType,
  EReprSOP,
  EForall (..),
  ESome (..),
  EUnit (..),
  type (#->) (..),
  type (#=>) (..),
  Term,
  econ,
  ematch,
  Generic,
  elam,
  (#),
  EHs,
  EType,
  EEType,
) where

import GHC.Generics (Generic)
import Plutarch.Core
import Plutarch.EType

($$) :: EConstructable edsl a => (Term edsl a -> b) -> EConcrete edsl a -> b
f $$ x = f (econ x)
infixr 0 $$

type f $ x = f x
infixr 0 $
