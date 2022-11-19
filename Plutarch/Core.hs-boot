module Plutarch.Core (PDSL (..), PDSLKind (..), IsPTypePrim (..)) where

import Plutarch.PType (PType, PHs)
import Data.Kind (Constraint, Type)

newtype PDSLKind = PDSLKind (PType -> Type)

class Monad (PEffect edsl) => PDSL (edsl :: PDSLKind) where
  data PEffect edsl :: Type -> Type
  data IsPTypePrimData edsl :: forall (a :: PType). PHs a -> Type

type IsPTypePrim :: PDSLKind -> forall (a :: PType). PHs a -> Constraint
class IsPTypePrim (edsl :: PDSLKind) (x :: PHs a) where
  isPTypePrim :: IsPTypePrimData edsl x
