module Plutarch.Core (PDSLKind (PDSLKind), IsPTypePrim) where

import Plutarch.PType (PType, PHs)
import Data.Kind (Constraint, Type)

newtype PDSLKind = PDSLKind (PType -> Type)

type family IsPTypePrim (edsl :: PDSLKind) :: forall (a :: PType). PHs a -> Constraint
