module Plutarch.Core (PDSLKind (PDSLKind), IsPType') where

import Plutarch.PType (PType, PHs)
import Data.Kind (Constraint, Type)

newtype PDSLKind = PDSLKind (PType -> Type)

type family IsPType' (edsl :: PDSLKind) :: forall (a :: PType). PHs a -> Constraint
