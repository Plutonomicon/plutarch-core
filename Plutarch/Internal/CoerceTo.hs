module Plutarch.Internal.CoerceTo (Coerce, CoerceTo) where

import Data.Kind (Type)

type CoerceTo :: forall a. forall (b :: Type) -> a -> b
type family CoerceTo (b :: Type) (x :: a) :: b where
  CoerceTo _ x = x

type Coerce :: forall a b. a -> b
type family Coerce (x :: a) :: b where
  Coerce x = x
