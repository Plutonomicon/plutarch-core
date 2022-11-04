module Plutarch.Internal.CoerceTo (CoerceTo) where

import Data.Kind (Type)

type CoerceTo :: forall a. forall (b :: Type) -> a -> b
type family CoerceTo (b :: Type) (x :: a) :: b where
  CoerceTo _ x = x

