module Plutarch.Internal.Unimplemented (Unimplemented, Error) where

import GHC.TypeLits (Symbol)

class Unimplemented (t :: Symbol)

type family Error (t :: Symbol) :: k where
