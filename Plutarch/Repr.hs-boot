module Plutarch.Repr (PReprKind (PReprKind)) where

import Data.Kind (Type)

newtype PReprKind = PReprKind Type
