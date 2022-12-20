module Plutarch.Internal.WithDictHack (unsafeWithDict) where

import Data.Proxy (Proxy)
import Unsafe.Coerce (unsafeCoerce)

newtype Helper b c = Helper ( b => c )

-- `a` MUST have same representation as `b`.
unsafeWithDict :: forall a b c. Proxy b -> a -> (b => c) -> c
unsafeWithDict _ x f = unsafeCoerce (Helper f :: Helper b c) x
