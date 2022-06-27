module Plutarch.Do ((>>), (>>=)) where

import Plutarch.Core
import Prelude hiding (fail, (>>=))

-- (>>) :: Term s a -> Term s b -> Term s b
-- (>>) = id

(>>=) :: ((a -> Term edsl b) -> Term edsl b) -> (a -> Term edsl b) -> Term edsl b
(>>=) f x = f x

{-# DEPRECATED fail "oh no" #-}
fail :: a
fail = undefined
