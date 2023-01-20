{-# LANGUAGE NoFieldSelectors #-}

module Examples.C (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
--import Plutarch.Backends.C (compileAp)
import Plutarch.Frontends.C (PC)
import Plutarch.Prelude

pinc1 :: PC e => Term e PInt -> Term e PInt
pinc1 x = x + 1

data PMyModule ef = PMyModule
  { pinc1 :: ef /$ PUnit
  }

example :: Text
example = undefined -- runIdentity $ compileAp (Proxy @PLib) plib
