module Examples.Nix (example) where

import Plutarch.Prelude
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Backends.Nix (compileAp, serialise)
import Data.Text (Text, unpack)
import Plutarch.Frontends.Data (PAny (PAny))
import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))

example' :: (PNix e) => Term e (PAny #-> PAny #-> PAny #-> PAny)
example' = plam \x y z -> y

example :: IO ()
example = putStrLn $ unpack $ serialise $ runIdentity $ compileAp $ example'
