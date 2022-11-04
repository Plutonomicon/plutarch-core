module Examples.Nix (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text, unpack)
import Plutarch.Backends.Nix (compileAp, serialise)
import Plutarch.Frontends.Data (PAny (PAny))
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Prelude

example' :: (PNix e) => Term e (PAny #-> PAny #-> PAny #-> PAny)
example' = plam \x y z -> y

example :: IO ()
example = putStrLn $ unpack $ serialise $ runIdentity $ compileAp $ example'
