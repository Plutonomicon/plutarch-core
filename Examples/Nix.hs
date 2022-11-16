module Examples.Nix (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (unpack)
import Plutarch.Backends.Nix (compileAp)
import Plutarch.Frontends.Data (PAny (PAny))
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Prelude

data PMyTriple a b c ef = PMyTriple
  { x :: ef /$ a
  , y :: ef /$ b
  , z :: ef /$ c
  }
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pconst' :: (PNix e) => Term e (PAny #-> PAny #-> PAny)
pconst' = plam \x _y -> x

pmutate' :: PNix e => Term e (PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny)
pmutate' = plam \t ->
  pcon $
    PMyTriple
      { x = t.y
      , y = t.z
      , z = t.x
      }

data PLib ef = PLib
  -- FIXME: replace with foralls
  { pmutate :: ef /$ PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny
  , pconst :: ef /$ PAny #-> PAny #-> PAny
  }
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

newtype PMyUnit ef = PMyUnit (ef /$ PUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

plib :: PNix e => Term e PLib
plib =
  pcon $
    PLib
      { pmutate = pmutate'
      , pconst = pconst'
      }

example :: IO ()
example = putStrLn $ unpack $ runIdentity $ compileAp (Proxy @PLib) plib
