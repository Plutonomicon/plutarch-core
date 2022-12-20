{-# LANGUAGE NoFieldSelectors #-}

module Examples.Nix (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text, unpack)
import Plutarch.Backends.Nix (compileAp)
import Plutarch.Frontends.Data (PAny)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Prelude

data PMyTriple a b c ef = PMyTriple
  { x :: ef /$ a
  , y :: ef /$ b
  , z :: ef /$ c
  }
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

data PMyEither a b ef = PMyLeft (ef /$ a) | PMyRight (ef /$ b)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

data PMyVoid ef
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pconst :: (PNix e) => Term e (PAny #-> PAny #-> PAny)
pconst = plam \x _y -> x

pmutate :: PNix e => Term e (PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny)
pmutate = plam \t ->
  pcon $
    PMyTriple
      { x = t.y
      , y = t.z
      , z = t.x
      }

pswap :: (PNix e, IsPType e a, IsPType e b) => Term e (PMyEither a b #-> PMyEither b a)
pswap = plam \x -> pmatch x \case
  PMyLeft l -> pcon $ PMyRight l
  PMyRight r -> pcon $ PMyLeft r

data PVoidF a ef = PVoidF (ef /$ PMyVoid #-> a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pvoid :: (PNix e) => Term e (PForall PVoidF)
pvoid = pcon $ PForall $ pcon $ PVoidF $ plam \x -> pmatch x \case {}

newtype PMyUnit ef = PMyUnit (ef /$ PUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

ptop :: (PNix e, IsPType e a) => Term e (a #-> PMyUnit)
ptop = plam $ const $$ PMyUnit $ pcon PUnit

data PLib ef = PLib
  -- FIXME: replace with foralls
  { pmutate :: ef /$ PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny
  , pconst :: ef /$ PAny #-> PAny #-> PAny
  , pswap :: ef /$ PMyEither PAny PAny #-> PMyEither PAny PAny
  , pvoid :: ef /$ PForall PVoidF
  }
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

plib :: PNix e => Term e PLib
plib =
  pcon $
    PLib
      { pmutate
      , pconst
      , pswap
      , pvoid
      }

example :: Text
example = runIdentity $ compileAp (Proxy @PLib) plib

p :: IO ()
p = putStrLn $ unpack $ example
