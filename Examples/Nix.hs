{-# LANGUAGE NoFieldSelectors #-}

module Examples.Nix (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text, unpack)
import Plutarch.Backends.Nix (compileAp)
import Plutarch.Frontends.Data (PAny)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Prelude
import Plutarch.PType (pHs_inverse, PHsEf)
import Plutarch.Repr.Primitive (PReprPrimitive)
import Plutarch.Helpers (pforall, PForallNClass, PForallN(PForallN), PForallNF(PForallNF))
import Data.Type.Equality ((:~:)(Refl))

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

type PProxy :: forall k. PType -> PHs k -> PType
data PProxy a b ef = PProxy
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pproxy :: forall e k. PNix e => Term e (PForallN (PProxy @k))
pproxy = case pHs_inverse @k of Refl -> pcon $ PForallN $ pcon $ PForall $ pcon $ PForallNF $ pcon $ PForallN $ pcon $ PForall $ pcon $ PForallNF $ pcon $ PProxy

newtype PConstF a b ef = PConstF (ef /$ a #-> b #-> a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pconst :: (PNix e) => Term e (PForallN PConstF)
pconst = pforall $ pcon $ PConstF $ plam \x _y -> x

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

newtype PVoidF a ef = PVoidF (ef /$ PMyVoid #-> a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pvoid :: (PNix e) => Term e (PForall PVoidF)
pvoid = pcon $ PForall $ pcon $ PVoidF $ plam \x -> pmatch x \case {}

newtype PMyUnit ef = PMyUnit (ef /$ PUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

newtype PTopF a ef = PTopF (ef /$ a #-> PMyUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

ptop :: (PNix e) => Term e (PForall PTopF)
ptop = pcon $ PForall $ pcon $ PTopF $ plam $ const $$ PMyUnit $ pcon PUnit

data PLib ef = PLib
  -- FIXME: replace with foralls
  { pmutate :: ef /$ PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny
  , pconst :: ef /$ PForallN PConstF
  , pswap :: ef /$ PMyEither PAny PAny #-> PMyEither PAny PAny
  , pvoid :: ef /$ PForall PVoidF
  , ptop :: ef /$ PForall PTopF
  , pproxy :: ef /$ PForallN (PProxy @PUnit)
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
      , ptop
      , pproxy
      }

example :: Text
example = runIdentity $ compileAp (Proxy @PLib) plib

p :: IO ()
p = putStrLn $ unpack $ example
