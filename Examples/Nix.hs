{-# LANGUAGE NoFieldSelectors #-}

module Examples.Nix (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
import Plutarch.Backends.Nix (compileAp)
import Plutarch.Frontends.Data (PFix (PFix), PAny)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Helpers (PForall, PForallF (PForallF), pforall)
import Plutarch.PType (pHs_inverse)
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

type PProxy :: forall k. PType -> PHs k -> PType
data PProxy a b ef = PProxy
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pproxy :: forall e k. (PNix e, IsPType e k) => Term e (PForall (PProxy @k))
pproxy = case pHs_inverse @k of Refl -> pforall $ pcon PProxy

newtype PConstF a b ef = PConstF (ef /$ a #-> b #-> a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pconst :: (PNix e) => Term e (PForall PConstF)
pconst = pforall $ pcon $ PConstF $ plam \x _y -> x

-- TODO: implement
-- psomeconst :: (PNix e) => Term e (PSome PConstF)
-- psomeconst = pforall $ pcon $ PConstF $ plam \(x :: T PUnit) (_y :: T PUnit) -> x

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
pvoid = pforall $ pcon $ PVoidF $ plam \x -> pmatch x \case {}

newtype PMyUnit ef = PMyUnit (ef /$ PUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

newtype PTopF a ef = PTopF (ef /$ a #-> PMyUnit)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

ptop :: (PNix e) => Term e (PForall PTopF)
ptop = pforall $ pcon $ PTopF $ plam $ const $$ PMyUnit $$ PUnit

psometop :: (PNix e) => Term e (PSome1 PTopF)
psometop = pcon $ PSome1 Proxy $ pcon $ PTopF $ plam \(_ :: T PUnit) -> pcon $ PMyUnit $$ PUnit

-- Taken from Unraveling recursion (2019) by Kireev et al.
newtype PSelfF a self ef = PSelfF (ef /$ (self #-> a))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)
newtype PSelf a ef = PSelf (ef /$ PFix (PSelfF a))
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pself :: (PNix e, IsPType e a) => Term e $ (PSelf a #-> a) #-> PSelf a
pself = plam \s -> pcon $ PSelf $ pcon $ PFix $ pcon $ PSelfF $ plam \x -> s # (pcon $ PSelf x)

punself :: (PNix e, IsPType e a) => Term e $ PSelf a #-> PSelf a #-> a
punself = plam \s -> pmatch s \case
  PSelf s' -> pmatch s' \case
    PFix s'' -> pmatch s'' \case
      PSelfF s''' -> plam \y -> s''' # (pmatch y \case PSelf y' -> y')

pselfApply :: (PNix e, IsPType e a) => Term e $ PSelf a #-> a
pselfApply = plam \s -> punself # s # s

pY :: (PNix e, IsPType e a) => Term e $ (a #-> a) #-> a
pY = plam \f -> (plam \z -> f # (pselfApply # z)) # (pself # (plam \z -> f # (pselfApply # z)))

newtype PYF a ef = PYF (ef /$ (a #-> a) #-> a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pYPoly :: PNix e => Term e (PForall PYF)
pYPoly = pforall $ pcon $ PYF pY

pfix :: forall e a b. (PNix e, IsPType e a, IsPType e b) => Term e $ ((a #-> b) #-> a #-> b) #-> a #-> b
pfix = plam \f -> fzz f # (pself # fzz f) where
  expand :: Term e (a #-> b) -> Term e (a #-> b)
  expand f = plam \x -> f # x
  fzz :: Term e ((a #-> b) #-> a #-> b) -> Term e (PSelf (a #-> b) #-> a #-> b)
  fzz f = plam \z -> f # (expand $ pselfApply # z)

data PNatF a ef = PN | PS (ef /$ a)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)
newtype PNat ef = PNat (ef /$ PFix PNatF)
  deriving stock (Generic)
  deriving anyclass (PHasRepr)

pplus :: forall e. PNix e => Term e $ PNat #-> PNat #-> PNat
pplus = pfix # (plam \self x y -> f self x y) where
  f :: Term e (PNat #-> PNat #-> PNat) -> Term e PNat -> Term e PNat -> Term e PNat
  f self x y = pmatch x \case
    PNat x' -> pmatch x' \case
      PFix x'' -> pmatch x'' \case
        PN -> y
        PS x''' -> pmatch (self # (pcon $ PNat x''') # y) \case
          PNat r -> pcon $ PNat $ pcon $ PFix $ pcon $ PS r

data PLib ef = PLib
  { pmutate :: ef /$ PMyTriple PAny PAny PAny #-> PMyTriple PAny PAny PAny
  , pconst :: ef /$ PForall PConstF
  , pswap :: ef /$ PMyEither PAny PAny #-> PMyEither PAny PAny
  , pvoid :: ef /$ PForall PVoidF
  , ptop :: ef /$ PForall PTopF
  , pproxy :: ef /$ PForall (PProxy @PUnit)
  , psometop :: ef /$ PSome1 PTopF
  , pYPoly :: ef /$ PForall PYF
  , pplus :: ef /$ PNat #-> PNat #-> PNat
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
      , psometop
      , pYPoly
      , pplus
      }

example :: Text
example = runIdentity $ compileAp (Proxy @PLib) plib
