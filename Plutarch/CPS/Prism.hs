module Plutarch.CPS.Prism where
  
import Data.Profunctor

import Fresnel.Optic
import Fresnel.Iso

import Plutarch.CPS.Profunctor

type CPSPrism s t a b = forall p. IsCPSPrism p => Optic p s t a b

type CPSPrism' s a = CPSPrism s s a a

class (IsIso p, CPSChoice p) => IsCPSPrism p

cpsPrism :: (b -> t) -> (s -> CPSEither t a) -> CPSPrism s t a b
cpsPrism inj prj = dimap prj (\e -> e id inj) . cpsRight'

cpsPrism' ::
  (b -> s) ->
  (s -> (a -> (CPSEither s a)) -> CPSEither s a -> CPSEither s a) ->
  CPSPrism s s a b
cpsPrism' inj prj = cpsPrism inj (\s -> prj s cpsRight (cpsLeft s))

withCPSPrism ::
  CPSPrism s t a b ->
  (((b -> t) -> (s -> CPSEither t a) -> r) -> r)
withCPSPrism p u = u (prismSet c) (prismGet c)
  where
    c = p $ ConcretePrism id cpsRight

data ConcretePrism a b s t
  = ConcretePrism
  { prismSet :: b -> t
  , prismGet :: s -> CPSEither t a
  }

instance Functor (ConcretePrism a b s) where
  fmap = rmap

instance Profunctor (ConcretePrism a b) where
  dimap f g p
    = ConcretePrism
    { prismSet = g . prismSet p
    , prismGet = cpsLeft' g . prismGet p . f
    }

instance CPSChoice (ConcretePrism a b) where
  cpsLeft' p
    = ConcretePrism
      (cpsLeft . prismSet p)
      (\e -> e ((\e' -> e' (cpsLeft . cpsLeft) cpsRight) . prismGet p) (cpsLeft . cpsRight))

instance IsIso (ConcretePrism a b)
instance IsCPSPrism (ConcretePrism a b)