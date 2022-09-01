{-# LANGUAGE FlexibleInstances #-}

module Plutarch.CPS.Optics.Prism where

import Control.Monad
import Control.Monad.Trans.Cont
import Plutarch.CPS.Optics.Iso
import Plutarch.CPS.Optics.Optic
import Plutarch.CPS.Profunctor

type CPrism r s t a b = forall p. IsCPrism r p => COptic r p s t a b

type CPrism' r a b = CPrism r a a b b

class (IsCIso r p, CChoice r p) => IsCPrism r p

instance (Applicative f) => IsCPrism r (CStar r f)

cprism :: (b -> Cont r t) -> (s -> Cont r (Either t a)) -> CPrism r s t a b
cprism inj prj = cdimap prj (either return inj) . cright'

cprism' :: (b -> Cont r s) -> (s -> Cont r (Maybe a)) -> CPrism r s s a b
cprism' inj prj = cprism inj (\s -> prj s >>= maybe (return $ Left s) (return . Right))

withCPrism ::
  CPrism r s t a b ->
  ((b -> Cont r t) -> (s -> Cont r (Either t a)) -> r') ->
  r'
withCPrism o f =
  f (cprismSet l) (cprismGet l >=> either (fmap Left) (return . Right))
  where
    l = o $ ConcretePrism {cprismSet = return, cprismGet = return . Right}

data ConcretePrism r a b s t = ConcretePrism
  { cprismGet :: s -> Cont r (Either t a)
  , cprismSet :: b -> t
  }

instance CProfunctor r (ConcretePrism r a b) where
  cdimap ab cd p =
    ConcretePrism
      { cprismGet =
          ab
            >=> cprismGet p
            >=> either
              (\c -> Left . return <$> (c >>= cd))
              (return . Right)
      , cprismSet = cprismSet p >=> cd
      }

instance CChoice r (ConcretePrism r a b) where
  cleft' p =
    ConcretePrism
      { cprismGet =
          either
            (cprismGet p >=> either (fmap (Left . return . Left)) (return . Right))
            (return . Left . return . Right)
      , cprismSet = fmap Left . cprismSet p
      }

instance IsCIso r (ConcretePrism r a b)
instance IsCPrism r (ConcretePrism r a b)
