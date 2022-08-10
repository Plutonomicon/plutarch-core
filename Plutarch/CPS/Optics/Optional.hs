{-# LANGUAGE FlexibleInstances #-}
module Plutarch.CPS.Optics.Optional where

import Plutarch.CPS.Optics.Optic
import Plutarch.CPS.Optics.Lens
import Plutarch.CPS.Optics.Prism

import Control.Monad.Cont
import Plutarch.CPS.Optics.Iso
import Plutarch.CPS.Profunctor
import Control.Arrow

type COptional r s t a b = forall p. (IsCOptional r p) => COptic r p s t a b

type COptional' r s a = COptional r s s a a

class (IsCLens r p, IsCPrism r p) => IsCOptional r p

instance (Applicative f) => IsCOptional r (CStar r f)

withCOptional :: COptional r s t a b -> ((s -> Cont r (Either t a)) -> (s -> b -> Cont r t) -> r') -> r'
withCOptional o f = f (coptionalGet l >=> either (fmap Left) (return . Right)) (coptionalSet l)
  where l = o $ ConcreteOptional { coptionalGet = return . Right, coptionalSet = const return }

data ConcreteOptional r a b s t
  = ConcreteOptional
  { coptionalGet :: s -> Cont r (Either t a)
  , coptionalSet :: s -> b -> t
  }

instance CProfunctor r (ConcreteOptional r a b) where
  cdimap ab cd o
    = ConcreteOptional
    { coptionalGet =
      ab >=> coptionalGet o >=> return . left (>>= cd)
    , coptionalSet = \a b -> ab a >>= \b' -> coptionalSet o b' b >>= cd
    }

instance CStrong r (ConcreteOptional r a b) where
  cfirst' o
    = ConcreteOptional
    { coptionalGet = \(a, c) -> left (fmap (,c)) <$> coptionalGet o a
    , coptionalSet = \(a, c) b -> (,c) <$> coptionalSet o a b
    }

  csecond' o
    = ConcreteOptional
    { coptionalGet = \(c, a) -> left (fmap (c,)) <$> coptionalGet o a
    , coptionalSet = \(c, a) b -> (c,) <$> coptionalSet o a b
    }

instance CChoice r (ConcreteOptional r a b) where
  cleft' o
    = ConcreteOptional
    { coptionalGet =
        either
          (coptionalGet o >=>
            return . left (fmap Left))
          (return . Left . return . Right)
    , coptionalSet =
      \e b -> either (\a -> Left <$> coptionalSet o a b) (return . Right) e
    }

  cright' o
    = ConcreteOptional
    { coptionalGet =
        either
          (return . Left . return . Left)
          (coptionalGet o >=>
            return . left (fmap Right))
    , coptionalSet =
      \e b -> either (return . Left) (\a -> Right <$> coptionalSet o a b) e
    }

instance IsCIso r (ConcreteOptional r a b)
instance IsCLens r (ConcreteOptional r a b)
instance IsCPrism r (ConcreteOptional r a b)
instance IsCOptional r (ConcreteOptional r a b)