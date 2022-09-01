{-# LANGUAGE FlexibleInstances #-}

module Plutarch.CPS.Optics.Lens where

import Control.Monad
import Control.Monad.Trans.Cont
import Plutarch.CPS.Optics.Iso
import Plutarch.CPS.Optics.Optic
import Plutarch.CPS.Profunctor

type CLens r s t a b = forall p. (IsCLens r p) => COptic r p s t a b

type CLens' r s a = CLens r s s a a

class (IsCIso r p, CStrong r p) => IsCLens r p

instance (Functor f) => IsCLens r (CStar r f)

clens :: (s -> Cont r a) -> (s -> b -> Cont r t) -> CLens r s t a b
clens get set = cdimap (\s -> (s,) <$> get s) (uncurry set) . csecond'

withCLens :: CLens r s t a b -> ((s -> Cont r a) -> (s -> b -> Cont r t) -> r') -> r'
withCLens o f = f (clensGet l) (clensSet l)
  where
    l = o $ ConcreteLens {clensGet = return, clensSet = const return}

data ConcreteLens r a b s t = ConcreteLens
  { clensGet :: s -> Cont r a
  , clensSet :: s -> b -> t
  }

instance CProfunctor r (ConcreteLens r a b) where
  cdimap ab cd l =
    ConcreteLens
      { clensGet = ab >=> clensGet l
      , clensSet = \a b -> ab a >>= \b' -> clensSet l b' b >>= cd
      }

instance CStrong r (ConcreteLens r a b) where
  cfirst' l =
    ConcreteLens
      { clensGet = clensGet l . fst
      , clensSet = \(a, c) b -> (,c) <$> clensSet l a b
      }

instance IsCIso r (ConcreteLens r a b)
instance IsCLens r (ConcreteLens r a b)
