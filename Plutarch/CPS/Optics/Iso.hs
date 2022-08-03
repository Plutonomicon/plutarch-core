{-# LANGUAGE FlexibleInstances #-}

module Plutarch.CPS.Optics.Iso where
  
import Plutarch.CPS.Optics.Optic
import Plutarch.CPS.Profunctor

type CIso r s t a b = forall p. (IsCIso r p) => COptic r p s t a b

type CIso' r s a = CIso r s s a a

class (CProfunctor r p) => IsCIso r p

instance IsCIso r (->)
instance (Functor f) => IsCIso r (CStar r f)