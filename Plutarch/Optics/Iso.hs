{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Optics.Iso where

import Plutarch.Optics.Optic
import Plutarch.Optics.Profunctor

type PIso edsl s t a b = forall p. (IsPIso edsl p) => POptic p s t a b

type PIso' edsl s a = PIso edsl s s a a

class (PProfunctor edsl p) => IsPIso edsl p

instance (Functor f) => IsPIso edsl (PStar edsl f)