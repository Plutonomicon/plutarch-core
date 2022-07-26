{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Optics.Traversal where

import Plutarch.Core

import Plutarch.Optics.Optic
import Plutarch.Optics.Optional
import Plutarch.Optics.Profunctor

type PTraversal edsl s t a b =
  forall p.
  (IsPTraversal edsl p) =>
  POptic p s t a b

type PTraversal' edsl s a = PTraversal edsl s s a a

class (IsPOptional edsl p, PMonoidal edsl p) => IsPTraversal edsl p

instance (ESOP edsl, Applicative f) => IsPTraversal edsl (PStar edsl f)

traverseOf :: (ESOP edsl, Applicative f) => PTraversal edsl s t a b -> (Term edsl a -> f (Term edsl b)) -> (Term edsl s -> f (Term edsl t))
traverseOf p = unPStar . p . PStar
