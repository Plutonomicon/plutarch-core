{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Optics.Lens where

import Plutarch.Core

import Plutarch.Optics.Iso
import Plutarch.Optics.Optic
import Plutarch.Optics.Profunctor

type PLens edsl s t a b = forall p. IsPLens edsl p => POptic p s t a b

type PLens' edsl s a = PLens edsl s s a a

class (IsPIso edsl p, PStrong edsl p) => IsPLens edsl p

plens ::
  forall edsl s t a b.
  (ESOP edsl, IsEType edsl s, IsEType edsl t, IsEType edsl a, IsEType edsl b) =>
  (s :--> a) edsl ->
  (Term edsl s -> Term edsl b -> Term edsl t) ->
  PLens edsl s t a b
plens get set = pdimap (id `pand` get) (puncurry set) . psecond' @edsl

newtype UnpackedPLens edsl a b s t = UnpackedPLens
  { withUnpackedPLens ::
      forall r.
      ((s :--> a) edsl -> (Term edsl s -> Term edsl b -> Term edsl t) -> r) ->
      r
  }

pand ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  (s :--> a) edsl ->
  (s :--> b) edsl ->
  (s :--> EPair a b) edsl
pand sa sb s = econ $ EPair (sa s) (sb s)

puncurry ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c) =>
  (Term edsl a -> Term edsl b -> Term edsl c) ->
  (EPair a b :--> c) edsl
puncurry f tp = ematch tp \(EPair a b) -> f a b

data ConcreteLens edsl a b s t = ConcreteLens
  { plensGet :: (s :--> a) edsl
  , plensSet :: Term edsl b -> Term edsl s -> Term edsl t
  }

instance PProfunctor edsl (ConcreteLens edsl a b) where
  pdimap f g o = ConcreteLens (plensGet o . f) (\b -> g . plensSet o b . f)

instance
  (ESOP edsl, IsEType edsl a) =>
  PStrong edsl (ConcreteLens edsl a b)
  where
  pfirst' o =
    ConcreteLens
      (\p -> ematch p \(EPair a _) -> plensGet o a)
      (\b p -> ematch p \(EPair a c) -> econ $ EPair (plensSet o b a) c)

  psecond' o =
    ConcreteLens
      (\p -> ematch p \(EPair _ a) -> plensGet o a)
      (\b p -> ematch p \(EPair c a) -> econ $ EPair c (plensSet o b a))

instance IsPIso edsl (ConcreteLens edsl a b)
instance (ESOP edsl, IsEType edsl a) => IsPLens edsl (ConcreteLens edsl a b)
