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

instance PProfunctor edsl (UnpackedPLens edsl a b) where
  pdimap f g (UnpackedPLens r) =
    r \get set -> unpackedPLens (get . f) (unTermF . prmap g . TermF . set . f)

instance
  (ESOP edsl, IsEType edsl a) =>
  PStrong edsl (UnpackedPLens edsl a b)
  where
  pfirst' (UnpackedPLens r) =
    r \get set ->
      unpackedPLens
        (\tp -> ematch tp \(EPair a _) -> get a)
        (\tp b -> ematch tp \(EPair a c) -> econ $ EPair (set a b) c)

instance IsPIso edsl (UnpackedPLens edsl a b)
instance (ESOP edsl, IsEType edsl a) => IsPLens edsl (UnpackedPLens edsl a b)

withPLens ::
  forall edsl s t a b r.
  (ESOP edsl, IsEType edsl a) =>
  PLens edsl s t a b ->
  (((s :--> a) edsl -> (Term edsl s -> Term edsl b -> Term edsl t) -> r) -> r)
withPLens o = withUnpackedPLens (o (unpackedPLens id (const id)))

unpackedPLens ::
  (s :--> a) edsl ->
  (Term edsl s -> Term edsl b -> Term edsl t) ->
  UnpackedPLens edsl a b s t
unpackedPLens get set = UnpackedPLens $ \k -> k get set

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
