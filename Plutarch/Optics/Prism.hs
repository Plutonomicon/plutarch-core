{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Plutarch.Optics.Prism where

import Plutarch.Optics.Iso
import Plutarch.Optics.Optic
import Plutarch.Optics.Profunctor

import Plutarch.Core

type PPrism edsl s t a b = forall p. IsPPrism edsl p => POptic p s t a b

type PPrism' edsl s a = PPrism edsl s s a a

class (IsPIso edsl p, PChoice edsl p) => IsPPrism edsl p

pprism ::
  forall edsl s t a b.
  (ESOP edsl, IsEType edsl t, IsEType edsl a, IsEType edsl b) =>
  (b :--> t) edsl ->
  (s :--> EEither t a) edsl ->
  PPrism edsl s t a b
pprism inj prj = pdimap prj (peither id inj) . pright' @edsl

pprism' ::
  (ESOP edsl, IsEType edsl s, IsEType edsl t, IsEType edsl a, IsEType edsl b) =>
  (b :--> s) edsl ->
  (s :--> EEither t a) edsl ->
  PPrism edsl s s a b
pprism' inj prj =
  pprism
    inj
    ( \ts -> ematch (prj ts) \case
        ELeft _ -> econ $ ELeft ts
        ERight a -> econ $ ERight a
    )

newtype UnpackedPPrism edsl a b s t = UnpackedPPrism
  { withUnpackedPPrism ::
      forall r.
      ((b :--> t) edsl -> (s :--> EEither t a) edsl -> r) ->
      r
  }

unpackedPPrism ::
  (b :--> t) edsl ->
  (s :--> EEither t a) edsl ->
  UnpackedPPrism edsl a b s t
unpackedPPrism inj prj = UnpackedPPrism $ \k -> k inj prj

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PProfunctor edsl (UnpackedPPrism edsl a b)
  where
  pdimap f g (UnpackedPPrism r) =
    r $ \inj prj ->
      unpackedPPrism
        (g . inj)
        (peither (pleft . g) pright . prj . f)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PChoice edsl (UnpackedPPrism edsl a b)
  where
  pleft' (UnpackedPPrism r) =
    r $ \inj prj ->
      unpackedPPrism
        (pleft . inj)
        (peither
          (peither (pleft . pleft) pright . prj)
          (pleft . pright)
        )

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPIso edsl (UnpackedPPrism edsl a b)

instance
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  IsPPrism edsl (UnpackedPPrism edsl a b)

withPPrism ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b) =>
  PPrism edsl s t a b ->
  ((b :--> t) edsl -> (s :--> EEither t a) edsl -> r) ->
  r
withPPrism o = withUnpackedPPrism (o (unpackedPPrism id pright))