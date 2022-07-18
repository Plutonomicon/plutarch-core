{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Plutarch.Optics where

import Data.Profunctor

import Fresnel.Lens

import Plutarch.Core

type (:-->) a b edsl = Term edsl a -> Term edsl b

-- Lenses CAN be expressed as regular Haskell-level lenses.

type PLens edsl s t a b =
  Lens (Term edsl s) (Term edsl t) (Term edsl a) (Term edsl b)

type PLens' edsl s a = PLens edsl s s a a

-- Prisms cannot, and need a dedicated profunctor hierarchy, because of the non-standard Either type.

class PProfunctor edsl p where
  pdimap ::
    (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c, IsEType edsl d) =>
    (a :--> b) edsl ->
    (c :--> d) edsl ->
    p b c ->
    p a d

-- Every Profunctor is a PProfunctor. This allows rudimentary composition of prisms and lenses.

newtype PPro edsl p a b = PPro { unPPro :: p (Term edsl a) (Term edsl b) }

instance Profunctor p => PProfunctor edsl (PPro edsl p) where
  pdimap ab cd (PPro p) = PPro (dimap ab cd p)

class (PProfunctor edsl p) => PChoice edsl p where
  pleft' :: (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c) => p a b -> p (EEither a c) (EEither b c)
  pleft' = pdimap @edsl (peither pright pleft) (peither pright pleft) . pright' @edsl

  pright' :: (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl c) =>  p a b -> p (EEither c a) (EEither c b)
  pright' = pdimap @edsl (peither pright pleft) (peither pright pleft) . pleft' @edsl

type PPrism edsl s t a b =
  forall p. (PChoice edsl p) => p a b -> p s t

type PPrism' edsl s a = PPrism edsl s s a a

newtype UnpackedPPrism edsl a b s t
  = UnpackedPPrism
  { withUnpackedPPrism ::
      forall r.
      ((b :--> t) edsl -> (s :--> EEither t a) edsl -> r) ->
      r
  }

unpackedPPrism :: (b :--> t) edsl -> (s :--> EEither t a) edsl -> UnpackedPPrism edsl a b s t
unpackedPPrism inj prj = UnpackedPPrism $ \k -> k inj prj

withPPrism :: (ESOP edsl, IsEType edsl a, IsEType edsl b) => PPrism edsl s t a b -> (((b :--> t) edsl -> (s :--> EEither t a) edsl -> r) -> r)
withPPrism o = withUnpackedPPrism (o (unpackedPPrism id pright))

instance (ESOP edsl, IsEType edsl a) => PProfunctor edsl (UnpackedPPrism edsl a b) where
  pdimap f g (UnpackedPPrism r) =
    r $ \inj prj -> unpackedPPrism (g . inj) (peither (pleft . g) pright . prj . f)

instance (ESOP edsl, IsEType edsl a) => PChoice edsl (UnpackedPPrism edsl a b) where
  pleft' (UnpackedPPrism r) =
    r $ \inj prj -> unpackedPPrism (pleft . inj) (peither (peither (pleft . pleft) pright . prj) (pleft . pright))

pprism ::
  forall edsl s t a b.
  (ESOP edsl, IsEType edsl s, IsEType edsl t, IsEType edsl a, IsEType edsl b) =>
  (b :--> t) edsl ->
  (s :--> EEither t a) edsl ->
  PPrism edsl s t a b
-- pprism inj prj = pdimap prj (peither id inj) . pright'
pprism inj prj = pdimap prj (peither id inj) . pright' @edsl


pprism' ::
  (ESOP edsl, IsEType edsl s, IsEType edsl a, IsEType edsl b) =>
  (b :--> s) edsl ->
  (s :--> EEither EUnit a) edsl ->
  PPrism edsl s s a b
pprism' inj prj = pprism inj (\ts -> ematch (prj ts) \case
  ELeft _-> econ $ ELeft ts
  ERight b -> econ $ ERight b)

pfst_ ::
  (ESOP edsl, IsEType edsl a, IsEType  edsl b, IsEType edsl a') =>
  PLens edsl (EPair a b) (EPair a' b) a a'
pfst_ =
  lens
    (\tp -> ematch tp \(EPair a _) -> a)
    (\tp a -> ematch tp \(EPair _ b) -> econ $ EPair a b)

psnd_ ::
  (ESOP edsl, IsEType edsl a, IsEType  edsl b, IsEType edsl b') =>
  PLens edsl (EPair a b) (EPair a b') b b'
psnd_ =
  lens
    (\tp -> ematch tp \(EPair _ b) -> b)
    (\tp b -> ematch tp \(EPair a _) -> econ $ EPair a b)

_ELeft ::
  forall edsl a b a'.
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl a') =>
  PPrism edsl (EEither a b) (EEither a' b) a a'
_ELeft =
  pprism @edsl
    pleft
    (peither pright (pleft . pright))

_ERight ::
  forall edsl a b b'.
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  PPrism edsl (EEither a b) (EEither a b') b b'
_ERight =
  pprism @edsl
    pright
    (peither (pleft . pleft) pright)