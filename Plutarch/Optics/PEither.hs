{-# LANGUAGE AllowAmbiguousTypes #-}

module Plutarch.Optics.PEither where

import Plutarch.Optics.Prism

import Plutarch.Core

_PLeft ::
  forall edsl a a' b.
  (IsEType edsl a, IsEType edsl a', IsEType edsl b) =>
  PPrism edsl (EEither a b) (EEither a' b) a a'
_PLeft = pprism @edsl pleft (peither pright (pleft . pright))

_PRight ::
  forall edsl a b b'.
  (IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  PPrism edsl (EEither a b) (EEither a b') b b'
_PRight = pprism @edsl pright (peither (pleft . pleft) pright)