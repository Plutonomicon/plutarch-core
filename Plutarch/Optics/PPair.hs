{-# LANGUAGE AllowAmbiguousTypes #-}

module Plutarch.Optics.PPair where

import Plutarch.Optics.Lens

import Plutarch.Core

pfst_ ::
  forall edsl a a' b.
  (IsEType edsl a, IsEType edsl a', IsEType edsl b) =>
  PLens edsl (EPair a b) (EPair a' b) a a'
pfst_ =
  plens @edsl
    (\tp -> ematch tp \(EPair a _) -> a)
    (\ts a' -> ematch ts \(EPair _ b) -> econ $ EPair a' b)

psnd_ ::
  forall edsl a b b'.
  (IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  PLens edsl (EPair a b) (EPair a b') b b'
psnd_ =
  plens @edsl
    (\tp -> ematch tp \(EPair _ b) -> b)
    (\ts b' -> ematch ts \(EPair a _) -> econ $ EPair a b')