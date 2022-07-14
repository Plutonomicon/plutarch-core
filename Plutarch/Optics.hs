module Plutarch.Optics where

import Data.Profunctor

import Fresnel.Lens
import Fresnel.Optic

import Plutarch.Core

type PLens edsl s t a b =
  Lens (Term edsl s) (Term edsl t) (Term edsl a) (Term edsl b)

type PLens' edsl s a = PLens edsl s s a a

class Profunctor p => PChoice p where
  pleft' :: p (Term edsl a) (Term edsl b) -> p (Term edsl (EEither a c)) (Term edsl (EEither b c))
  pright' :: p (Term edsl a) (Term edsl b) -> p (Term edsl (EEither c a)) (Term edsl (EEither c b))

type PPrism edsl s t a b =
  forall p. PChoice p =>
    Optic p (Term edsl s) (Term edsl t) (Term edsl a) (Term edsl b)

type PPrism' edsl s a = PPrism edsl s s a a

pprism ::
  (ESOP edsl, IsEType edsl t, IsEType edsl b) =>
  (Term edsl b -> Term edsl t) ->
  (Term edsl s -> Term edsl (EEither t a)) ->
  PPrism edsl s t a b
pprism inj prj = dimap prj (peither id inj) . pright'

pprism' ::
  (ESOP edsl, IsEType edsl s, IsEType edsl a, IsEType edsl b) =>
  (Term edsl b -> Term edsl s) ->
  (Term edsl s -> Term edsl (EEither EUnit a)) ->
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
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl a') =>
  PPrism edsl (EEither a b) (EEither a' b) a a'
_ELeft =
  pprism
    (econ . ELeft)
    (peither (econ . ERight) (econ . ELeft . econ . ERight))

_ERight ::
  (ESOP edsl, IsEType edsl a, IsEType edsl b, IsEType edsl b') =>
  PPrism edsl (EEither a b) (EEither a b') b b'
_ERight =
  pprism
    (econ . ERight)
    (peither (econ . ELeft . econ . ELeft) (econ . ERight))