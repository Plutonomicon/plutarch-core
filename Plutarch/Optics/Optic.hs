module Plutarch.Optics.Optic (
  POptic,
  POptic',
) where

type POptic p s t a b = p a b -> p s t

type POptic' p s a = POptic p s s a a
