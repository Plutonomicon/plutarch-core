module Plutarch.Lam (plam) where

class ELamN (a :: Type) (b :: EType) (s :: S) | a -> b, s b -> a where
  elam :: forall c. (Term s c -> a) -> Term s (c :--> b)

instance {-# OVERLAPPABLE #-} (a' ~ Term s a) => ELamN a' a s where
  elam = elam'

instance (a' ~ Term s a, ELamN b' b s) => ELamN (a' -> b') (a :--> b) s where
  elam f = elam' $ \x -> elam (f x)
