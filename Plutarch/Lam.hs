{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Lam (plam) where

import Data.Kind (Type)
import GHC.Stack (HasCallStack, withFrozenCallStack)
import Plutarch.Core (PConcrete, PConstructable, PDSLKind, Term, pcon, type (#->) (PLam))
import Plutarch.PType (PType)

plam' :: forall edsl a b. (HasCallStack, PConstructable edsl (a #-> b)) => (Term edsl a -> Term edsl b) -> Term edsl (a #-> b)
plam' f = pcon $ (PLam f :: PConcrete edsl (a #-> b))

class PLamN (a :: Type) (b :: PType) (edsl :: PDSLKind) | a -> b, edsl b -> a where
  plam :: forall c. (HasCallStack, PConstructable edsl (c #-> b)) => (Term edsl c -> a) -> Term edsl (c #-> b)

instance {-# OVERLAPPABLE #-} (a' ~ Term edsl a) => PLamN a' a edsl where
  plam = withFrozenCallStack plam'

instance (PConstructable edsl (a #-> b), a' ~ Term edsl a, PLamN b' b edsl) => PLamN (a' -> b') (a #-> b) edsl where
  plam f = withFrozenCallStack $ plam' $ \x -> plam (f x)
