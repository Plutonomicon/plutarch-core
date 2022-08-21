{-# LANGUAGE FlexibleInstances #-}

module Plutarch.CPS.Optics.Traversal where

import Control.Monad.Cont
import Plutarch.CPS.Optics.Optic
import Plutarch.CPS.Optics.Optional
import Plutarch.CPS.Profunctor

type CTraversal r s t a b = forall p. (IsCTraversal r p) => COptic r p s t a b

type CTraversal' r s a = CTraversal r s s a a

class (IsCOptional r p, CMonoidal r p) => IsCTraversal r p

instance (Applicative f) => IsCTraversal r (CStar r f)

ctraverse :: (CChoice r p, CMonoidal r p) => p a (Cont r b) -> p (FunList a c t) (Cont r (FunList b c t))
ctraverse k = cdimap (return . unFunList) (return . FunList) . cright' $ cpar k (ctraverse k)

ctraverseOf ::
  (Applicative f) =>
  CTraversal r s t a b ->
  (a -> Cont r (f b)) ->
  s ->
  Cont r (f (Cont r t))
ctraverseOf p = runCStar . p . CStar . (fmap . fmap . fmap) return

newtype FunList a b t = FunList {unFunList :: Either t (a, FunList a b (b -> t))}

single :: a -> FunList a b b
single a = FunList $ Right (a, FunList $ Left id)

instance Functor (FunList a b) where
  fmap f (FunList (Left t)) = FunList (Left (f t))
  fmap f (FunList (Right (a, as))) = FunList (Right (a, fmap (f .) as))

instance Applicative (FunList a b) where
  pure = FunList . Left
  FunList (Left f) <*> l' = fmap f l'
  FunList (Right (a, l)) <*> l' = FunList (Right (a, fmap flip l <*> l'))

fuse :: FunList b b t -> Cont r t
fuse = either return (\(a, c) -> ($ a) <$> fuse c) . unFunList

newtype ConcreteTraversal r s t a b = ConcreteTraversal {unConcreteTraversal :: s -> Cont r (FunList a b t)}

traversal :: (s -> Cont r (FunList a b t)) -> CTraversal r s t a b
traversal h = cdimap h fuse . ctraverse
