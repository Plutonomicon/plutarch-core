{-# OPTIONS_GHC -Wno-unused-foralls #-}

module Plutarch.TermCont (TermCont, unTermCont, tcont, runTermCont) where

import Data.Kind (Type)
import Plutarch.Core (IsPType, PDSLKind, Term)
import Plutarch.PType (PType)

newtype TermCont :: forall (r :: PType). PDSLKind -> Type -> Type where
  TermCont :: forall r e a. {runTermCont :: IsPType e r => ((a -> Term e r) -> Term e r)} -> TermCont @r e a

unTermCont :: IsPType e a => TermCont @a e (Term e a) -> Term e a
unTermCont t = runTermCont t id

instance Functor (TermCont e) where
  fmap f (TermCont g) = TermCont $ \h -> g (h . f)

instance Applicative (TermCont e) where
  pure x = TermCont $ \f -> f x
  x <*> y = do
    x <- x
    y <- y
    pure (x y)

instance Monad (TermCont e) where
  (TermCont f) >>= g = TermCont $ \h ->
    f
      ( \x ->
          runTermCont (g x) h
      )

tcont :: (IsPType e r => (a -> Term e r) -> Term e r) -> TermCont @r e a
tcont = TermCont
