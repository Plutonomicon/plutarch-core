{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Plutarch.Optics.Fix(fixt) where

import Data.Fix
import Control.Lens

import Data.Functor.Base
import Data.Function

fixt ::
  (Applicative f) =>
  (forall ra rb. (ra -> f rb) -> a ra -> f (b rb)) ->
  Fix a ->
  f (Fix b)
fixt f = fmap Fix . (fix (f . dimap unFix (fmap Fix))) . unFix

list' :: Traversal (Fix (ListF a)) (Fix (ListF b)) a b
list' f = fixt (listf f)

listf ::
  (Applicative f) =>
  (a -> f b) ->
  (ra -> f rb) ->
  ListF a ra ->
  f (ListF b rb)
listf _ _ Nil = pure Nil
listf f r (Cons a b) = Cons <$> f a <*> r b
