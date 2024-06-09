module Plutarch.Core (
  Term (..),
  Permutation (..),
  Insert (..),
  Language,
  L,
) where

import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)

type Language = Type
data family L (l :: Language) :: [Language] -> Type

-- Insert x xs ys is a witness for that inserting x into xs at some index gives ys
data Insert x xs ys where
  IN :: Insert x xs (x : xs)
  IS :: Insert x xs ys -> Insert x (y : xs) (y : ys)

type Permutation :: [a] -> [a] -> Type
data Permutation xs ys where
  PN :: Permutation '[] '[]
  PS :: Insert x ys ys' -> Permutation xs ys -> Permutation (x : xs) ys'

type Term :: [Language] -> Type
data Term ls where
  Term :: L l ls -> Permutation (l : ls) ls' -> Term ls'

--- Show instances

instance Show (Insert x xs ys) where
  showsPrec prec x = showsPrec prec (f x) where
    f :: forall x xs ys. Insert x xs ys -> Int
    f IN = 0
    f (IS x) = f x + 1

data SomeInsert = forall x xs ys. SomeInsert (Insert x xs ys)
instance Show SomeInsert where
  showsPrec prec x = showsPrec prec (unsafeCoerce x :: Insert x xs ys)

instance Show (Permutation xs ys) where
  showsPrec prec x = let _ = SomeInsert in showsPrec prec (unsafeCoerce x :: [SomeInsert])
