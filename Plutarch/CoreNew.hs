{-# LANGUAGE GHC2021, DataKinds, TypeFamilies #-}

module Plutarch.CoreNew where

import Data.Kind (Type)

type Language = Type
data family L (l :: Language) :: [Language] -> Type

data Nat = N | S Nat

-- Insert idx x xs ys is a proof that inserting x into xs at idx gives ys
data Insert idx x xs ys where
  IAN :: Insert N x xs (x : xs)
  IAS :: Insert idx x xs ys -> Insert (S idx) x (y : xs) (y : ys)

type Permutation :: [a] -> [a] -> Type
data Permutation xs ys where
  PermutationN :: Permutation '[] '[]
  PermutationS :: Insert idx x ys ys' -> Permutation xs ys -> Permutation (x : xs) ys'

type Term :: [Language] -> Type
data Term ls where
  Term :: L l ls -> Permutation (l : ls) ls' -> Term ls'

type PType = Type
data Expr (a :: PType)
data LC
data Var (a :: PType)
data instance L (Expr a) ls where
data instance L (Var a) ls where
  Var :: L (Var a) '[Expr a]
  VarCollapse :: Term (Var a : Var a : ls) -> L (Var a) ls
data instance L LC ls where
  Lam :: Term (Var a : ls) (Expr b : ls) -> L ls (Expr (a -> b) : ls)
  LamCollapse :: Term (LC : LC : ls) -> L LC ls
data instance L App lc where
  App :: Term (Expr (a -> b) : ls) -> Term (Expr a : ls) -> L App (Expr b : ls)
