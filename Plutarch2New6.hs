{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-unused-type-patterns #-}
{-# OPTIONS_GHC -Wno-unused-packages -Wno-unused-imports -Wno-missing-export-lists #-}

-- TODO:
-- - Use stable names to reduce work
-- - Hashing partial interpreter for hoisting
-- - Example ULC interpreter
-- - Ergonomic op-level definitions
-- - Optimisations
-- - Data types
-- - PAsData
-- - Optics
-- - Plugins for syntax

module Plutarch2New6 where

import Data.Kind (Type)
import Type.Reflection (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy (Proxy))
import Numeric.Natural (Natural)
import Data.Functor.Const (Const (Const), getConst)
import GHC.Exts
import Unsafe.Coerce
import Data.Type.Equality

data Append xs ys r where
  Append0 :: Append '[] ys ys
  Append1 :: Append xs ys r -> Append (x ': xs) ys (x ': r)

type Tag = Type
type Language = Type
type L :: Language -> [Language] -> Tag -> Type
data family L l ls tag

data Expr (a :: Type)

data Bools
data instance L Bools ls tag where
  Xor :: Term ls0 (Expr Bool) -> Term ls1 (Expr Bool) -> Append ls0 ls1 ls -> L Bools ls (Expr Bool)
  BoolLit :: Bool -> L Bools '[] (Expr Bool)
  ExpandBools :: Term ls tag -> L Bools ls tag
  ContractBools :: Term (Bools : Bools : ls) tag -> L Bools ls tag

-- isomorphic to naturals
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1N :: ListEqMod1 xs (x ': xs) x
  ListEqMod1S :: ListEqMod1 xs ys x -> ListEqMod1 (y ': xs) (y ': ys) x

type Permute :: [a] -> [a] -> Type
data Permute xs ys where
  Permute0 :: Permute '[] '[]
  Permute1 :: ListEqMod1 ys ys' x -> Permute xs ys -> Permute (x ': xs) ys'

permutePermute :: Permute xs ys -> Permute ys zs -> Permute xs zs
permutePermute = undefined

flipPermute :: Permute xs ys -> Permute ys xs
flipPermute = undefined

newtype Interpreter l l'  = Interpreter (forall ls tag. L l ls tag -> L l' ls tag)
runInterpreter :: Interpreter l l' -> L l ls tag -> L l' ls tag
runInterpreter (Interpreter f) = f
composeInterpreters :: Interpreter l1 l2 -> Interpreter l0 l1 -> Interpreter l0 l2
composeInterpreters (Interpreter f) (Interpreter g) = Interpreter (f . g)

data InterpretAll ls ls' where
  InterpretAll0 :: InterpretAll '[] '[]
  InterpretAll1 :: Interpreter l l' -> InterpretAll ls ls' -> InterpretAll (l : ls) (l' : ls')

type TermTy = [Language] -> Tag -> Type
type Term :: TermTy
data Term ls tag where
  Send :: L l ls0 tag -> Permute ls1 (l : ls0) -> InterpretAll ls1 ls -> Term ls tag

interpret :: (forall ls tag. L l ls tag -> L l' ls tag) -> Term (l : ls) tag -> Term (l' : ls) tag
interpret = undefined -- Interpret . Interpreter

absurdTerm :: Term '[] tag -> a
absurdTerm (Send _ _ _) = undefined -- case idx of

data BooleanArithmetic = BL Bool | BXor BooleanArithmetic BooleanArithmetic

interpretBools :: Term '[Bools] (Expr Bool) -> BooleanArithmetic
interpretBools (Send b (Permute1 ListEqMod1N Permute0) (InterpretAll1 int InterpretAll0)) = case runInterpreter int b of
  BoolLit b -> BL b
  Xor x _ Append0 -> absurdTerm x
  ExpandBools x -> absurdTerm x
  ContractBools x -> _
--interpretBools (Send _ (Permute1 (ListEqMod1S _) idxs) ints) = case idxs of
interpretBools _ = undefined
  {-
interpretBools (Interpret int (Send x (Permute1 ListEqMod1N Permute0))) = case runInterpreter int x of
  BoolLit b -> BL b
  Xor x _ Append0 -> absurdTerm x
interpretBools (Interpret _ (Send _ (Permute1 (ListEqMod1S _) idxs))) = case idxs of
interpretBools (Interpret int (Interpret int' term)) = interpretBools (Interpret (int `composeInterpreters` int') term)
-}
