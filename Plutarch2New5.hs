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

module Plutarch2New5 where

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
class CAppend xs ys r | xs ys -> r where
  append :: Append xs ys r
instance CAppend '[] ys ys where
  append = Append0
instance CAppend xs ys r => CAppend (x ': xs) ys (x ': r) where
  append = Append1 append

data Nat = N | S Nat
data SNat (n :: Nat) where
  SN :: SNat 'N
  SS :: SNat n -> SNat ('S n)

type Tag = Type
data NonEmpty a = Last a | a :| (NonEmpty a)

infixr 5 :|

data LanguageArg = LanguageArg
  { tag :: Tag
  , extra_langs :: [Language]
  }

type Language = Type
type L :: Language -> [NonEmpty LanguageArg] -> Tag -> Type
data family L l lss tag

data Expr (a :: Type)

type Only tag = Last ('LanguageArg tag '[])

data Bools
data instance L Bools ls tag where
  Xor :: L Bools '[ Only (Expr Bool), Only (Expr Bool) ] (Expr Bool)
  BoolLit :: Bool -> L Bools '[] (Expr Bool)
  --ExpandBools :: L Bools '[ 'Last ('LanguageArg tag '[]) ] tag
  --ContractBools :: L Bools '[ 'Last ('LanguageArg tag '[Bools, Bools]) ] tag

data Ints
data instance L Ints ls tag where
  Mult :: L Ints '[ Only (Expr Int), Only (Expr Int) ] (Expr Int)
  IntLit :: Int -> L Ints '[] (Expr Int)

data IntBoolConversions
data instance L IntBoolConversions ls tag where
  IntAsBool :: L IntBoolConversions '[ Only (Expr Int) ] (Expr Bool)
  BoolAsInt :: L IntBoolConversions '[ Only (Expr Bool) ] (Expr Int)

-- isomorphic to naturals
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1N :: ListEqMod1 xs (x ': xs) x
  ListEqMod1S :: ListEqMod1 xs ys x -> ListEqMod1 (y ': xs) (y ': ys) x

type InsertAll :: [a] -> [a] -> [a] -> Type
data InsertAll xs ys zs where
  InsertAll0 :: InsertAll '[] ys ys
  InsertAll1 :: ListEqMod1 zs zs' x -> InsertAll xs ys zs -> InsertAll (x ': xs) ys zs'

insertAllDirect :: CAppend xs ys zs => InsertAll xs ys zs
insertAllDirect = f append where
  f :: Append xs ys zs -> InsertAll xs ys zs
  f Append0 = InsertAll0
  f (Append1 x) = InsertAll1 ListEqMod1N (f x)

data ExArgs args ls where
  ExArgsN ::
    Append extra_langs ls ls' ->
    Term ls' tag ->
    ExArgs ('Last ('LanguageArg tag extra_langs)) ls
  ExArgsS ::
    Append extra_langs ls ls' ->
    Term ls' tag ->
    ExArgs args ls ->
    ExArgs ('LanguageArg tag extra_langs ':| args) ls

data ExArgss argss ls where
  ExArgssN :: ExArgss '[] '[]
  ExArgssS :: ExArgs args ls' -> InsertAll ls' ls_old ls_new -> ExArgss argss ls_old -> ExArgss (args ': argss) ls_new

type TermTy = [Language] -> Tag -> Type
type Term :: TermTy
data Term ls tag where
  Send :: ExArgss argss ls' -> ListEqMod1 ls' ls l -> L l argss tag -> Term ls tag

xorOfTrueAndFalse :: Term '[Bools, Bools, Bools] (Expr Bool)
xorOfTrueAndFalse = Send (ExArgssS (ExArgsN Append0 l) insertAllDirect (ExArgssS (ExArgsN Append0 r) insertAllDirect ExArgssN)) ListEqMod1N Xor
    where
      l :: Term '[Bools] (Expr Bool)
      l = Send ExArgssN ListEqMod1N (BoolLit True)
      r :: Term '[Bools] (Expr Bool)
      r = Send ExArgssN ListEqMod1N (BoolLit False)

absurdTerm :: Term '[] tag -> a
absurdTerm (Send _ idx _) = case idx of

modIdcs ::
  ListEqMod1 new' new x ->
  ListEqMod1 tail new y ->
  (forall tail'.
    Either
      (x :~: y, new' :~: tail)
      (ListEqMod1 tail' tail x, ListEqMod1 (x ': tail') (x ': new') y)
    -> b
  ) ->
  b
modIdcs ListEqMod1N ListEqMod1N f = f (Left (Refl, Refl))
modIdcs ListEqMod1N (ListEqMod1S idx) f = f (Right (ListEqMod1N, ListEqMod1S idx))
modIdcs (ListEqMod1S idx) ListEqMod1N f = f (Right (idx, ListEqMod1S ListEqMod1N))
modIdcs (ListEqMod1S idx) (ListEqMod1S idx') f = modIdcs idx idx' \case
  Left (x, Refl) -> f (Left (x, Refl))
  Right (idx2, ListEqMod1S idx'2) -> f (Right (ListEqMod1S idx2, ListEqMod1S $ ListEqMod1S idx'2))
  Right (idx2, ListEqMod1N) -> f (Right (ListEqMod1S idx2, ListEqMod1S $ ListEqMod1S ListEqMod1N))

bring :: ListEqMod1 new' new x -> InsertAll old '[] new -> InsertAll old '[] (x ': new')
bring ListEqMod1N x = x
bring idx (InsertAll1 idx' tail) =
  modIdcs idx idx' \case
    Left (Refl, Refl) -> InsertAll1 ListEqMod1N tail
    Right (idx2, idx'2) -> InsertAll1 idx'2 $
       bring idx2 $ tail

bring' :: Int -> [Int] -> [Int]
bring' idx (idx' : idxs) =
  case compare idx idx' of
    EQ -> 0 : idxs
    LT -> idx' : bring' idx idxs
    GT -> idx' : bring' (idx - 1) idxs
bring' _ _ = error "impossible"
{-
-- case GT
bring (ListEqMod1S (ListEqMod1S idx)) (InsertAll1 (ListEqMod1S ListEqMod1N) tail) =
  InsertAll1 (ListEqMod1S $ ListEqMod1S ListEqMod1N) $
      bring (ListEqMod1S idx) tail
bring (ListEqMod1S idx) (InsertAll1 idx' tail) =
  case eqListEqMod1 (ListEqMod1S idx) idx' of
    Just (Refl, Refl) -> InsertAll1 ListEqMod1N tail
    Nothing -> undefined -- InsertAll1 idx' $ bring idx tail
    -}

{-
pull :: ListEqMod1 ls ls' l -> Term ls' tag -> Term (l ': ls) tag
pull ListEqMod1N x = x
pull idx (Send (ExArgssS args idxs ExArgssN) top_idx t) = Send argss (ListEqMod1S ListEqMod1N) t
pull (ListEqMod1S idx) x = undefined

oneBoolsToOneInts :: Term '[Bools] (Expr Bool) -> Term '[Ints] (Expr Int)
oneBoolsToOneInts (Send _ _ ListEqMod1N (BoolLit b)) =
  Send ExArgssN FlattenN ListEqMod1N (IntLit $ if b then -1 else 1)
oneBoolsToOneInts (Send args _ ListEqMod1N Xor) = case args of
  ExArgssS (ExArgsN _ arg) _ -> error "FIXME: prove unreachable" arg
oneBoolsToOneInts (Send _ _ (ListEqMod1S idx) _) = case idx of
-}

{-
oneBoolsToOneInts' :: Term (Bools ': ls) tag -> Term (IntBoolConversions ': Ints ': ls) tag
oneBoolsToOneInts' (Send ExArgssN ListEqMod1N (BoolLit b)) =
  Send (ExArgssS (ExArgsN Append0 $ Send ExArgssN ListEqMod1N (IntLit $ if b then -1 else 1)) insertAllDirect ExArgssN) ListEqMod1N IntAsBool
oneBoolsToOneInts' (Send _ ListEqMod1N Xor) = undefined
oneBoolsToOneInts' (Send (ExArgssS (ExArgsN Append0 y) (InsertAll1 ListEqMod1N InsertAll0) ExArgssN) (ListEqMod1S idx) x) =
  let y' = oneBoolsToOneInts' y
  in
    Send (ExArgssS (ExArgsN Append0 y') insertAllDirect ExArgssN) (ListEqMod1S (ListEqMod1S idx)) x
oneBoolsToOneInts' (Send (ExArgssS (ExArgsN (Append1 Append0) y) (InsertAll1 ListEqMod1N InsertAll0) ExArgssN) (ListEqMod1S idx) x) =
  let y' = oneBoolsToOneInts' $ _ y
  in
    Send (ExArgssS (ExArgsN _ y') insertAllDirect ExArgssN) (ListEqMod1S (ListEqMod1S idx)) x
oneBoolsToOneInts' (Send (ExArgssS args idxs _) (ListEqMod1S idx) x) = undefined
-}
