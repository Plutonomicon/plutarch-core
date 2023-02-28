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

module Plutarch2New4 where

import Data.Kind (Type)
import Type.Reflection (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy (Proxy))
import Numeric.Natural (Natural)
import Data.Functor.Const (Const (Const), getConst)
import GHC.Exts
import Unsafe.Coerce
import Data.Type.Equality

data Nat = N | S Nat
data SNat (n :: Nat) where
  SN :: SNat 'N
  SS :: SNat n -> SNat ('S n)

type Tag = Type
data LanguageBuiltinArg paramt = LanguageBuiltinArg { check_tag :: paramt -> Tag -> Type, extra_langs :: [Language] }
data LanguageBuiltin = forall (paramt :: Type). LanguageBuiltin
    { dat :: paramt -> Type
    , check_tag :: paramt -> Tag -> Type
    , argss :: [(LanguageBuiltinArg paramt, [LanguageBuiltinArg paramt])]
    }
type Language = Type
type family LanguageBuiltins (l :: Language) :: [LanguageBuiltin]

data Append xs ys r where
  Append0 :: Append '[] ys ys
  Append1 :: Append xs ys r -> Append (x ': xs) ys (x ': r)

type TermTy = [Language] -> Tag -> Type
data ExtractArgs args param term ls where
  ExtractArgsN ::
    check_tag param tag ->
    Append extra_langs ls ls' ->
    term ls' tag ->
    ExtractArgs '( 'LanguageBuiltinArg check_tag extra_langs, '[]) param term ls
  ExtractArgsS ::
    check_tag param tag ->
    Append extra_langs ls ls' ->
    term ls' tag ->
    ExtractArgs '(last_arg, args) param term ls ->
    ExtractArgs '(last_arg, ('LanguageBuiltinArg check_tag extra_langs ': args)) param term ls

data ExtractArgss argss param term lss where
  ExtractArgssN :: ExtractArgss '[] param term '[]
  ExtractArgssS :: ExtractArgs args param term ls -> ExtractArgss argss param term lss -> ExtractArgss (args ': argss) param term (ls ': lss)

data ElemOf x xs where
  Here :: ElemOf x (x ': xs)
  There :: ElemOf x xs -> ElemOf x (x' ': xs)

type L :: Language -> TermTy -> [[Language]] -> Tag -> Type
data L l term lss tag where
  L ::
    ElemOf ('LanguageBuiltin dat check_tag argss) (LanguageBuiltins l) ->
    dat param ->
    check_tag param tag ->
    ExtractArgss argss param term lss ->
    L l term lss tag

data Expr (a :: Type)

data Bools
data IsBool (u :: ()) tag where
  IsBool :: IsBool u (Expr Bool)
type instance LanguageBuiltins Bools =
  '[ 'LanguageBuiltin Proxy IsBool '[ '( 'LanguageBuiltinArg IsBool '[], '[]), '( 'LanguageBuiltinArg IsBool '[], '[])]
   , 'LanguageBuiltin (Const Bool) IsBool '[]
   ]

data Ints
data IsInt (u :: ()) tag where
  IsInt :: IsInt u (Expr Int)
type instance LanguageBuiltins Ints =
  '[ 'LanguageBuiltin Proxy IsInt '[ '( 'LanguageBuiltinArg IsInt '[], '[]), '( 'LanguageBuiltinArg IsInt '[], '[])]
   , 'LanguageBuiltin (Const Int) IsInt '[]
   ]

data IntBoolConversions
type instance LanguageBuiltins IntBoolConversions =
  '[ 'LanguageBuiltin Proxy IsBool '[ '( 'LanguageBuiltinArg IsInt '[], '[])]
   , 'LanguageBuiltin Proxy IsInt '[ '( 'LanguageBuiltinArg IsBool '[], '[])]
   ]

{-
type LengthOf :: [a] -> Type
data LengthOf xs where
  LengthZero :: LengthOf '[]
  LengthSucc :: LengthOf xs -> LengthOf (x ': xs)

class CLengthOf (xs :: [a]) where
  lengthOf :: LengthOf xs
instance CLengthOf '[] where
  lengthOf = LengthZero
instance CLengthOf xs => CLengthOf (x ': xs) where
  lengthOf = LengthSucc lengthOf

type LengthsOf :: [[a]] -> Type
data LengthsOf xss where
  LNil :: LengthsOf '[]
  LCons :: LengthOf xs -> LengthsOf xss -> LengthsOf (xs ': xss)

class CLengthsOf xss where
  lengthsOf :: LengthsOf xss
instance CLengthsOf '[] where
  lengthsOf = LNil
instance (CLengthOf xs, CLengthsOf xss) => CLengthsOf (xs ': xss) where
  lengthsOf = LCons lengthOf lengthsOf

-- ListEqMod1 xs ys x tells us that ys is equal to xs but has an extra x somewhere
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1Base :: ListEqMod1 xs (x ': xs) x
  ListEqMod1Step :: ListEqMod1 xs ys x -> ListEqMod1 (y ': xs) (y ': ys) x

class CListEqMod1 xs ys x where
  listEqMod1 :: ListEqMod1 xs ys x
instance CListEqMod1 xs (x ': xs) x where listEqMod1 = ListEqMod1Base
instance CListEqMod1 xs ys x => CListEqMod1 (y ': xs) (y ': ys) x where listEqMod1 = ListEqMod1Step listEqMod1

-- `Flattened xss xs` proves that `xs ~ ListAppendAll xss`
type Flattened :: [[a]] -> [a] -> Type
data Flattened xss xs where
  FlattenedBase :: Flattened '[] '[]
  FlattenedBase' :: Flattened '[xs] xs
  FlattenedSeg :: Flattened xss xs -> Flattened ('[x] ': xss) (x ': xs)
  FlattenedStep :: Flattened (xs' ': xss) xs -> Flattened ((x ': xs') ': xss) (x ': xs)

class CFlattened xss xs | xss -> xs where
  flattened :: Flattened xss xs
instance CFlattened '[] '[] where flattened = FlattenedBase
instance CFlattened xss xs => CFlattened ('[x] ': xss) (x ': xs) where flattened = FlattenedSeg flattened
instance CFlattened ((x' ': xs') ': xss) xs => CFlattened ((x ': x' ': xs') ': xss) (x ': xs) where flattened = FlattenedStep flattened

type SwapInList :: [a] -> [a] -> a -> a -> Type
data SwapInList xs ys x y where
  SWBase :: SwapInList (x ': xs) (y ': xs) x y
  SWInc :: SwapInList xs ys x y -> SwapInList (z ': xs) (z ': ys) x y

class CSwapInList xs ys x y where
  swapInList :: SwapInList xs ys x y
instance CSwapInList (x ': xs) (y ': xs) x y where swapInList = SWBase
instance CSwapInList xs ys x y => CSwapInList (z ': xs) (z ': ys) x y where swapInList = SWInc swapInList

-- RB xss xs tells us where each element in xs comes from in xss
-- TODO: Establish a canonical representation that either puts
-- all RB1s first, or prevent using RB2 when RB1 could be used.
type RB :: [[a]] -> [a] -> Type
data RB xss xs where
  RB0 :: RB '[] '[]
  RB1 :: RB xss xs -> RB ('[] ': xss) xs
  RB2 :: ListEqMod1 ys ys' x -> SwapInList xss xss' ys ys' -> RB xss xs -> RB xss' (x ': xs)

type RemoveFrom :: [a] -> a -> [a]
type family RemoveFrom xs x where
  RemoveFrom (x ': xs) x = xs
  RemoveFrom (y ': xs) x = y ': RemoveFrom xs x

type family ListAppendReverse xs ys where
  ListAppendReverse '[] ys = ys
  ListAppendReverse (x ': xs) ys = ListAppendReverse xs (x ': ys)

type family RemoveFrom2Helper rest xs xss x where
  RemoveFrom2Helper rest '[] xss x = ListAppendReverse rest '[] ': RemoveFrom2 xss x
  RemoveFrom2Helper rest (x ': xs) xss x = ListAppendReverse rest xs ': xss
  RemoveFrom2Helper rest (y ': xs) xss x = RemoveFrom2Helper (y ': rest) xs xss x

type family RemoveFrom2 xss x where
  RemoveFrom2 ('[] ': xss) x = RemoveFrom2 xss x
  RemoveFrom2 ((x ': xs) ': xss) x = xs ': xss
  RemoveFrom2 (xs ': xss) x = RemoveFrom2Helper '[] xs xss x

type FindWithHelper :: [a] -> [[a]] -> a -> [a]
type family FindWithHelper xs xss x where
  FindWithHelper '[] xss x = FindWith xss x
  FindWithHelper (x ': xs) xss x = x ': xs
  FindWithHelper (y ': xs) xss x = y ': FindWithHelper xs xss x

type FindWith :: [[a]] -> a -> [a]
type family FindWith xss x where
  FindWith (xs ': xss) x = FindWithHelper xs xss x

data ListOf xs x where
  ListOfNil :: ListOf '[] x
  ListOfCons :: ListOf xs x -> ListOf (x ': xs) x

class CListOf xs x where
  listOf :: ListOf xs x
instance CListOf '[] x where listOf = ListOfNil
instance CListOf xs x => CListOf (x ': xs) x where listOf = ListOfCons listOf

class CRBInto xss xs where
  rbinto :: RB xss xs
instance CListOf xss '[] => CRBInto xss '[] where
  rbinto = f listOf where
    f :: forall xss. ListOf xss '[] -> RB xss '[]
    f ListOfNil = RB0
    f (ListOfCons x) = RB1 (f x)
instance
  ( ys ~ RemoveFrom ys' x
  , ys' ~ FindWith xss' x
  , xss ~ RemoveFrom2 xss' x
  , CListEqMod1 ys ys' x
  , CSwapInList xss xss' ys ys'
  , CRBInto xss xs
  ) => CRBInto xss' (x ': xs) where
  rbinto = RB2 (listEqMod1 :: ListEqMod1 ys ys' x) (swapInList :: SwapInList xss xss' ys ys') rbinto

class CRBFlat xss xs | xss -> xs where
  rbflat :: RB xss xs
instance CRBFlat ('[] :: [[a]]) ('[] :: [a]) where rbflat = RB0
instance CRBFlat xss xs => CRBFlat ('[x] ': xss) (x ': xs) where
  rbflat = RB2 ListEqMod1Base SWBase (RB1 (rbflat :: RB xss xs))
instance CRBFlat ((x' ': xs') ': xss) xs => CRBFlat ((x ': x' ': xs') ': xss) (x ': xs) where
  rbflat = RB2 ListEqMod1Base SWBase (rbflat :: RB ((x' ': xs') ': xss) xs)

type Term :: TermTy
data Term ls tag where
  Send :: RB lss ls' -> ListEqMod1 ls' ls l -> L l Term lss tag -> Term ls tag
  --Bring :: ListEqMod1 ls' ls l -> Term ls tag -> Term (l ': ls') tag

data SList (xs :: [a]) where
  SConsNil :: SList '[x]
  SCons :: SList xs -> SList (x ': xs)
 
data BoolAST = BAXor BoolAST BoolAST | BAT | BAF

{-
send :: CRBFlat ('[l] ': lss) ls => L l Term lss tag -> Term ls tag
send = Send rbflat
sendInto :: CRBInto ('[l] ': lss) ls => L l Term lss tag -> Term ls tag
sendInto = Send rbinto
 
example_1 :: Term '[Bools, Bools, Bools] (Expr Bool)
example_1 = send $ Xor (send $ BoolLit True) (send $ BoolLit False)
-}

--example_2 :: Term '[Bools, Bools, Bools] (Expr Bool)
--example_2 = send $ Xor (send $ BoolLit True) (send $ BoolLit False)

{-
conv_1 :: Term '[Bools] (Expr Bool) -> Term '[Ints] (Expr Int)
conv_1 (Send (RB2 ListEqMod1Base SWBase next) (BoolLit b)) = send $ IntLit $ if b then -1 else 1
conv_1 (Send (RB2 (ListEqMod1Step idx) SWBase _) _) = case idx of
conv_1 (Send (RB2 _ (SWInc (SWInc _)) next) _) = case next of
conv_1 (Send (RB2 _ (SWInc SWBase) next) _) = case next of
conv_1 (Send (RB2 ListEqMod1Base SWBase (RB1 (RB1 (RB1 next)))) x) = case next of

conv_2 :: Term (Bools ': ls) (Expr Bool) -> Term (IntBoolConversions ': Ints ': ls) (Expr Bool)
conv_2 (Send FlattenedBase (BoolLit b)) = send $ IntAsBool $ send $ IntLit $ if b then -1 else 1

conv_3 :: Term (Bools ': ls) (Expr Bool) -> Term (IntBoolConversions ': Ints ': IntBoolConversions ': ls) (Expr Int)
conv_3 (Send lengths (Xor (x :: Term ls0 (Expr Bool)) y)) = Bring (ListEqMod1Step $ ListEqMod1Step $ h lengths) $ Send (FlattenedStep $ f $ FlattenedStep $ FlattenedBase') $ Mult (Send FlattenedBase' $ BoolAsInt x) (Send FlattenedBase' $ BoolAsInt y) where
  f :: Flattened xss xs -> Flattened (ls0 ': xss) (ListAppend ls0 xs)
  f = g (j lengths)
  g :: SList ys -> Flattened xss xs -> Flattened (ys ': xss) (ListAppend ys xs)
  g SConsNil x = FlattenedSeg x
  g (SCons s) x = FlattenedStep $ g s x
  h :: Flattened '[xs, ys] zs -> ListEqMod1 zs (ListAppend xs (x ': ys)) x
  h (FlattenedStep x) = ListEqMod1Step $ h x
  h (FlattenedSeg x) = case i x of Refl -> ListEqMod1Step ListEqMod1Base
  i :: Flattened '[xs] ys -> xs :~: ys
  i FlattenedBase' = Refl
  i (FlattenedSeg FlattenedBase) = Refl
  i (FlattenedStep x) = case i x of Refl -> Refl
  j :: Flattened '[xs, ys] zs -> SList xs
  j (FlattenedSeg _) = SConsNil
  j (FlattenedStep x) = SCons $ j x
conv_3 (Bring idx x) = conv_4 idx x

--conv_4 :: ListEqMod1 ls' ls Bools -> Term ls (Expr Bool) -> Term (IntBoolConversions ':) (Expr Int)
--conv_4 (Bring idx (x :: Term _ (Expr Bool))) = _ $ conv_4 _ x
---}
---}
