{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wall -Wcompat -Wno-unticked-promoted-constructors -Wno-unused-type-patterns #-}

module Plutarch2New7 (Term(..), InterpretAllIn(..), InterpretIn(..), Permute(..), ListEqMod1(..), MaybeSwapInList2(..), Tag, Language, L, interpret) where

import Data.Kind (Type)

type Tag = Type
type Language = Type
type L :: Language -> [Language] -> Tag -> Type
data family L l ls tag

-- isomorphic to naturals
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1N :: ListEqMod1 xs (x : xs) x
  ListEqMod1S :: ListEqMod1 xs ys x -> ListEqMod1 (y ': xs) (y : ys) x

type Permute :: [a] -> [a] -> Type
data Permute xs ys where
  PermuteN :: Permute '[] '[]
  PermuteS :: ListEqMod1 ys ys' x -> Permute xs ys -> Permute (x ': xs) ys'

data MaybeSwapInList2 xs ys zs ws z w b where
  MaybeSwapInList2Base :: MaybeSwapInList2 xs xs '[] '[] z w False
  MaybeSwapInList2Swap :: MaybeSwapInList2 xs ys zs ws z w b -> MaybeSwapInList2 (x : xs) (y : ys) (x : zs) (y : ws) z w b
  MaybeSwapInList2Skip :: MaybeSwapInList2 xs ys zs ws z w b -> MaybeSwapInList2 xs ys (x : zs) (y : ws) z w b
  MaybeSwapInList2Step :: MaybeSwapInList2 xs ys zs ws z w b -> MaybeSwapInList2 (x : xs) (x : ys) zs ws z w b
  MaybeSwapInList2Except :: MaybeSwapInList2 xs ys zs ws z w False -> MaybeSwapInList2 xs ys (z : zs) (w : ws) z w True

newtype InterpretIn ls ls' l l'
  = InterpretIn
    (forall ls0 ls1 tag.
      MaybeSwapInList2 ls0 ls1 ls ls' l l' True ->
      L l ls0 tag ->
      L l' ls1 tag
    )

runInterpreter ::
  InterpretIn ls ls' l l' ->
  (forall ls0 ls1 tag.
    MaybeSwapInList2 ls0 ls1 ls ls' l l' True ->
    L l ls0 tag ->
    L l' ls1 tag
  )
runInterpreter (InterpretIn f) = f

data InterpretAllIn ls0 ls1 ls0' ls1' where
  InterpretAllInN :: InterpretAllIn ls0 ls1 '[] '[]
  InterpretAllInS :: InterpretIn ls0 ls1 l l' -> InterpretAllIn ls0 ls1 ls0' ls1' -> InterpretAllIn ls0 ls1 (l : ls0') (l' : ls1')

type Interpret ls ls' = InterpretAllIn ls ls' ls ls'

type Term :: [Language] -> Tag -> Type
data Term ls tag where
  Send :: L l ls0 tag -> Permute ls1 (l : ls0) -> Interpret ls1 ls2 -> Term ls2 tag

interpret :: Term ls tag -> Interpret ls ls' -> Term ls' tag
interpret (Send node pm InterpretAllInN) intr' = Send node pm intr'
interpret (Send node pm (InterpretAllInS intr InterpretAllInN)) (InterpretAllInS intr' InterpretAllInN) =
  Send node pm $
    InterpretAllInS
      (InterpretIn
        \(MaybeSwapInList2Except MaybeSwapInList2Base) x ->
          runInterpreter intr' (MaybeSwapInList2Except MaybeSwapInList2Base) $
            runInterpreter intr (MaybeSwapInList2Except MaybeSwapInList2Base) x)
      InterpretAllInN
interpret (Send node pm (InterpretAllInS intr0 (InterpretAllInS intr1 InterpretAllInN))) (InterpretAllInS intr0' (InterpretAllInS intr1' InterpretAllInN)) =
  Send node pm $
    InterpretAllInS
      (_ intr0 intr0') $
        InterpretAllInS
        (_ intr1 intr1')
        InterpretAllInN
