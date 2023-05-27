module Plutarch.Core (
  Nat (..),
  Term (..),
  LengthOfTwo (..),
  runInterpreter,
  Interpret (..),
  Term' (..),
  InterpretAllIn (..),
  InterpretIn (..),
  Permutation (..),
  ListEqMod1 (..),
  ListEqMod1Idx (..),
  SubLS (..),
  Tag,
  Language,
  L,
) where

import Data.Kind (Type)

type Tag = Type
type Language = Type
type L :: Language -> [Language] -> Tag -> Type
data family L l ls tag

{- | Isomorphic to naturals.
 @ListEqMod1 xs ys x@ tells us that @xs@ is equal to @ys@, modulo @x@,
 i.e., if you remove a specific @x@ from @ys@, you get @xs@.
 You can also think of it as inserting @x@ into @xs@, resulting in @ys@.
 Representationally it is an index into a list.
-}
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1N :: ListEqMod1 xs (x : xs) x
  ListEqMod1S :: ListEqMod1 xs ys x -> ListEqMod1 (y : xs) (y : ys) x

data Nat = N | S Nat

-- FIXME: Should be a data family
data ListEqMod1Idx xs ys x idx where
  ListEqMod1IdxN :: ListEqMod1Idx xs (x : xs) x N
  ListEqMod1IdxS :: ListEqMod1Idx xs ys x idx -> ListEqMod1Idx (y : xs) (y : ys) x (S idx)

{- | @Permutation xs ys@ tells us we can permute @xs@ into @ys@.
 The proof of that is a list of indices into @ys@, each one
 being the corresponding index from the element in @xs@ into @ys@.
-}
type Permutation :: [a] -> [a] -> Type
data Permutation xs ys where
  PermutationN :: Permutation '[] '[]
  PermutationS :: ListEqMod1 ys ys' x -> Permutation xs ys -> Permutation (x : xs) ys'

-- @SubLS xs ys zs ws (Just '(x, y))@ shows that @xs@ and @ys@ share a common suffix,
-- with the prefix containing @zs@ in @xs@ and @ws@ in @ys@, except for @x@ and @y@.
data SubLS :: [Language] -> [Language] -> [Language] -> [Language] -> Type where
  SubLSBase :: SubLS xs xs '[] '[]
  SubLSSwap :: SubLS xs ys zs ws -> SubLS (x : xs) (y : ys) (x : zs) (y : ws)
  SubLSSkip :: SubLS xs ys zs ws -> SubLS xs ys (x : zs) (y : ws)

{- | Interpret a term of root language l to
 a term of root language l'. The inner languages
 are mappped from ls to ls'.
-}
type InterpretIn :: [Language] -> [Language] -> Language -> Language -> Type
newtype InterpretIn ls ls' l l'
  = InterpretIn
      ( forall ls0 ls1 tag.
        SubLS ls0 ls1 ls ls' ->
        Term' l ls0 tag ->
        Term' l' ls1 tag
      )

runInterpreter ::
  InterpretIn ls ls' l l' ->
  SubLS ls0 ls1 ls ls' ->
  Term' l ls0 tag ->
  Term' l' ls1 tag
runInterpreter (InterpretIn f) = f

data LengthOfTwo :: [a] -> [b] -> Nat -> Type where
  LengthOfTwoN :: LengthOfTwo '[] '[] N
  LengthOfTwoS :: LengthOfTwo xs ys len -> LengthOfTwo (x : xs) (y : ys) (S len)

{- | @InterpretAllIn ls0 ls1 ls2 ls3@ contains functions to
 interpret terms which root nodes are in the languages of @ls2@ into
 root nodes which languages are of @ls3@, while mapping the inner languages
 from @ls0@ to @ls1@.
-}

-- FIXME: Move the length statement to the top always by
-- refactoring into two types, one recursive and one not.
data InterpretAllIn :: [Language] -> [Language] -> Nat -> Type where
  InterpretAllInN :: LengthOfTwo ls0 ls1 idx -> InterpretAllIn ls0 ls1 idx
  InterpretAllInS ::
    ListEqMod1Idx ls0' ls0 l idx ->
    ListEqMod1Idx ls1' ls1 l' idx ->
    InterpretIn ls0' ls1' l l' ->
    InterpretAllIn ls0 ls1 (S idx) ->
    InterpretAllIn ls0 ls1 idx

-- | @Interpret ls ls'@ contains functions to interpret the languages @ls@ to @ls'@.
type Interpret :: [Language] -> [Language] -> Type
type Interpret ls ls' = InterpretAllIn ls ls' N

-- | Like @Term@, but explicitly notes the language of the root node.
type Term' :: Language -> [Language] -> Tag -> Type
data Term' l ls tag where
  Term' :: L l ls0 tag -> Interpret ls0 ls1 -> Permutation ls1 ls2 -> Term' l ls2 tag

{- | @Term ls tag@ represents a term in the languages of @ls@,
 with the tag @tag@, often representing an embedded type.
-}
type Term :: [Language] -> Tag -> Type
data Term ls tag where
  Term :: Term' l ls tag -> ListEqMod1 ls ls' l -> Term ls' tag
