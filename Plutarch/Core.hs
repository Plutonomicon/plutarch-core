module Plutarch.Core (
  Nat (..),
  Term (..),
  LenTwo (..),
  runInterpreter,
  Interpret,
  Term' (..),
  InterpretAsc (..),
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

{- | @SubLS xs ys zs ws@ shows that @xs@ and @ys@ share a common suffix,
 with the prefix containing @zs@ in @xs@ and @ws@ in @ys@.
 It can be thought of as extending zs and ws to xs and ys by appending a suffix
 to a filtered version of both.
-}
data SubLS :: [Language] -> [Language] -> [Language] -> [Language] -> Type where
  SubLSBase :: SubLS xs xs '[] '[]
  SubLSSwap :: SubLS xs ys zs ws -> SubLS (x : xs) (y : ys) (x : zs) (y : ws)
  SubLSSkip :: SubLS xs ys zs ws -> SubLS xs ys (x : zs) (y : ws)

{- | Interpret a term of root language l to
 a term of root language l'. The inner languages
 are mapped from ls to ls'.
-}
type InterpretIn :: [Language] -> [Language] -> Language -> Language -> Type
newtype InterpretIn ls ls' l l'
  = InterpretIn
      ( forall ls0 ls1 tag.
        SubLS ls0 ls1 ls ls' ->
        Term' l ls0 tag ->
        -- TODO: Possibly change this to `Term (l' : ls1) tag`.
        -- This _shouldn't_ restrict the consumer in practice,
        -- but it's not clear if it _benefits_ the producer in
        -- practice either, after all,
        -- you could only change the root node to only of those you
        -- know, i.e. those in ls', but you can only choose them if
        -- they are present in ls1, which isn't a given.
        -- When would it be useful to _some times_ be able to choose
        -- another root node language?
        Term' l' ls1 tag
      )

runInterpreter ::
  InterpretIn ls ls' l l' ->
  SubLS ls0 ls1 ls ls' ->
  Term' l ls0 tag ->
  Term' l' ls1 tag
runInterpreter (InterpretIn f) = f

-- FIXME: Should be just LengthOf and should be erased
data LenTwo :: [a] -> [b] -> Nat -> Type where
  LenN :: LenTwo '[] '[] N
  LenS :: LenTwo xs ys len -> LenTwo (x : xs) (y : ys) (S len)

{- | @InterpretAsc ls0 ls1 ls2 ls3@ contains functions to
 interpret terms which root nodes are in the languages of @ls2@ into
 root nodes which languages are of @ls3@, while mapping the inner languages
 from @ls0@ to @ls1@.
-}

data InterpretAsc :: [Language] -> [Language] -> Nat -> Type where
  InterpretAscN :: LenTwo ls0 ls1 idx -> InterpretAsc ls0 ls1 idx
  InterpretAscS ::
    ListEqMod1Idx ls0' ls0 l idx ->
    ListEqMod1Idx ls1' ls1 l' idx ->
    InterpretIn ls0' ls1' l l' ->
    InterpretAsc ls0 ls1 (S idx) ->
    InterpretAsc ls0 ls1 idx

-- | @Interpret ls ls'@ contains functions to interpret the languages @ls@ to @ls'@.
type Interpret :: [Language] -> [Language] -> Type
type Interpret ls ls' = InterpretAsc ls ls' N

-- | Like @Term@, but explicitly notes the language of the root node.
type Term' :: Language -> [Language] -> Tag -> Type
data Term' l ls tag where
  -- TODO: Add {union/intersection}/{sum/product} languages?
  Term' :: L l ls0 tag -> Interpret ls0 ls1 -> Permutation ls1 ls2 -> Term' l ls2 tag

{- | @Term ls tag@ represents a term in the languages of @ls@,
 with the tag @tag@, often representing an embedded type.
-}
type Term :: [Language] -> Tag -> Type
data Term ls tag where
  Term :: Term' l ls tag -> ListEqMod1 ls ls' l -> Term ls' tag
