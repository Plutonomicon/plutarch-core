{-# LANGUAGE TypeFamilyDependencies, UndecidableInstances #-}

module Plutarch.Example where

import Unsafe.Coerce (unsafeCoerce, unsafeCoerce#)
import Plutarch.Core
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type, Constraint)
import GHC.Exts (ZeroBitType, TYPE)
import Data.Type.Equality ((:~:)(Refl))
import GHC.TypeLits (Nat, type (-))


type NodeKind = Type

type MergeCategory = Type

data family MergeCategoryFor :: Language -> MergeCategory -> a -> Type
type CMergeCategoryFor :: Language -> MergeCategory -> a -> Constraint
class CMergeCategoryFor l c i | l -> c i , i c -> l where
  cmergeCategoryFor :: MergeCategoryFor l c i

data family Merge (kind :: NodeKind) (category :: MergeCategory) (x :: a) (y :: a) :: a -> Type
type CMerge :: NodeKind -> MergeCategory -> a -> a -> a -> Constraint
class CMerge kind cat x y r | kind cat x y -> r where
  cmerge :: Merge kind cat x y r

-- This type _should_ have been isomorphic to unit,
-- but this isn't possible to do in Haskell.
-- You can't do a practical emulation "zero bit types" properly in Haskell,
-- due to a lack of totality combined with equality proofs
-- being possible.
-- The core challenge is that you must somehow define a `type ZEither :: ZeroBitType`,
-- which supports pattern matching on it such that either:
-- - the result also has kind `ZeroBitType` (thus it needn't be run, but totality!)
-- - both branches are _erased to the same code_ (how could we possibly emulate this?)
--
-- You _could_ still do it if you don't allow pattern matching on it with functions,
-- but instead some calculus which you have full control over.
-- This would be very painful however.
--
-- We choose the less painful but indeed much more dissatisfactory approach of
-- making `Merges` not erased, such that it has actual meaning.
--
-- Anything which you do in `Merges`, should instead be done in your language definition.
-- You should not have any `Merge k c x y` that has more than one possible value,
-- likewise for `MergeCategoryFor` and `MergeIndexFor`.
--
-- We can't enforce this, however, and it won't break anything either,
-- it's just bad style.
type Merges :: NodeKind -> [Language] -> [Language] -> [Language] -> Type
data Merges kind xs ys rs where
  MergesBase :: Merges kind '[] '[] '[]
  MergesStep ::
    MergeCategoryFor x cat x' ->
    MergeCategoryFor y cat y' ->
    Merge kind cat x' y' r' ->
    MergeCategoryFor r cat r' ->
    Merges kind xs ys rs ->
    Merges kind (x : xs) (y : ys) (r : rs)

class CMerges kind xs ys rs | kind xs ys -> rs where
  cmerges :: Merges kind xs ys rs
instance CMerges kind '[] '[] '[] where
  cmerges = MergesBase
instance (
  CMergeCategoryFor x cat x',
  CMergeCategoryFor y cat y',
  CMerge kind cat x' y' r',
  CMergeCategoryFor r cat r',
  CMerges kind xs ys rs
  ) => CMerges kind (x : xs) (y : ys) (r : rs) where
  cmerges = MergesStep cmergeCategoryFor cmergeCategoryFor cmerge cmergeCategoryFor cmerges

type PType = [Language] -> Type

data Expr (a :: PType) :: Language
data instance L (Expr a) ls where

data ProductNode :: NodeKind
data SumNode :: NodeKind

infixr 0 #->
data (#->) :: PType -> PType -> PType

data App :: Language
data instance L App lc where
  App :: Merges ProductNode xs ys rs -> Term (Expr (a #-> b) : xs) -> Term (Expr a : ys) -> L App (Expr b : rs)

data AppC :: MergeCategory
data instance MergeCategoryFor App cat idx where
  MergeCategoryFor_App :: MergeCategoryFor App AppC idx
data instance Merge _ AppC x y z = Merge_App

instance CMergeCategoryFor App AppC '() where
  cmergeCategoryFor = MergeCategoryFor_App
instance CMerge ProductNode AppC x y '() where
  cmerge = Merge_App

data ElemOf a as where
  ElemOfN :: ElemOf x (x : xs)
  ElemOfS :: ElemOf x xs -> ElemOf x (y : xs)

--plam :: (Term '[Vars, Expr a] -> Term (Expr b : ls)) -> Term (Expr (a #-> b) : ls)
--plam = undefined

{-
data TypedVar (as :: [PType]) :: Language
data instance L (TypedVar as) ls where
  TypedVar :: ElemOf a as -> L (TypedVar as) '[Expr a]
  TypedVarCollapse :: Term (TypedVar a : TypedVar a : ls) -> L (TypedVar a) ls

instance CMergeCategoryFor

data LC :: Language
data instance L LC ls where
  Lam :: Term (TypedVar a : Expr b : ls) -> L LC (Expr (a #-> b) : ls)
  LamConst :: Term (Expr b : ls) -> L LC (Expr (a #-> b) : ls)
  LamCollapse :: Term (LC : LC : ls) -> L LC ls

flipTerm :: Term (x : y : ls) -> Term (y : x : ls)
flipTerm = undefined

flip3Term :: Term (x : y : z : ls) -> Term (z : x : y : ls)
flip3Term = undefined

stripPermutation :: Permutation xs ys -> Permutation xs xs
stripPermutation = undefined

flipPermutation :: Permutation xs ys -> Permutation ys xs
flipPermutation = undefined

-- Given some languages ys, we figure out how to extract it from xs,
-- collapsing as much as we can at the same time.
-- For each element in `ys`, we check if it exists in `xs`,
-- and if so, "remove" it from `xs`.
-- At the end, we are left with an unused portion of `xs`, which
-- we must merge into what we have.
-- This isn't possible for all languages.
-- If there is a language for which it isn't possible,
-- an error is generated.
-- This might e.g. be the case for unconsumed linear variables.
class Collapse (xs :: [Language]) (ys :: [Language]) where
  collapse :: Term xs -> Term ys

-- thanks @AndrasKovacs, @rhendric, @effectfully!
-- See https://discourse.haskell.org/t/challenge-implement-automatic-type-level-permutation/9610
class CInsert x xs ys | x ys -> xs where
  cinsert :: Insert x xs ys

class CInsert_fallback x y xs ys | x y ys -> xs where
  cinsert_fallback :: Proxy y -> Insert x xs (y : ys)
instance {-# INCOHERENT #-} (a ~ b, xs ~ ys) => CInsert_fallback (Expr a) (Expr b) xs ys where
  cinsert_fallback Proxy = IN
instance  (xs ~ y : xs', CInsert x xs' ys) => CInsert_fallback x y xs ys where
  cinsert_fallback Proxy = IS cinsert

instance xs ~ ys => CInsert x xs (x : ys) where
  cinsert = IN
instance {-# INCOHERENT #-} CInsert_fallback x y xs ys => CInsert x xs (y : ys) where
  cinsert = cinsert_fallback (Proxy @y)

class CPermutation (xs :: [a]) (ys :: [a]) where
  cpermutation :: Permutation xs ys
instance CPermutation '[] '[] where
  cpermutation = PN
instance (CInsert x ys ys', CPermutation xs ys) => CPermutation (x : xs) ys' where
  cpermutation = PS cinsert cpermutation
instance {-# INCOHERENT #-} CPermutation xs xs where
  cpermutation = undefined -- FIXME

pr' :: CPermutation xs ys => Term xs -> Term ys
pr' = undefined

pr :: CPermutation ys xs => Term xs -> Term ys
pr = undefined

givePermutation :: Permutation xs ys -> (CPermutation xs ys => r) -> r
givePermutation _ _ = undefined

plam :: forall a b ls. (forall l. Term '[l, Expr a] -> Term (l : Expr b : ls)) -> Term (LC : Expr (a #-> b) : ls)
plam f = Term (Lam $ f $ Term Var (PS IN (PS IN PN))) cpermutation

data PList (a :: PType) :: PType

data ListLang
data instance L ListLang ls where
  Nil :: L ListLang '[Expr (PList a)]
  Cons :: Merges SumNode ls0 ls1 ls -> Term (Expr a : ls0) -> Term (Expr (PList a) : ls1) -> L ListLang (Expr (PList a) : ls)
  ListMatch ::
    Merges SumNode ls10 ls11 ls1 ->
    Merges ProductNode ls0 ls1 ls ->
    Term (Expr (PList a) : ls0) ->
    Term (Expr b : ls10) ->
    Term (Expr b : ls11) -> -- FIXME: pass in head and tail
    L ListLang (Expr b : ls)

pnil :: Term '[Expr (PList a), ListLang]
pnil = Term Nil cpermutation

pcons ::
  forall a left' left right' right combined.
  (CInsert (Expr a) left' left, CInsert (Expr (PList a)) right' right, CAppend left' right' combined) =>
  Term left -> Term right -> Term (Expr (PList a) : ListLang : combined)
pcons x xs = Term (Cons cappend (pr x :: Term (Expr a : left')) (pr xs :: Term (Expr (PList a) : right'))) cpermutation
{-

--pcons = Term '[Expr (a #-> PList a #-> PList a), LC, LC, ListLang, ListLang]
--pcons = plam \x -> undefined $ plam \y ->

psingleton :: Term '[LC, Expr (a #-> PList a), ListLang, ListLang]
psingleton = plam \x -> pr $ pcons x pnil

--plist_of_3 :: Term '[LC, LC, LC, Expr (a #-> a #-> a #-> PList a)]
--plist_of_3 = undefined $ plam \f -> undefined $ plam \acc -> flip3Term $ flip3Term $ plam \list -> undefined

pid :: Term '[LC, Expr (a #-> a)]
pid = plam id

data A
data B

c :: (forall ys. Insert A ys '[A, A] -> r) -> r
-- CInsert A ys '[A, A]
-- CInsert A
c f = f cinsert

{-
c :: Permutation '[A, A] '[A, A]
-- CPermutation '[A, A] '[A, A]
-- CPermutation '[A] ys
-- CInsert A ys '[A, A]
c = cpermutation
-}
-}
-}
