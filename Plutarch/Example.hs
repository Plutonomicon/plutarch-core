{-# LANGUAGE TypeFamilyDependencies, UndecidableInstances, MagicHash, UnboxedTuples #-}

module Plutarch.Example where

import Unsafe.Coerce (unsafeCoerce, unsafeCoerce#)
import Plutarch.Core
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type, Constraint)
import GHC.Exts (ZeroBitType)

type Unit = (# #)
mkUnit :: () -> Unit
mkUnit () = (# #)
data Box (a :: ZeroBitType) = Box a

infix 0 :#:
type (:#:) :: Type -> Type -> ZeroBitType
newtype (:#:) a b = UnsafeEq (# #)

infix 0 :~:
data (:~:) (a :: Type) (b :: Type) where
  Refl :: a :~: a

mkEq :: Box (a :#: a)
mkEq = Box (UnsafeEq (# #))
unEq :: a :#: a -> a :~: a
unEq (UnsafeEq (# #)) = unsafeCoerce Refl

unsafeFakeZeroBitType :: forall (a :: ZeroBitType). Box a
unsafeFakeZeroBitType = Box (unsafeCoerce# (# #))

type ZeroPair :: ZeroBitType -> ZeroBitType -> ZeroBitType
newtype ZeroPair a b = UnsafeZeroPair (# #)

mkZeroPair :: a -> b -> ZeroPair a b
mkZeroPair _ _ = UnsafeZeroPair (# #)

unZeroPair :: ZeroPair a b -> (# a, b #)
unZeroPair _ = case (unsafeFakeZeroBitType, unsafeFakeZeroBitType) of (Box x, Box y) -> (# x, y #)

f :: (# #) -> Int
f (# #) = 0

type NodeKind = Type

data family Merge (kind :: NodeKind) (x :: Language) (y :: Language) :: Language -> ZeroBitType

type Merges :: NodeKind -> [Language] -> [Language] -> [Language] -> ZeroBitType
newtype Merges kind xs ys zs = UnsafeMerges (# #)

merges_base :: Box (Merges kind '[] '[] '[])
merges_base = Box (UnsafeMerges (# #))

merges_step :: Merge kind x y z -> Merges kind xs yz zs -> Merges kind (x : xs) (y : ys) (z : zs)
merges_step _ (UnsafeMerges (# #)) = (UnsafeMerges (# #))

merges_unstep :: Merges kind (x : xs) (y : ys) (z : zs) -> (# Merge kind x y z, Merges kind xs ys zs #)
merges_unstep (UnsafeMerges (# #)) = case unsafeFakeZeroBitType of Box x -> (# x, UnsafeMerges (# #) #)

type PType = [Language] -> Type
data Expr (a :: PType) :: Language
data TypeInfo (a :: PType) :: Language

data ProductNode :: NodeKind
data SumNode :: NodeKind

infixr 0 -->
data (-->) :: PType -> PType -> PType

{-
data App :: Language
data instance L App lc where
  App :: Merges ProductNode xs ys rs -> Term (Expr (a --> b) : xs) -> Term (Expr a : ys) -> L App (Expr b : rs)
newtype instance Merge kind App app0 app1 = MergeApp (app0 :~: App, app1 :~: App)

class CMerge (kind :: NodeKind) (x :: Language) (ys :: [Language]) (rs :: [Language]) where
  cmerge :: Merges 

class CMerges (kind :: NodeKind) (xs :: [Language]) (ys :: [Language]) (rs :: [Language]) | kind xs ys -> rs where
  cmerges :: CMerges kind xs ys rs

data LC :: Language
data Var (a :: PType) :: Language
data instance L (Expr a) ls where
data instance L (Var a) ls where
  Var :: L (Var a) '[Expr a]
  VarCollapse :: Term (Var a : Var a : ls) -> L (Var a) ls

data instance L LC ls where
  Lam :: Term (Var a : Expr b : ls) -> L LC (Expr (a #-> b) : ls)
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
