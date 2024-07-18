{-# LANGUAGE TypeFamilyDependencies, UndecidableInstances, MagicHash, UnboxedTuples, ViewPatterns, PatternSynonyms #-}

module Plutarch.Example where

import Unsafe.Coerce (unsafeCoerce, unsafeCoerce#)
import Plutarch.Core
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type, Constraint)
import GHC.Exts (ZeroBitType, TYPE)
import Data.Type.Equality ((:~:)(Refl))
import GHC.TypeLits (Nat, type (-))

type ZeroUnit = (# #)
mkZeroUnit :: () -> ZeroUnit
mkZeroUnit () = (# #)
type Box :: ZeroBitType -> Type
data Box a = Box a
unBox :: Box a -> a
unBox (Box x) = x

infix 4 ~#
type (~#) :: a -> a -> ZeroBitType
newtype (~#) x y = UnsafeEq (# #)

mkZeroRefl :: Box (a ~# a)
mkZeroRefl = Box (UnsafeEq (# #))
unZeroEq :: a ~# b -> a :~: b
unZeroEq (UnsafeEq (# #)) = unsafeCoerce Refl

pattern ZeroRefl :: () => a ~ b => a ~# b
pattern ZeroRefl <- (unZeroEq -> Refl) where
  ZeroRefl = unBox mkZeroRefl
{-# COMPLETE ZeroRefl #-}

unsafeFakeZeroBitType :: forall (a :: ZeroBitType). Box a
unsafeFakeZeroBitType = Box (unsafeCoerce# (# #))

type ZeroPair :: ZeroBitType -> ZeroBitType -> ZeroBitType
newtype ZeroPair a b = UnsafeZeroPair (# #)

mkZeroPair :: a -> b -> ZeroPair a b
mkZeroPair _ _ = UnsafeZeroPair (# #)

unZeroPair :: ZeroPair a b -> (Box a, Box b)
unZeroPair _ = (unsafeFakeZeroBitType, unsafeFakeZeroBitType)

pattern ZeroPair :: a -> b -> ZeroPair a b
pattern ZeroPair x y <- (unZeroPair -> (Box x, Box y)) where
  ZeroPair x y = mkZeroPair x y
{-# COMPLETE ZeroPair #-}

type ZeroEither :: ZeroBitType -> ZeroBitType -> ZeroBitType
newtype ZeroEither a b = UnsafeZeroEither (# #)

mkZeroLeft :: a -> ZeroEither a b
mkZeroLeft _ = UnsafeZeroEither (# #)

mkZeroRight :: b -> ZeroEither a b
mkZeroRight _ = UnsafeZeroEither (# #)

unsafeUnZeroEither :: forall (a :: ZeroBitType) (b :: ZeroBitType) (c :: ZeroBitType). ZeroEither a b -> (a -> c) -> (b -> c) -> c
unsafeUnZeroEither _ f g =
  case (unsafeFakeZeroBitType, unsafeFakeZeroBitType) of { (Box x, Box y) ->
    case f x of { _ ->
      case g y of _ -> case unsafeFakeZeroBitType of Box z -> z
    }
  }

type ZeroSome :: (a -> ZeroBitType) -> ZeroBitType
newtype ZeroSome f = UnsafeZeroSome (# #)

mkZeroSome :: f x -> ZeroSome f
mkZeroSome _ = UnsafeZeroSome (# #)

unZeroSome :: forall f rep (r :: TYPE rep). ZeroSome f -> (forall x. f x -> r) -> r
unZeroSome (UnsafeZeroSome (# #)) f = case unsafeFakeZeroBitType of Box x -> f x

type ZeroSomeHelper :: (a -> ZeroBitType) -> Type
data ZeroSomeHelper f = forall x. ZeroSomeHelper (f x)

zeroSomeHelper :: ZeroSome f -> ZeroSomeHelper f
zeroSomeHelper (UnsafeZeroSome (# #)) = ZeroSomeHelper (unBox unsafeFakeZeroBitType)

pattern ZeroSome
  :: forall a {f :: a -> ZeroBitType}.
     () =>
     forall (x :: a).
     f x -> ZeroSome f
pattern ZeroSome fx <- (zeroSomeHelper -> ZeroSomeHelper fx) where
  ZeroSome fx = mkZeroSome fx
{-# COMPLETE ZeroSome #-}

type ZeroSome6 :: (a0 -> a1 -> a2 -> a3 -> a4 -> a5 -> ZeroBitType) -> ZeroBitType
newtype ZeroSome6 f = UnsafeZeroSome6 (# #)

mkZeroSome6 :: f x0 x1 x2 x3 x4 x5 -> ZeroSome6 f
mkZeroSome6 _ = UnsafeZeroSome6 (# #)

unZeroSome6 :: forall f rep (r :: TYPE rep). ZeroSome6 f -> (forall x0 x1 x2 x3 x4 x5. f x0 x1 x2 x3 x4 x5 -> r) -> r
unZeroSome6 (UnsafeZeroSome6 (# #)) f = f (unBox unsafeFakeZeroBitType)

type ZeroSome6Helper :: (a0 -> a1 -> a2 -> a3 -> a4 -> a5 -> ZeroBitType) -> Type
data ZeroSome6Helper f = forall x0 x1 x2 x3 x4 x5. ZeroSome6Helper (f x0 x1 x2 x3 x4 x5)

zeroSome6Helper :: ZeroSome6 f -> ZeroSome6Helper f
zeroSome6Helper (UnsafeZeroSome6 (# #)) = ZeroSome6Helper (unBox unsafeFakeZeroBitType)

pattern ZeroSome6
  :: forall a0 a1 a2 a3 a4 a5 {f :: a0 -> a1 -> a2 -> a3 -> a4 -> a5 -> ZeroBitType}.
     () =>
     forall (x0 :: a0) (x1 :: a1) (x2 :: a2) (x3 :: a3) (x4 :: a4) (x5 :: a5).
     f x0 x1 x2 x3 x4 x5 -> ZeroSome6 f
pattern ZeroSome6 fx <- (zeroSome6Helper -> ZeroSome6Helper fx) where
  ZeroSome6 fx = mkZeroSome6 fx
{-# COMPLETE ZeroSome6 #-}

type ZeroForall :: (a -> ZeroBitType) -> ZeroBitType
newtype ZeroForall f = UnsafeZeroForall (# #)

mkZeroForall :: (forall x. f x) -> ZeroForall f
mkZeroForall _ = UnsafeZeroForall (# #)

unZeroForall :: ZeroForall f -> f x
unZeroForall (UnsafeZeroForall (# #)) = case unsafeFakeZeroBitType of Box x -> x

type NodeKind = Type

type MergeCategory = Type
type family GetMergeCategory (x :: Language) :: MergeCategory
type family GetMergeIndex (x :: Language) :: a

data family Merge (kind :: NodeKind) (category :: MergeCategory) (x :: a) (y :: a) :: a -> ZeroBitType

newtype MergesBase xs ys zs = MergesBase (ZeroPair (ZeroPair (xs ~# '[]) (ys ~# '[])) (zs ~# '[]))

{-
data HList as where
  HNil :: HList '[]
  HCons :: a -> HList as -> HList (a : as)

type Index :: forall a as. Nat -> HList as -> a
type family Index (idx :: Nat) (xs :: HList as) :: a where
  forall a as (x :: a) (xs :: HList as). Index @a @(a : as) 0 (HCons x xs) = x
  Index n (HCons y xs) = Index (n - 1) xs
-}

newtype MergesStep kind xs ys zs x y z xs' ys' zs' =
  MergesStep (
    ZeroPair
      (ZeroPair
        (ZeroPair (Merge kind x y z))
        (Merges kind xs' ys' zs'))
      (ZeroPair (xs ~# x : xs') (ZeroPair (ys ~# y : ys') (zs ~# z : zs')))
  )

type Merges :: NodeKind -> [Language] -> [Language] -> [Language] -> ZeroBitType
newtype Merges kind xs ys zs = Merges (ZeroEither (MergesBase xs ys zs) (ZeroSome6 (MergesStep kind xs ys zs)))

merges_base :: Box (Merges kind '[] '[] '[])
merges_base = Box (Merges (mkZeroLeft (MergesBase (ZeroPair (ZeroPair ZeroRefl ZeroRefl) ZeroRefl))))

merges_step :: Merge kind x y z -> Merges kind xs ys zs -> Merges kind (x : xs) (y : ys) (z : zs)
merges_step merge merges = Merges (mkZeroRight (ZeroSome6 (MergesStep (ZeroPair (ZeroPair merge merges) (ZeroPair ZeroRefl (ZeroPair ZeroRefl ZeroRefl))))))

merges_unstep :: Merges kind (x : xs) (y : ys) (z : zs) -> ZeroPair (Merge kind x y z) (Merges kind xs ys zs)
merges_unstep (Merges merges) =
  unsafeUnZeroEither
    merges
    (\(MergesBase (ZeroPair (ZeroPair _eq _) _)) -> unBox unsafeFakeZeroBitType) -- this case has a contradiction, be careful that we don't use it to type things illegally and cause e.g. a segfault
    (\(ZeroSome6 (MergesStep (ZeroPair (ZeroPair merge merges) (ZeroPair ZeroRefl (ZeroPair ZeroRefl ZeroRefl))))) -> ZeroPair merge merges)

type PType = [Language] -> Type
data Expr (a :: PType) :: Language
data TypeInfo (a :: PType) :: Language

data ProductNode :: NodeKind
data SumNode :: NodeKind

infixr 0 -->
data (-->) :: PType -> PType -> PType

data App :: Language
data instance L App lc where
  App :: Merges ProductNode xs ys rs -> Term (Expr (a --> b) : xs) -> Term (Expr a : ys) -> L App (Expr b : rs)
newtype instance Merge kind App app0 app1 = MergeAppLeft (ZeroPair (app0 ~# App) (app1 ~# App))
newtype instance Merge kind app0 App app1 = MergeAppRight (ZeroPair (app0 ~# App) (app1 ~# App))

{-

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
