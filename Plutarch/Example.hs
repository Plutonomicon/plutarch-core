{-# LANGUAGE TypeFamilyDependencies, UndecidableInstances #-}

module Plutarch.Example where

import Unsafe.Coerce (unsafeCoerce)
import Plutarch.Core
import Data.Proxy (Proxy (Proxy))
import Data.Kind (Type, Constraint)

type PType = Type
data Expr (a :: PType)
data LC
data Var (a :: PType)
data instance L (Expr a) ls where
data instance L (Var a) ls where
  Var :: L (Var a) '[Expr a]
  VarCollapse :: Term (Var a : Var a : ls) -> L (Var a) ls
data instance L LC ls where
  Lam :: Term (Var a : Expr b : ls) -> L LC (Expr (a #-> b) : ls)
  LamConst :: Term (Expr b : ls) -> L LC (Expr (a #-> b) : ls)
  LamCollapse :: Term (LC : LC : ls) -> L LC ls
data App
data instance L App lc where
  App :: Term (Expr (a #-> b) : ls) -> Term (Expr a : ls) -> L App (Expr b : ls)

data PList :: PType -> PType

infixr 0 #->
data (#->) (a :: PType) (b :: PType)

class Interpretible (l :: Language) where
  interpret :: Proxy l -> ()

class All (c :: a -> Constraint) (l :: [a]) where
  --c_all ::
instance All c '[]
instance (c x, All c xs) => All c (x : xs)

{-
transPermute :: Permutation xs ys -> Permutation ys zs -> Permutation xs zs
transPermute = undefined

permuteTerm :: Permutation xs ys -> Term xs -> Term ys
permuteTerm = undefined
-}

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

-- thanks @rhendric!
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

reorderTerm :: CPermutation xs ys => Term xs -> Term ys
reorderTerm = undefined

reorderTermFlipped :: CPermutation ys xs => Term xs -> Term ys
reorderTermFlipped = undefined

givePermutation :: Permutation xs ys -> (CPermutation xs ys => r) -> r
givePermutation _ _ = undefined

plam :: forall a b ls. (forall l. Term '[Expr a, l] -> Term (Expr b : l : ls)) -> Term (LC : Expr (a #-> b) : ls)
plam f =
  let t = f (Term Var (PS (IS IN) (PS IN PN)))
      p :: Permutation ls ls
      p = case t of Term _ p' -> case flipPermutation p' of PS _ (PS _ p) -> stripPermutation p
  in givePermutation p $ Term (Lam (reorderTerm t :: Term (Var a : Expr b : ls))) cpermutation

-- explicit type family since this is erased to ()
data family Append :: [a] -> [a] -> [a] -> Type
data instance Append '[] ys ys = Append0
newtype instance Append (x : xs) ys (x : zs) = Append1 (Append xs ys zs)

class CAppend xs ys zs | xs ys -> zs where
  cappend :: Append xs ys zs
instance CAppend '[] ys ys where
  cappend = Append0
instance CAppend xs ys zs => CAppend (x : xs) ys (x : zs) where
  cappend = Append1 cappend

unsafeAppendProof :: Append xs ys zs
unsafeAppendProof = unsafeCoerce ()

data ListLang
data instance L ListLang ls where
  Nil :: L ListLang '[Expr (PList a)]
  Cons :: Append ls0 ls1 ls -> Term (Expr a : ls0) -> Term (Expr (PList a) : ls1) -> L ListLang (Expr (PList a) : ls)
  ListMatch ::
    Append ls0 ls1 ls2 ->
    Append ls2 ls3 ls ->
    Term (Expr (PList a) : ls0) ->
    Term (Expr b : ls1) ->
    Term (Expr b : ls3) -> -- FIXME: pass in head and tail
    L ListLang (Expr b : ls)

pnil :: Term '[Expr (PList a), ListLang]
pnil = Term Nil cpermutation

pcons' :: Term '[Expr a, Var a] -> Term '[Expr (PList a), Var (PList a)] -> Term '[Expr (PList a), ListLang, Var (PList a), Var a]
pcons' x xs = Term (Cons cappend x xs) cpermutation

--pcons = Term '[Expr (a #-> PList a #-> PList a), LC, LC, ListLang, ListLang]
--pcons = plam \x -> undefined $ plam \y ->

psingleton :: Term '[LC, Expr (a #-> PList a), ListLang, ListLang]
psingleton = plam \x -> Term (Cons cappend x (Term Nil (PS (IS IN) (PS IN PN)))) cpermutation

--plist_of_3 :: Term '[LC, LC, LC, Expr (a #-> a #-> a #-> PList a)]
--plist_of_3 = undefined $ plam \f -> undefined $ plam \acc -> flip3Term $ flip3Term $ plam \list -> undefined

pid :: Term '[Expr (a #-> a), LC]
pid = reorderTerm $ plam \x -> x

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
