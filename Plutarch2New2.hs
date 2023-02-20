{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoFieldSelectors #-}

module Plutarch2New where

import Data.Kind (Type)
import Type.Reflection (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy)
import Numeric.Natural (Natural)
import Data.Functor.Const (Const (Const), getConst)
import GHC.TypeLits
import GHC.Exts

witness :: c => Proxy c -> ()
witness c = let _ = witness c in ()

data ElemOf a as = UnsafeElemOf Natural (TypeRep a)

here :: Typeable a => ElemOf a (a ': as)
here = UnsafeElemOf 0 typeRep

there :: ElemOf a as -> ElemOf a (a' ': as)
there (UnsafeElemOf i t) = UnsafeElemOf (i + 1) t

class CElemOf a as where
  elemOf :: ElemOf a as

instance Typeable a => CElemOf a (a ': as) where
  elemOf = here

instance {-# OVERLAPPABLE #-} CElemOf a as => CElemOf a (a' ': as) where
  elemOf = there elemOf

type PType = Type
type Tag = Type -- TODO: Possibly replace with newtype of Type
type TermTy = [Language] -> Tag -> Type
type Language = Type -- TODO: Possibly replace with newtype of Type
data family L (l :: Language) :: TermTy -> [[Language]] -> Tag -> Type

data SBool :: Bool -> Type where
  STrue :: SBool 'True
  SFalse :: SBool 'False

class KnownBool b where
  knownBool :: SBool b

instance KnownBool 'True where
  knownBool = STrue

instance KnownBool 'False where
  knownBool = SFalse

class IsLanguageExpansible l ~ 'True => LangE l
instance IsLanguageExpansible l ~ 'True => LangE l
class IsLanguageExpansible l ~ 'True => LangC l
instance IsLanguageExpansible l ~ 'True => LangC l

type SwapInList :: [a] -> [a] -> a -> a -> Type
data SwapInList xs ys x y where
  SWBase :: SwapInList (x ': xs) (y ': xs) x y
  SWInc :: SwapInList xs ys x y -> SwapInList (z ': xs) (z ': ys) x y

type SwapInList2 :: [[a]] -> [[a]] -> a -> a -> Type
data SwapInList2 xss yss x y where
  SwapInList2 :: SwapInList xss yss xs ys -> SwapInList xs ys x y -> SwapInList2 xss yss x y

--data Swappable (l :: Language) (l' :: Language) where

class
  ( KnownBool (IsLanguageContractible l)
  , KnownBool (IsLanguageExpansible l)
  , Typeable l
  ) => IsLanguage (l :: Language) where
  type IsLanguageExpansible l :: Bool
  type IsLanguageContractible l :: Bool
  interpretIn ::
    forall f lss lss' l0 l1 tag.
    (Functor f, IsLanguage l0, IsLanguage l1) =>
    SwapInList2 lss lss' l0 l1 ->
    Interpreter l0 l1 f tag ->
    L l Term lss tag ->
    f (L l Term lss' tag)
  interpretIn = undefined

type ListAppend :: [a] -> [a] -> [a]
type family ListAppend xs ys where
  ListAppend '[] ys = ys
  ListAppend (x ': xs) ys = x ': (ListAppend xs ys)

type ListAppendAll :: [[a]] -> [a]
type family ListAppendAll xss where
  ListAppendAll '[] = '[]
  ListAppendAll (xs ': xss) = ListAppend xs (ListAppendAll xss)

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

-- TODO: Don't store length of last list, technically not needed
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

data Union (l :: Language) (l' :: Language)
type Term :: TermTy
data Term ls tag where
  Send :: IsLanguage l => LengthsOf lss -> TypeRep l -> L l Term lss tag -> Term (l ': ListAppendAll lss) tag
  Expand :: IsLanguageExpansible l ~ 'True => Term ls tag -> Term (l ': ls) tag
  Contract :: IsLanguageContractible l ~ 'True => ElemOf l ls -> Term (l ': ls) tag -> Term ls tag
  Swap :: Term (l ': l' ': ls) tag -> Term (l' ': l ': ls) tag
  Pack :: Term (l ': l' ': ls) tag -> Term (Union l l' ': ls) tag
  Unpack :: Term (Union l l' ': ls) tag -> Term (l ': l' ': ls) tag
  Rotate :: Term (l0 ': l1 ': l2 ': ls) tag -> Term (l2 ': l0 ': l1 ': ls) tag

data Interpreter l l' f tag
  = Interpreter
    (forall lss. L l (TermF f) lss tag -> f (L l' Term lss tag))
    (forall lss. L l Term lss tag -> f (L l' Term lss tag))

runInterpreterStep :: Interpreter l l' f tag -> L l (TermF f) lss tag -> f (L l' Term lss tag)
runInterpreterStep (Interpreter step _) = step

runInterpreterBase :: Interpreter l l' f tag -> L l Term lss tag -> f (L l' Term lss tag)
runInterpreterBase (Interpreter _ base) = base

interpret ::
  forall f ls ls' l l' tag.
  (Functor f, IsLanguage l, IsLanguage l') =>
  SwapInList ls ls' l l' ->
  Interpreter l l' f tag ->
  Term ls tag ->
  f (Term ls' tag)
interpret SWBase intr (Send lengths tyrep x) = Send undefined undefined <$> runInterpreterBase intr x

sendLin :: (IsLanguage l, CLengthsOf lss, Typeable l) => L l Term lss tag -> Term (l ': ListAppendAll lss) tag
sendLin x = Send lengthsOf typeRep x

--class AllEqual (lss :: [[Language]]) (ls :: [Language])
--instance AllEqual '[] '[]

--send :: (CElemOf l ls, IsLanguageContractible l ~ True) => L l Term lss tag -> Term ls tag
--send x = undefined -- Send elemOf x

type TermF :: (Type -> Type) -> TermTy
newtype TermF f ls tag = TermF (f (Term ls tag))
unTermF :: TermF f ls tag -> f (Term ls tag)
unTermF (TermF t) = t

data Multiplicity = Free | Linear
data Expr (w :: Multiplicity) (a :: PType)
type FreeExpr = Expr 'Free
type LinExpr = Expr 'Linear
data Eff (a :: PType)
data TypeInfo (a :: PType)

data Arithmetic
data instance L Arithmetic _term _ls _tag where
  Add :: term ls0 (Expr w Int) -> term ls1 (Expr w Int) -> L Arithmetic term '[ls0, ls1] (Expr w Int)
  IntLiteral :: Int -> L Arithmetic term '[] (Expr w Int)
  Double :: term ls0 (Expr w Int) -> L Arithmetic term '[ls0] (Expr w Int)
  IntTy :: L Arithmetic term '[] (TypeInfo Int)
instance IsLanguage Arithmetic where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True
  interpretIn (SwapInList2 SWBase idx) f (Add x y) = flip Add y <$> interpret idx f x
  interpretIn (SwapInList2 (SWInc SWBase) idx) f (Add x y) = Add x <$> interpret idx f y
  interpretIn (SwapInList2 (SWInc (SWInc idx')) _) _ (Add _ _) = case idx' of
  interpretIn (SwapInList2 SWBase idx) f (Double x) = Double <$> interpret idx f x

data HasLinearVar (a :: PType)
data instance L (HasLinearVar _a) _term _ls _tag where
  LinearVar :: L (HasLinearVar a) term '[] (LinExpr a)
instance Typeable a => IsLanguage (HasLinearVar a) where
  type IsLanguageContractible _ = 'False
  type IsLanguageExpansible _ = 'False

data (a :: PType) --> (b :: PType)
infixr 0 -->

data LinearLC
data instance L LinearLC _term _ls _tag where
  LinLam :: term (HasLinearVar a ': ls0) (LinExpr b) -> L LinearLC term '[ls0] (LinExpr (a --> b))
  LinApp :: term ls0 (LinExpr (a --> b)) -> term ls1 (LinExpr a) -> L LinearLC term '[ls0, ls1] (LinExpr b)
instance IsLanguage LinearLC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data HasFreeVar (a :: PType)
data instance L (HasFreeVar _a) _term _ls _tag where
  FreeVar :: L (HasFreeVar a) term '[] (FreeExpr a)
instance Typeable a => IsLanguage (HasFreeVar a) where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data FreeLC
data instance L FreeLC _term _ls _tag where
  MakeLin :: term ls0 (FreeExpr a) -> L FreeLC term '[ls0] (LinExpr a)
  FreeLam :: term (HasFreeVar a ': ls0) (FreeExpr a) -> L FreeLC term '[ls0] (FreeExpr (a -> b))
  FreeApp :: term ls0 (FreeExpr (a -> b)) -> term ls1 (FreeExpr a) -> L FreeLC term '[ls0, ls1] (FreeExpr b)
instance IsLanguage FreeLC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data HOAS_LC
data instance L HOAS_LC _term _ls _tag where
  HOAS_Lam :: (term '[] (FreeExpr a) -> term ls0 (FreeExpr b)) -> L HOAS_LC term '[ls0] (FreeExpr (a -> b))
instance IsLanguage HOAS_LC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

double :: Term '[LinearLC] (LinExpr (Int --> Int))
double = sendLin $ LinLam $ sendLin LinearVar

add :: Term '[LinearLC, Arithmetic, LinearLC] (LinExpr (Int --> Int --> Int))
add = Unpack $ Swap $ sendLin $ LinLam $ Swap $ Pack $ sendLin $ LinLam $ Swap $ sendLin $ Add (sendLin (LinearVar @Int)) (sendLin (LinearVar @Int))

addSelf :: Term '[FreeLC, Arithmetic] (FreeExpr (Int -> Int))
addSelf = sendLin $ FreeLam $ Swap $ Contract elemOf $ Rotate $ sendLin $ Add (sendLin FreeVar) (sendLin $ FreeVar)

addSelf2 :: Term '[HOAS_LC, Arithmetic] (FreeExpr (Int -> Int))
addSelf2 = sendLin $ HOAS_Lam \x -> sendLin $ Add x x

eleven :: Term '[Arithmetic] (FreeExpr Int)
eleven = Contract here $ Contract here $ sendLin $ Add (sendLin $ IntLiteral 5) (sendLin $ IntLiteral 6)

data DummyLang
data instance L DummyLang _term _ls _tag where
instance IsLanguage DummyLang where
  type IsLanguageExpansible _ = 'True
  type IsLanguageContractible _ = 'True

interpretArithmetic :: Term '[Arithmetic] (FreeExpr Int) -> Int
interpretArithmetic x = getConst $ interpret SWBase (Interpreter step base) x where
  step :: L Arithmetic (TermF (Const Int)) ls' (FreeExpr Int) -> Const Int (L DummyLang Term ls' (FreeExpr Int))
  step (IntLiteral n) = Const n
  step (Add (TermF (Const x)) (TermF (Const y))) = Const (x + y)
  step (Double (TermF (Const x))) = Const $ x + x
  base :: L Arithmetic Term ls' (FreeExpr Int) -> Const Int (L DummyLang Term ls' (FreeExpr Int))
  base (IntLiteral n) = Const n
  base (Add _ _) = error "FIXME: prove impossible"
  base (Double _) = error "FIXME: prove impossible"
{-

jkk
data OnlyAdds
data instance L OnlyAdds _term _ls _tag where
  OnlyAdd :: term ls (Expr Int) -> term ls (Expr Int) -> L OnlyAdds term ls (Expr Int)
instance IsLanguage OnlyAdds where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

onlyAddsToArithmetic :: Term (OnlyAdds ': ls) tag -> Term (Arithmetic ': ls) tag
onlyAddsToArithmetic = runIdentity . interpret \case
  OnlyAdd (TermF (Identity x)) (TermF (Identity y)) -> Identity $ Add x y
-}
