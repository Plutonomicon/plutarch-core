{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoFieldSelectors #-}
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

module Plutarch2New where

import Data.Kind (Type)
import Type.Reflection (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy)
import Numeric.Natural (Natural)
import Data.Functor.Const (Const (Const), getConst)
import GHC.TypeLits
import GHC.Exts
import Unsafe.Coerce
import Data.Type.Equality

witness :: c => Proxy c -> ()
witness c = let _ = witness c in ()

data ElemOf a as where
  Here :: ElemOf a (a ': as)
  There :: ElemOf a as -> ElemOf a (a' ': as)

here :: ElemOf a (a ': as)
here = Here

there :: ElemOf a as -> ElemOf a (a' ': as)
there = There

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

-- ListEqMod1 xs ys x tells us that ys is equal to xs but has an extra x somewhere
type ListEqMod1 :: [a] -> [a] -> a -> Type
data ListEqMod1 xs ys x where
  ListEqMod1Base :: ListEqMod1 xs (x ': xs) x
  ListEqMod1Step :: ListEqMod1 xs ys x -> ListEqMod1 (y ': xs) (y ': ys) x

class CListEqMod1 xs ys x where
  listEqMod1 :: ListEqMod1 xs ys x
instance CListEqMod1 '[x] '[x, x] x where
  listEqMod1 = ListEqMod1Base
instance {-# OVERLAPPABLE #-} CListEqMod1 xs (x ': xs) x where
  listEqMod1 = ListEqMod1Base
instance {-# OVERLAPPABLE #-} CListEqMod1 xs ys x => CListEqMod1 (y ': xs) (y ': ys) x where
  listEqMod1 = ListEqMod1Step listEqMod1

type RemoveFrom :: [a] -> a -> [a]
type family RemoveFrom xs x where
  RemoveFrom (x ': xs) x = xs
  RemoveFrom (y ': xs) x = y ': RemoveFrom xs x

-- Permute1 xs ys means that xs ys are equal one element being moved.
type Permute1 :: [a] -> [a] -> Type
data Permute1 xs ys where
  Permute1Base :: ListEqMod1 xs ys x -> Permute1 (x ': xs) ys
  Permute1BaseInv :: ListEqMod1 xs ys x -> Permute1 ys (x ': xs)
  Permute1Step :: Permute1 xs ys -> Permute1 (x ': xs) (x ': ys)

class CPermute1 xs ys where
  permute1 :: Permute1 xs ys
instance CListEqMod1 xs ys x => CPermute1 (x ': xs) ys where
  permute1 = Permute1Base listEqMod1
instance CPermute1 xs ys => CPermute1 (x ': xs) (x ': ys) where
  permute1 = Permute1Step permute1

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
    Interpreter l0 l1 f ->
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
  ListAppendAll '[xs] = xs
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
  SwapAt :: Permute1 ls ls' -> Term ls tag -> Term ls' tag
  Swap :: Term (l ': l' ': ls) tag -> Term (l' ': l ': ls) tag
  Pack :: Term (l ': l' ': ls) tag -> Term (Union l l' ': ls) tag
  Unpack :: Term (Union l l' ': ls) tag -> Term (l ': l' ': ls) tag
  Rotate :: Term (l0 ': l1 ': l2 ': ls) tag -> Term (l2 ': l0 ': l1 ': ls) tag

data Interpreter l l' f
  = Interpreter
    (forall lss tag. L l (TermF f) lss tag -> f (L l' Term lss tag))
    (forall lss tag. L l Term lss tag -> f (L l' Term lss tag))
    --(forall lss tag. L l ())

runInterpreterStep :: Interpreter l l' f -> L l (TermF f) lss tag -> f (L l' Term lss tag)
runInterpreterStep (Interpreter step _) = step

runInterpreterBase :: Interpreter l l' f -> L l Term lss tag -> f (L l' Term lss tag)
runInterpreterBase (Interpreter _ base) = base

interpret ::
  forall f ls ls' l l' tag.
  (Functor f, IsLanguage l, IsLanguage l') =>
  SwapInList ls ls' l l' ->
  Interpreter l l' f ->
  Term ls tag ->
  f (Term ls' tag)
interpret SWBase intr (Send lengths _ x) = Send lengths typeRep <$> runInterpreterBase intr x

contract :: (IsLanguageContractible l ~ 'True, CElemOf l ls) => Term (l ': ls) tag -> Term ls tag
contract x = Contract elemOf x

swapAt :: CPermute1 ls ls' => Term ls tag -> Term ls' tag
swapAt x = SwapAt permute1 x

bring :: forall l ls' ls tag. (ls' ~ RemoveFrom ls l, CListEqMod1 ls' ls l) => Term ls tag -> Term (l ': ls') tag
bring x = SwapAt (Permute1BaseInv listEqMod1) x

sendLin :: (IsLanguage l, CLengthsOf lss) => L l Term lss tag -> Term (l ': ListAppendAll lss) tag
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
data instance L Arithmetic term ls tag where
  Add :: term ls0 (Expr w Int) -> term ls1 (Expr w Int) -> L Arithmetic term '[ls0, ls1] (Expr w Int)
  Mult :: term ls0 (Expr w Int) -> term ls1 (Expr w Int) -> L Arithmetic term '[ls0, ls1] (Expr w Int)
  IntLiteral :: Int -> L Arithmetic term '[] (Expr w Int)
  Double :: term ls0 (Expr w Int) -> L Arithmetic term '[ls0] (Expr w Int)
  IntTy :: L Arithmetic term '[] (TypeInfo Int)
  IsZero :: term ls0 (Expr w Int) -> L Arithmetic term '[ls0] (Expr w Bool)
instance IsLanguage Arithmetic where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True
  interpretIn (SwapInList2 SWBase idx) f (Add x y) = flip Add y <$> interpret idx f x
  interpretIn (SwapInList2 (SWInc SWBase) idx) f (Add x y) = Add x <$> interpret idx f y
  interpretIn (SwapInList2 (SWInc (SWInc idx')) _) _ (Add _ _) = case idx' of
  interpretIn (SwapInList2 SWBase idx) f (Mult x y) = flip Mult y <$> interpret idx f x
  interpretIn (SwapInList2 (SWInc SWBase) idx) f (Mult x y) = Mult x <$> interpret idx f y
  interpretIn (SwapInList2 (SWInc (SWInc idx')) _) _ (Mult _ _) = case idx' of
  interpretIn (SwapInList2 SWBase idx) f (Double x) = Double <$> interpret idx f x
  interpretIn (SwapInList2 SWBase idx) f (IsZero x) = IsZero <$> interpret idx f x

data Arithmetic2
data instance L Arithmetic2 term ls tag where
  Arithmetic2 :: term (Arithmetic ': ls0) tag -> L Arithmetic2 term '[ls0] tag

data Conditionals
data instance L Conditionals term ls tag where
  If :: term ls0 (Expr w Bool) -> term ls1 (Expr w a) -> term ls1 (Expr w a) -> L Conditionals term '[ls0, ls1] (Expr w a)
instance IsLanguage Conditionals where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True
  interpretIn (SwapInList2 SWBase idx) f (If b x y) = flip (flip If x) y <$> interpret idx f b
  interpretIn (SwapInList2 (SWInc SWBase) idx) f (If b x y) = undefined (interpret idx f x) (interpret idx f y)

data HasLinVar (a :: PType)
data instance L (HasLinVar a) term ls tag where
  LinVar :: L (HasLinVar a) term '[] (LinExpr a)
instance Typeable a => IsLanguage (HasLinVar a) where
  type IsLanguageContractible _ = 'False
  type IsLanguageExpansible _ = 'False

data (a :: PType) --> (b :: PType)
infixr 0 -->

data LinearLC
data instance L LinearLC term ls tag where
  LinLam :: term (HasLinVar a ': ls0) (LinExpr b) -> L LinearLC term '[ls0] (LinExpr (a --> b))
  LinLam' :: term (HasLinVar a ': LinearLC ': ls0) (LinExpr b) -> L LinearLC term '[ls0] (LinExpr (a --> b))
  LinApp :: term ls0 (TypeInfo a) -> term ls1 (LinExpr (a --> b)) -> term ls2 (LinExpr a) -> L LinearLC term '[ls0, ls1, ls2] (LinExpr b)
instance IsLanguage LinearLC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data HasFreeVar (a :: PType)
data instance L (HasFreeVar _a) term ls tag where
  FreeVar :: L (HasFreeVar a) term '[] (FreeExpr a)
instance Typeable a => IsLanguage (HasFreeVar a) where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data FreeLC
data instance L FreeLC term ls tag where
  MakeLin :: term ls0 (FreeExpr a) -> L FreeLC term '[ls0] (LinExpr a)
  FreeLam :: term (HasFreeVar a ': ls0) (FreeExpr a) -> L FreeLC term '[ls0] (FreeExpr (a -> b))
  FreeApp :: term ls0 (TypeInfo a) -> term ls1 (FreeExpr (a -> b)) -> term ls2 (FreeExpr a) -> L FreeLC term '[ls0, ls1, ls2] (FreeExpr b)
instance IsLanguage FreeLC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data HOAS_LC
data instance L HOAS_LC term ls tag where
  HOAS_Lam :: (term '[] (FreeExpr a) -> term ls0 (FreeExpr b)) -> L HOAS_LC term '[ls0] (FreeExpr (a -> b))
instance IsLanguage HOAS_LC where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

data HasExp
data instance L HasExp term ls tag where
  Exp :: term ls0 (Expr w Int) -> term ls1 (Expr w Int) -> L HasExp term '[ls0, ls1] (Expr w Int)

double :: Term '[LinearLC] (LinExpr (Int --> Int))
double = sendLin $ LinLam $ sendLin LinVar

add :: Term '[LinearLC, Arithmetic] (LinExpr (Int --> Int --> Int))
add = contract $ sendLin $ LinLam $ bring $ sendLin $ LinLam $ bring $ sendLin $ Add (sendLin (LinVar @Int)) (sendLin (LinVar @Int))

add_expanded :: Term '[LinearLC, Arithmetic] (LinExpr (Int --> Int --> Int))
add_expanded = contract $ contract $ contract $ sendLin $ LinLam $ bring $ sendLin $ LinApp (sendLin IntTy) add (sendLin LinVar)

addSelf :: Term '[FreeLC, Arithmetic] (FreeExpr (Int -> Int))
addSelf = sendLin $ FreeLam $ Swap $ Contract elemOf $ Rotate $ sendLin $ Add (sendLin FreeVar) (sendLin $ FreeVar)

addSelf2 :: Term '[HOAS_LC, Arithmetic] (FreeExpr (Int -> Int))
addSelf2 = sendLin $ HOAS_Lam \x -> sendLin $ Add x x

eleven :: Term '[Arithmetic] (FreeExpr Int)
eleven = Contract here $ Contract here $ sendLin $ Add (sendLin $ IntLiteral 5) (sendLin $ IntLiteral 6)

linLam ::
  (CListEqMod1 ls' ls (HasLinVar a), CLengthOf ls', CElemOf LinearLC ls') =>
  Term ls (LinExpr b) -> Term ls' (LinExpr (a --> b))
linLam x = contract $ sendLin $ LinLam $ SwapAt (Permute1BaseInv listEqMod1) x

ifZeroThenPlusSixElseId :: Term '[LinearLC, Conditionals, Arithmetic] (LinExpr (Int --> Int --> Int))
ifZeroThenPlusSixElseId = contract $ bring @Arithmetic $ contract $ sendLin $ LinLam @Term @Int $ bring $ sendLin $ LinLam @Term @Int $ bring $ sendLin $ If (sendLin $ IsZero (sendLin (LinVar @Int))) (contract $ sendLin $ Add (sendLin $ IntLiteral 6) (sendLin LinVar)) (Expand $ sendLin (LinVar @Int))


data DummyLang
data instance L DummyLang term ls tag where
instance IsLanguage DummyLang where
  type IsLanguageExpansible _ = 'True
  type IsLanguageContractible _ = 'True

type InterpArithmetic :: TermTy
data family InterpArithmetic ls tag
newtype instance InterpArithmetic ls (Expr w a) = IA a

data family ExtractType :: Tag -> Type
newtype instance ExtractType (Expr w a) = ExtractType a
data instance ExtractType (TypeInfo a) = ExtractTypeInfo

interpretArithmetic :: Term '[Arithmetic] (FreeExpr Int) -> Int
interpretArithmetic x = getConst $ interpret SWBase (Interpreter step base) x where
  step :: L Arithmetic (TermF (Const Int)) lss tag -> Const Int (L DummyLang Term lss tag)
  step (IntLiteral n) = Const n
  step (Add (TermF (Const x)) (TermF (Const y))) = Const (x + y)
  step (Mult (TermF (Const x)) (TermF (Const y))) = Const (x * y)
  step (Double (TermF (Const x))) = Const $ x + x
  step (IsZero (TermF (Const _))) = error "FIXME" -- Const $ x == 0
  step IntTy = error "FIXME: make impossible"
  base :: L Arithmetic Term ls' tag -> Const Int (L DummyLang Term ls' tag)
  base (IntLiteral n) = Const n
  base _ = error "FIXME: prove impossible"
  f :: L Arithmetic InterpArithmetic lss tag -> ExtractType tag
  f (IntLiteral n) = ExtractType n
  f (Add (IA x) (IA y)) = ExtractType $ x + y
  f (Mult (IA x) (IA y)) = ExtractType $ x + y
  f (Double (IA x)) = ExtractType $ x + x
  f (IsZero (IA x)) = ExtractType $ x == 0
  f IntTy = ExtractTypeInfo
  g :: L Conditionals InterpArithmetic lss tag -> ExtractType tag
  g (If (IA b) (IA x) (IA y)) = ExtractType $ if b then x else y
  eta_reduce :: L LinearLC Term lss tag -> L LinearLC Term lss tag
  --eta_reduce (LinApp (X False x) y) = X False $ LinApp x y
  --eta_reduce (LinApp (X True x) y) = X False $ LinApp x y
  eta_reduce (LinLam body) = undefined

eta_reduce_opt :: Term '[LinearLC, Arithmetic] tag -> Term '[LinearLC, Arithmetic] tag
eta_reduce_opt (Contract Here (Send _ _ (LinLam (Send _ _ (LinApp _ lhs rhs))))) = _
eta_reduce_opt _ = error "unimplemented"
{-

jkk
data OnlyAdds
data instance L OnlyAdds term ls tag where
  OnlyAdd :: term ls (Expr Int) -> term ls (Expr Int) -> L OnlyAdds term ls (Expr Int)
instance IsLanguage OnlyAdds where
  type IsLanguageContractible _ = 'True
  type IsLanguageExpansible _ = 'True

onlyAddsToArithmetic :: Term (OnlyAdds ': ls) tag -> Term (Arithmetic ': ls) tag
onlyAddsToArithmetic = runIdentity . interpret \case
  OnlyAdd (TermF (Identity x)) (TermF (Identity y)) -> Identity $ Add x y
-}
