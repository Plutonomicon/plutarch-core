{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoFieldSelectors #-}

module Plutarch2New where

import Data.Kind (Constraint, Type)
import Type.Reflection (Typeable, TypeRep, eqTypeRep, typeRep, pattern HRefl)
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy (Proxy))
import Data.Coerce (Coercible)
import Generics.SOP.Dict (Dict (Dict))
import GHC.Fingerprint (Fingerprint)

witness :: c => Proxy c -> ()
witness c = let _ = witness c in ()

data ElemOf e es = UnsafeElemOf (TypeRep e)

here :: Typeable e => ElemOf e (e ': es)
here = UnsafeElemOf typeRep

there :: ElemOf e es -> ElemOf e (e' ': es)
there (UnsafeElemOf r) = UnsafeElemOf r

type PType = Type
newtype Tag = Tag Type
type TermTy = Tag -> Type
type Language = TermTy -> TermTy

class UnsafeRepresentational l where
  representational :: forall term term'. Coercible term term' => Dict (Coercible (l term)) (l term')

unsafeMakeCoercible :: Dict (Coercible a) b
unsafeMakeCoercible = unsafeCoerce (Dict :: Dict (Coercible ()) ())

instance {-# OVERLAPPABLE #-}
  (forall term term'.
    Coercible term term' =>
    Coercible (l term) (l term')
  ) => UnsafeRepresentational l where
  representational = Dict
type Representational = UnsafeRepresentational

class (Typeable l, Representational l) => IsLanguage (l :: Language)

class CryptoHashable (a :: Type) where
  cryptoHash :: (Int -> [b] -> b) -> a -> b

-- FIXME: require representationality
type Union :: [Language] -> Language
data Union (ls :: [Language]) (term :: TermTy) (tag :: Tag) = forall l. Representational l => Union (ElemOf l ls) (l term tag)

absurdUnion :: Union '[] term tag -> b
absurdUnion (Union (UnsafeElemOf t) _) = error $ "Union should be empty; contains " <> show t

matchUnion ::
  forall l ls term tag. IsLanguage l =>
  Union (l ': ls) term tag ->
  Either (Union ls term tag) (l term tag)
matchUnion (Union (UnsafeElemOf l'r) l') = case (eqTypeRep (typeRep :: TypeRep l) l'r) of
  Just HRefl -> Right l'
  Nothing -> Left (Union (UnsafeElemOf l'r) l')

class Inject (l :: Language) (ls :: [Language]) where
  inject :: l term tag %n -> Union ls term tag

instance (IsLanguage l) => Inject l (l ': ls) where
  inject l = Union here l

instance {-# OVERLAPPABLE #-} (IsLanguage l, Inject l ls) => Inject l (l' ': ls) where
  inject l = let _ = witness (Proxy @(Inject l ls)) in Union (UnsafeElemOf typeRep) l

--newtype RawTerm ls tag = RawTerm (Union ls (RawTerm ))

type family Injectable (x :: a) (xs :: [a]) :: Constraint where
  Injectable x (x ': _) = ()
  Injectable x (y ': xs) = Injectable x xs

type family Reorderable (xs :: [a]) (ys :: [a]) :: Constraint where
  Reorderable (x ': xs) (x ': ys) = Reorderable xs ys
  Reorderable (x ': xs) ys = (Injectable x ys, Reorderable xs ys)

data S = S
type Term :: S -> [Language] -> TermTy
data Term (s :: S) ls tag = Term
  { unTerm :: Union ls (Term s ls) tag
  }
unTerm :: Term s ls tag -> Union ls (Term s ls) tag
unTerm t = t.unTerm

send :: (IsLanguage l, Inject l ls) => l (Term s ls) tag %n -> Term s ls tag
send x = Term (inject x)

reorderMaybe :: Term s ls tag -> Term s ls' tag
reorderMaybe = unsafeCoerce

-- Warning! _Resolving_ this constraint is O(n*m) unfortunately
-- since we can't sort then compare ls and ls' (I think?).
class Reorder ls ls' where
  reorder :: Term s ls tag -> Term s ls' tag

instance Reorder '[] ls' where
  reorder = reorderMaybe

instance Reorder ls ls' => Reorder (l ': ls) (l ': ls') where
  reorder = let _ = witness (Proxy @(Reorder ls ls')) in reorderMaybe

instance {-# OVERLAPPABLE #-} (Inject l ls', Reorder ls ls') => Reorder (l ': ls) ls' where
  reorder = let _ = witness (Proxy @(Inject l ls', Reorder ls ls')) in reorderMaybe

data Expr' (a :: PType)
type Expr a = 'Tag (Expr' a)

data Eff' (a :: PType)
type Eff a = 'Tag (Eff' a)

data TypeInfo' (a :: PType)
type TypeInfo a = 'Tag (TypeInfo' a)

data Opaque (l :: Language) :: Language where
  Opaque :: l term tag -> Opaque l term tag
  deriving anyclass (IsLanguage)
instance Representational l => UnsafeRepresentational (Opaque l) where
  representational = unsafeMakeCoercible

data Arithmetic :: Language where
  Add :: term (Expr Int) -> term (Expr Int) -> Arithmetic term (Expr Int)
  IntLiteral :: Int -> Arithmetic term (Expr Int)
  Double :: term (Expr Int) %1 -> Arithmetic term (Expr Int)
  IntTy :: Arithmetic term (TypeInfo Int)
  deriving anyclass (IsLanguage)

instance CryptoHashable Int where
  cryptoHash f x = f x []

instance (forall tag'. CryptoHashable (term tag')) => CryptoHashable (Arithmetic term tag) where
  cryptoHash :: (Int -> [a] -> a) -> Arithmetic term tag -> a
  cryptoHash f (Add x y) = f 0 [cryptoHash f x, cryptoHash f y]
  cryptoHash f (IntLiteral n) = f 1 [cryptoHash f n]
  cryptoHash f (Double x) = f 2 [cryptoHash f x]
  cryptoHash f IntTy = f 3 []

data LetBindings :: Language where
  Let :: term (TypeInfo a) -> (term (Expr a) -> term (Expr b)) -> term (Expr a) -> LetBindings term (Expr b)
  deriving anyclass (IsLanguage)

instance (forall tag'. CryptoHashable (term tag')) => CryptoHashable (LC term tag) where

data Proc (a :: PType) (b :: PType)

data LC :: Language where
  MkLam :: (term (Expr a) -> term (Expr b)) -> LC term (Expr (a -> b))
  AppLam :: term (TypeInfo a) -> term (Expr (a -> b)) -> term (Expr a) -> LC term (Expr b)
  --MkProc :: (term (Expr a) -> term (Eff b)) -> LC term (Expr (Proc a b))
  --AppProc :: term (TypeInfo a) -> term (Expr (Proc a b)) -> term (Expr a) -> LC term (Eff b)
  FunTy :: term (TypeInfo a) -> term (TypeInfo b) -> LC term (TypeInfo (a -> b))
  deriving anyclass (IsLanguage)

data LC_HOAS :: Language where
  MkLamHOAS :: (term (Expr a) -> term (Expr b)) -> LC_HOAS term (Expr (a -> b))

data LC_DB :: Language where
  MkLamDB :: term (Expr b) -> LC_DB term (Expr (a -> b))
 
data Untyped :: Language where
  DummyTy :: Untyped term (TypeInfo a)
  deriving anyclass (IsLanguage)

data SequenceEff :: Language where
  SequenceEff :: term (TypeInfo a) -> term (Eff a) -> (term (Expr a) -> term (Eff b)) -> SequenceEff term (Eff b)
  deriving anyclass (IsLanguage)

data LCDBType = LCDBInt | LCDBFun LCDBType LCDBType
  deriving stock (Show)

data LCDB = DoubleDB LCDB | LvlDB Int | AppDB LCDB LCDB | LamDB LCDBType LCDB | LitDB Int | AddDB LCDB LCDB
  deriving stock (Show)

data VarIdx :: Language where
  VarIdx :: Int -> VarIdx term (Expr a)
  deriving anyclass (IsLanguage)

data VarLvl :: Language where
  VarLvl :: Int -> VarLvl term (Expr a)
  deriving anyclass (IsLanguage)

newtype ClosedTerm ls tag = ClosedTerm { openClosedTerm :: forall s. Term s ls tag }
openClosedTerm :: ClosedTerm ls tag -> Term s ls tag
openClosedTerm (ClosedTerm x) = x
unsafeCloseOpenTerm :: Term s ls tag -> ClosedTerm ls tag
unsafeCloseOpenTerm = unsafeCoerce

{-
interpret :: ClosedTerm '[Arithmetic, LC] (TypeInfo a) -> ClosedTerm '[Arithmetic, LC] (Expr a) -> LCDB
interpret = \tyinfo t -> interpret' 0 (reorder $ openClosedTerm tyinfo) (reorder $ openClosedTerm t) where
  interpret' :: Int -> Term s '[Opaque VarLvl, Arithmetic, LC] (TypeInfo a) -> Term s '[Opaque VarLvl, Arithmetic, LC] (Expr a) -> LCDB
  interpret' lvl tyinfo (Term u) = case matchUnion u of
    Right (Opaque (VarLvl lvl)) -> LvlDB lvl
    Left u -> case matchUnion u of
      Right (Add x y) -> AddDB (interpret' lvl (send IntTy) x) (interpret' lvl (send IntTy) y)
      Right (IntLiteral l) -> LitDB l
      Right (Double x) -> DoubleDB (interpret' lvl (send IntTy) x)
      Left u -> case matchUnion u of
        Right (AppLam tyinfo' x y) -> AppDB (interpret' lvl (send $ FunTy tyinfo' (reorder tyinfo)) x) (interpret' lvl undefined y)
        Right (MkLam f) ->
          case matchUnion (unTerm tyinfo) of
            Right (Opaque x) -> case x of
            Left u -> case matchUnion u of
              Right x -> case x of
              Left u -> case matchUnion u of
                Right (FunTy _ b) -> LamDB LCDBInt (interpret' (lvl + 1) b $ f (send $ Opaque $ VarLvl lvl))
                Left u -> absurdUnion u
        Right (MkProc _) -> error "unimplemented" --
        Left u -> absurdUnion u
-}

takeTwoAndAdd :: Term s '[Arithmetic, LC] (Expr (Int -> Int -> Int))
takeTwoAndAdd = send $ MkLam \x -> send $ MkLam \y -> send $ Add y (reorder x)

--result :: LCDB
--result = interpret (ClosedTerm $ send $ FunTy (send IntTy) (send $ FunTy (send IntTy) $ send IntTy)) $ ClosedTerm takeTwoAndAdd

data HasPairs :: Language where
  MkPair :: term (Expr a) -> term (Expr b) -> HasPairs term (Expr (a, b))
  FstPair :: term (Expr (a, b)) -> HasPairs term (Expr a)
  SndPair :: term (Expr (a, b)) -> HasPairs term (Expr b)

data LinLam (a :: PType) (b :: PType)

data Lin :: Language where
  MkLinLam :: (term (Expr a) %1 -> term (Expr b)) -> Lin term (Expr (LinLam a b))
  AppLinLam :: term (TypeInfo a) -> term (Expr (LinLam a b)) -> term (Expr a) -> Lin term (Expr b)
  deriving anyclass (IsLanguage)

linId :: Term s '[Arithmetic, Lin] (Expr (LinLam Int Int))
linId = send $ MkLinLam \x -> send (Double x)

data HasOnlyDouble :: Language where
  AlsoDouble :: term (Expr Int) -> HasOnlyDouble term (Expr Int)

newtype Send ls term = Send ( forall l tag. (IsLanguage l, Inject l ls) => l term tag -> term tag )
runSend :: forall ls term l tag. (IsLanguage l, Inject l ls) => Send ls term -> l term tag -> term tag
runSend (Send f) = f

{-
popTerm :: (forall term tag'. Send ls term -> l term tag' -> term tag') -> ClosedTerm (l ': ls) tag -> ClosedTerm ls tag
popTerm f = \(ClosedTerm t) -> ClosedTerm $ go t where
  go = undefined

pop_HasOnlyDouble :: Inject Arithmetic ls => ClosedTerm (HasOnlyDouble ': ls) tag -> ClosedTerm ls tag
pop_HasOnlyDouble = popTerm f where
  f :: Inject Arithmetic ls => Send ls term -> HasOnlyDouble term tag -> term tag
  f (Send send) (AlsoDouble t) = send $ Double t
-}
