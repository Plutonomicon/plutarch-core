{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Plutarch.Backends.C (compileAp) where

import Control.Applicative (liftA2)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Data.Coerce (coerce)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.List (foldl', foldl1')
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Text (Text, pack)
import Data.Text.Builder.Linear qualified as TB
import Data.Type.Equality (pattern Refl)
import Generics.SOP (
  ConstructorName,
  FieldName,
  K (K),
  NP (Nil, (:*)),
  NS (S, Z),
  SListI,
  SListI2,
  SOP (SOP),
  para_SList,
  unSOP,
 )
import Generics.SOP.NP (
  POP (POP),
  cliftA3_NP,
  cliftA_NP,
  collapse_NP,
  liftA2_NP,
  liftA_NP,
 )
import Generics.SOP.NS (apInjs_POP)
import Plutarch.Core (
  CompileAp,
  CompileTy,
  IsPTypeData (IsPTypeData),
  IsPTypePrim (isPTypePrim),
  PAp (papl, papr),
  PConcreteEf,
  PConstructablePrim (pcaseImpl, pconImpl, pmatchImpl),
  PDSL (IsPTypePrimData, PEffect),
  PDSLKind (PDSLKind),
  Term (Term),
  UnPDSLKind,
  isPType,
  unTerm,
  withIsPType,
 )
import Plutarch.Frontends.Data (
  IsPTypeSOP (isPTypeSOP),
  IsPTypeSOPData (constructorInfo, constructorNames, from, to, typeInfo),
  PAny (PAny),
  PConstructorInfo (PConstructor, PInfix, PRecord),
  PEither (PLeft, PRight),
  PHasNewtypes,
  PPair (PPair),
  PSOP,
 )
import Plutarch.Frontends.Harvard (PHarvard)
import Plutarch.Frontends.LC (PPolymorphic)
import Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce))
import Plutarch.PType (PCode, Pf' (Pf'), pHs_inverse)
import Plutarch.Prelude
import Plutarch.Repr.Newtype (PNewtyped (PNewtyped))
import Plutarch.Repr.SOP (PSOPed (PSOPed))

newtype Lvl = Lvl Int
  deriving newtype (Show)

getTabs :: ReaderT Int Identity TB.Builder
getTabs = do
  n <- ask
  pure $ fromString $ take (n * 2) $ repeat ' '

succTabs :: ReaderT Int Identity a -> ReaderT Int Identity a
succTabs = withReaderT (+ 1)

{-
serialiseTy' :: CType -> ReaderT Int Identity TB.Builder
serialiseTy' (NFunTy a b) = do
  tabs <- getTabs
  l <- serialiseTy' a
  r <- serialiseTy' b
  pure $ l <> " ->\n" <> tabs <> r
serialiseTy' (NSetTy kvs) = do
  let f acc (k, v) = do
        acc <- acc
        tabs <- getTabs
        tabs' <- succTabs getTabs
        v' <- succTabs $ serialiseTy' v
        pure $ acc <> tabs <> TB.fromText k <> " ::\n" <> tabs' <> v' <> ";\n"
  kvs' <- succTabs $ foldl' f (pure mempty) kvs
  tabs <- getTabs
  pure $ "{\n" <> kvs' <> tabs <> "}"
serialiseTy' (NTyVar v) = pure $ TB.fromText v
serialiseTy' (NTyLam t v x) = do
  t' <- serialiseTy' t
  x' <- serialiseTy' x
  pure $ "(" <> TB.fromText v <> " :: " <> t' <> " : " <> x' <> ")"
serialiseTy' (NForallTy x) = do
  x' <- serialiseTy' x
  pure $ "(forall " <> x' <> ")"
serialiseTy' (NSomeTy x) = do
  x' <- serialiseTy' x
  pure $ "(some " <> x' <> ")"
serialiseTy' NAnyTy = pure $ "Any"
serialiseTy' NVoidTy = pure $ "Void"
serialiseTy' (NUnionTy a b) = do
  a' <- serialiseTy' a
  b' <- serialiseTy' b
  pure $ "(" <> a' <> "|" <> b' <> ")"
serialiseTy' (NFixedStringTy s) = pure $ "\"" <> TB.fromText s <> "\""
serialiseTy' NType = pure $ "*"
-}

serialiseTy :: CType -> Text
serialiseTy t = undefined -- TB.runBuilder $ runIdentity $ runReaderT (serialiseTy' t) 0

newtype Var = Var {unVar :: Text}
  deriving stock (Show)

data CType
  = CInt
  | CPointer CType
  | CFunPointer CType [CType]
  deriving stock (Show)

data COp
  = CPlus
  | CMinus
  | CMult
  | CDiv
  | CLT
  | CLTE
  | CEq
  | CAnd
  | COr
  | CXor
  | CNot
  deriving stock (Show)

data CExpr
  = COpApp COp CExpr CExpr
  | CDeref CExpr
  | CRef Var
  | CExprVar Var
  deriving stock (Show)

data CStmt
  = CCall {rty :: CType, rname :: Var, func :: Var, args :: [CExpr]}
  | CRet CExpr
  | CIf CExpr CStmt CStmt
  | CWhile CExpr CStmt
  | CBind {rty :: CType, rname :: Var, expr :: CExpr}
  deriving stock (Show)

data CDef = CDef
  { outTy :: CType
  , inTys :: [(Var, CType)]
  , name :: Text
  , body :: CStmt
  }
  deriving stock (Show)

data CModule = CModule
  { includes :: [Text]
  , defs :: [CDef]
  }

{-
serialise' :: CModule -> TB.Builder
serialise' (NLam ty v a) = "(" <> TB.fromText v <> " /* :: " <> (runIdentity $ runReaderT (serialiseTy' ty) 0) <> " */ : " <> serialise' a <> ")"
serialise' (NMkSet kvs) = foldl' f "{" kvs <> "}"
  where
    f acc (NString k, v) = acc <> TB.fromText k <> " = " <> serialise' v <> ";\n"
    f acc (k, v) = acc <> "${" <> serialise' k <> "} = " <> serialise' v <> ";\n"
serialise' (NString t) = "\"" <> TB.fromText t <> "\"" -- FIXME escape string
serialise' (NVar v) = TB.fromText v
serialise' (NLet kvs k) = foldl' f "(let " kvs <> "in " <> serialise' k <> ")"
  where
    f acc (k, v) = acc <> TB.fromText k <> " = " <> serialise' v <> ";\n"
serialise' (NIfThenElse cond x y) = "(if " <> serialise' cond <> " then " <> serialise' x <> " else " <> serialise' y <> ")"
serialise' (NOpApp op x y) = case op of
  NApp -> generic " "
  NPlus -> generic " + "
  NMinus -> generic " - "
  NMult -> generic " * "
  NDiv -> generic " / "
  NUpdate -> generic " // "
  NConcat -> generic " ++ "
  NLT -> generic " < "
  NLTE -> generic " <= "
  NEq -> generic " == "
  NAnd -> generic " && "
  NOr -> generic " || "
  NDot -> case y of
    NString y' -> serialise' x <> "." <> TB.fromText y'
    _ -> serialise' x <> ".${" <> serialise' y <> "}"
  NHas -> case y of
    NString y' -> serialise' x <> " ? " <> TB.fromText y'
    _ -> serialise' x <> " ? ${" <> serialise' y <> "}"
  where
    generic s = "(" <> serialise' x <> s <> serialise' y <> ")"
-}

serialise :: CModule -> Text
serialise v = undefined -- TB.runBuilder $ serialise' v

newtype State = State {lvl :: Lvl}

initialState :: State
initialState = State {lvl = Lvl 0}

newtype M a = M (ReaderT State Identity a)
  deriving newtype (Functor, Applicative, Monad)

sequenceA_M :: (Applicative m, Traversable t) => t (M (m a)) -> M (m (t a))
sequenceA_M = (sequenceA <$>) . sequenceA

runM :: M a -> State -> a
runM (M x) s = coerce $ runReaderT x s

varify :: Lvl -> Text
varify l = pack $ 'x' : show l

getLvl :: M Lvl
getLvl = (.lvl) <$> M ask

succLvl :: M a -> M a
succLvl (M x) = M $ flip withReaderT x \(State (Lvl lvl)) -> (State $ Lvl $ lvl + 1)

newtype Impl' m (a :: PType) = Impl {runImpl :: M (m CModule)}
type Impl m = 'PDSLKind (Impl' m)

mkImpl :: Applicative m => CModule -> UnPDSLKind (Impl m) a
mkImpl x = Impl $ pure $ pure $ x

mkTerm :: Applicative m => CModule -> Term (Impl m) a
mkTerm x = Term $ Impl $ pure $ pure $ x

runTerm :: Term (Impl m) a -> M (m CModule)
runTerm = runImpl . unTerm

mapTerm :: Functor m => (CModule -> CModule) -> Term (Impl m) a -> UnPDSLKind (Impl m) b
mapTerm f x = Impl $ (f <$>) <$> runTerm x

changeTy :: UnPDSLKind (Impl m) a -> UnPDSLKind (Impl m) b
changeTy = coerce

getTy :: forall m a. IsPType (Impl m) a => Proxy m -> Proxy a -> M CType
getTy _ _ = undefined -- case isPType :: IsPTypeData (Impl m) a of IsPTypeData (IsPTypePrimData t) -> t

instance PDSL (Impl m) where
  newtype PEffect (Impl m) a = PEffect (Identity a)
    deriving newtype (Functor, Applicative, Monad)
  data IsPTypePrimData (Impl m) _ = IsPTypePrimData

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl $ (x *>) <$> y
  papl (Term (Impl x)) y = Term $ Impl $ (<* y) <$> x

instance PHarvard (Impl m)

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m CModule
compile' (Term t) = runM (runImpl t) initialState

compileAp :: CompileAp PHarvard CModule
compileAp _ x = compile' x
