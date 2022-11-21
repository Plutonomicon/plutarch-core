{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Backends.Nix (compileAp) where

import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (Identity), runIdentity)
import Data.Kind (Constraint, Type)
import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Text (Text, pack)
import Data.Text.Builder.Linear qualified as TB
import Generics.SOP (
  All2,
  ConstructorInfo (Constructor, Infix, Record),
  DatatypeInfo (ADT, Newtype),
  FieldInfo (FieldInfo),
  FieldName,
  K (K),
  NP (Nil, (:*)),
  NS (Z),
  SOP (SOP),
 )
import Generics.SOP.GGP (gdatatypeInfo, gfrom, gto)
import Generics.SOP.NP (POP (POP), collapse_NP, collapse_POP, liftA2_NP, liftA_NP, liftA_POP)
import Plutarch.Core (
  CompileAp,
  IsPTypeData (IsPTypeData),
  IsPTypePrim (isPTypePrim),
  PAp (papl, papr),
  PConcreteEf,
  PConstructablePrim (pcaseImpl, pconImpl, pmatchImpl),
  PDSL (IsPTypePrimData, PEffect),
  PDSLKind (PDSLKind),
  Term (Term),
  isPType,
  unTerm,
 )
import Plutarch.Frontends.Data (
  IsPTypeSOP (isPTypeSOP),
  IsPTypeSOPData (IsPTypeSOPData),
  PAny (PAny),
  PConstructorInfo (PRecord),
  PEither (PLeft, PRight),
  PPair (PPair),
 )
import Plutarch.Frontends.LC (PPolymorphic)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce))
import Plutarch.PType (PCode, PGeneric, PTypeF, Pf' (Pf'), pgfrom, pgto)
import Plutarch.Prelude
import Plutarch.Repr.SOP (PSOPed (PSOPed))

newtype Lvl = Lvl Int
  deriving newtype (Show)

data NixType
  = NFunTy NixType NixType
  | NForallTy Text NixType
  | NTyVar Text
  | NSetTy [(Text, NixType)]
  | NAnyTy
  | NUnionTy NixType NixType
  | NFixedStringTy Text
  deriving stock (Show)

getTabs :: ReaderT Int Identity TB.Builder
getTabs = do
  n <- ask
  pure $ fromString $ take (n * 2) $ repeat ' '

succTabs :: ReaderT Int Identity a -> ReaderT Int Identity a
succTabs = withReaderT (+ 1)

serialiseTy' :: NixType -> ReaderT Int Identity TB.Builder
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
serialiseTy' (NForallTy v x) = do
  x' <- serialiseTy' x
  pure $ "(forall " <> TB.fromText v <> ". " <> x' <> ")"
serialiseTy' NAnyTy = pure $ "Any"
serialiseTy' (NUnionTy a b) = do
  a' <- serialiseTy' a
  b' <- serialiseTy' b
  pure $ "(" <> a' <> "|" <> b' <> ")"
serialiseTy' (NFixedStringTy s) = pure $ "\"" <> TB.fromText s <> "\""

serialiseTy :: NixType -> Text
serialiseTy t = TB.runBuilder $ runIdentity $ runReaderT (serialiseTy' t) 0

data NOp
  = NApp
  | NPlus
  | NMinus
  | NMult
  | NDiv
  | NUpdate
  | NConcat
  | NLT
  | NLTE
  | NEq
  | NAnd
  | NOr
  deriving stock (Show)

data NixAST
  = NLam NixType Text NixAST
  | NOpApp NOp NixAST NixAST
  | NMkSet [(NixAST, NixAST)]
  | NString Text
  | NVar Text
  | NLet [(Text, NixAST)] NixAST
  | NIfThenElse NixAST NixAST NixAST
  | NDot NixAST NixAST
  deriving stock (Show)

serialise' :: NixAST -> TB.Builder
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
serialise' (NDot x (NString y)) = serialise' x <> "." <> TB.fromText y
serialise' (NDot x y) = serialise' x <> ".${" <> serialise' y <> "}"
serialise' (NOpApp op x y) = "(" <> serialise' x <> s <> serialise' y <> ")"
  where
    s = case op of
      NApp -> " "
      NPlus -> " + "
      NMinus -> " - "
      NMult -> " * "
      NDiv -> " / "
      NUpdate -> " // "
      NConcat -> " ++ "
      NLT -> " < "
      NLTE -> " <= "
      NEq -> " == "
      NAnd -> " && "
      NOr -> " || "

serialise :: NixAST -> Text
serialise v = TB.runBuilder $ serialise' v

newtype State = State {lvl :: Lvl}

initialState :: State
initialState = State {lvl = Lvl 0}

newtype M a = M (ReaderT State Identity a)
  deriving newtype (Functor, Applicative, Monad)

runM :: M a -> State -> a
runM (M x) s = coerce $ runReaderT x s

varify :: Lvl -> Text
varify l = pack $ 'x' : show l

getLvl :: M Lvl
getLvl = (.lvl) <$> M ask

succLvl :: M a -> M a
succLvl (M x) = M $ flip withReaderT x \(State (Lvl lvl)) -> (State $ Lvl $ lvl + 1)

mkTerm :: Applicative m => NixAST -> Term (Impl m) a
mkTerm x = Term $ Impl $ pure $ pure $ x

newtype Impl' m (a :: PType) = Impl {runImpl :: M (m NixAST)}
type Impl m = 'PDSLKind (Impl' m)

runTerm :: Term (Impl m) a -> M (m NixAST)
runTerm = runImpl . unTerm

getTy :: forall m a. IsPType (Impl m) a => Proxy m -> Proxy a -> NixType
getTy _ _ = case isPType :: IsPTypeData (Impl m) a of IsPTypeData (IsPTypePrimData t) -> t

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (a #-> b) where
  isPTypePrim = IsPTypePrimData $ NFunTy (getTy (Proxy @m) (Proxy @a)) (getTy (Proxy @m) (Proxy @b))

instance IsPTypePrim (Impl m) PAny where
  isPTypePrim = IsPTypePrimData NAnyTy

instance IsPTypePrim (Impl m) PUnit where
  isPTypePrim = IsPTypePrimData $ NSetTy []

instance IsPTypePrim (Impl m) PPType where
  isPTypePrim = IsPTypePrimData $ error "PPType has no type info"

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (PEither a b) where
  isPTypePrim =
    IsPTypePrimData $
      NUnionTy
        (NSetTy [("left", getTy (Proxy @m) (Proxy @a))])
        (NSetTy [("right", getTy (Proxy @m) (Proxy @b))])

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (PPair a b) where
  isPTypePrim = IsPTypePrimData $ NSetTy [("x", getTy (Proxy @m) (Proxy @a)), ("y", getTy (Proxy @m) (Proxy @b))]

instance (IsPTypeSOP (Impl m) a) => IsPTypePrim (Impl m) (PSOPed a) where
  isPTypePrim = IsPTypePrimData t
    where
      t :: NixType
      t = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info elems -> case (info, elems) of
        (IsPTypeSOPData _ _ _ (PRecord fields :* Nil), POP (tys :* Nil)) ->
          NSetTy $ collapse_NP $ liftA2_NP (\(K name) (IsPTypeData (IsPTypePrimData ty)) -> K (pack name, ty)) fields tys

instance IsPTypePrim (Impl m) (PForall f)

instance IsPTypePrim (Impl m) @(a #-> b) ( 'PLam f)

instance (IsPType (Impl m) a, IsPType (Impl m) b, Applicative m) => PConstructablePrim (Impl m) (a #-> b) where
  pconImpl (PLam f) = Impl do
    l <- varify <$> getLvl
    body <- succLvl $ runTerm $ f $ mkTerm $ NVar l
    pure $ NLam (getTy (Proxy @m) (Proxy @a)) l <$> body
  pmatchImpl x f = f (PLam g)
    where
      g :: Term (Impl m) a -> Term (Impl m) b
      g y = Term $ Impl do
        x <- runImpl x
        y <- runImpl $ unTerm y
        pure $ NOpApp NApp <$> x <*> y

instance PConstructablePrim (Impl m) PAny where
  pconImpl (PAny Proxy x) = coerce $ unTerm x
  pmatchImpl x f = f (PAny (Proxy @PAny) (Term x))
  pcaseImpl x f = f (PAny (Proxy @PAny) (Term x))

instance PDSL (Impl m) where
  newtype PEffect (Impl m) a = PEffect (Identity a)
    deriving newtype (Functor, Applicative, Monad)
  newtype IsPTypePrimData (Impl m) _ = IsPTypePrimData NixType

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl $ (x *>) <$> y
  papl (Term (Impl x)) y = Term $ Impl $ (<* y) <$> x

instance PUntyped (Impl m) where
  punsafeCoerce t = coerce t

instance PPolymorphic (Impl m)

instance PConstructablePrim (Impl m) PUnit

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PEither a b)

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PPair a b)

instance (Applicative m, IsPTypeSOP (Impl m) a) => PConstructablePrim (Impl m) (PSOPed a) where
  pconImpl (PSOPed x) = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info elems -> case (info, elems) of
    (IsPTypeSOPData _ _ _ (PRecord names :* Nil), _) ->
      Impl case pgfrom (Proxy @a) (Proxy @(PConcreteEf (Impl m))) $ gfrom x of
        SOP (Z vals) ->
          let f :: forall a' b m. Functor m => (a', M (m b)) -> M (m (a', b))
              f (name, val) = ((name,) <$>) <$> val
              g :: K FieldName ty -> Pf' (PConcreteEf (Impl m)) ty -> K (NixAST, M (m NixAST)) ty
              g (K name) (Pf' v) = K (NString (pack name), runTerm v)
           in ((NMkSet <$>) . sequenceA) <$> do traverse f $ collapse_NP $ liftA2_NP g names vals
  pmatchImpl = impl
    where
      impl = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info elems -> case (info, elems) of
        (IsPTypeSOPData _ _ (K _ :* Nil) (PRecord (names) :* Nil), POP ((_ :: NP (IsPTypeData (Impl m)) tys) :* Nil)) ->
          \t f -> Term $ Impl do
            l <- varify <$> getLvl
            t <- runImpl t
            let set :: NixAST
                set = NVar l
                fields :: NP (K NixAST) tys
                fields = liftA_NP (\(K name) -> K (NDot set (NString $ pack name))) names
                fields' :: NP (Pf' (PConcreteEf (Impl m))) tys
                fields' = liftA_NP (\(K ast) -> Pf' $ mkTerm ast) fields
                sopped :: a (PConcreteEf (Impl m))
                sopped = gto $ pgto (Proxy @a) (Proxy @(PConcreteEf (Impl m))) $ SOP $ Z $ fields'
            k <- succLvl $ runTerm (f $ PSOPed sopped)
            pure $ (\t k -> NLet [(l, t)] k) <$> t <*> k

instance PConstructablePrim (Impl m) (PForall f)

instance Applicative m => PNix (Impl m)

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m Text
compile' (Term t) =
  flip fmap (runM (runImpl t) initialState) $
    ("/* Type: " <>)
      . (serialiseTy (getTy (Proxy @m) (Proxy @a)) <>)
      . (" */ \n" <>)
      . serialise

compileAp :: CompileAp PNix Text
compileAp _ x = compile' x
