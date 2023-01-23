{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Backends.Nix (compileAp, compileTy) where

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
  PDSL (IsPTypePrimData, PIO, punsafePerformIO),
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
  PFix (PFix),
  PHasNewtypes,
  PPair (PPair),
  PRecursion,
  PSOP,
 )
import Plutarch.Frontends.LC (PPolymorphic)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce, punsafeGiveType))
import Plutarch.PType (PCode, Pf' (Pf'), pHs_inverse)
import Plutarch.Prelude
import Plutarch.Repr.Newtype (PNewtyped (PNewtyped))
import Plutarch.Repr.SOP (PSOPed (PSOPed))

newtype Lvl = Lvl Int
  deriving newtype (Show)

data NixType
  = NFunTy NixType NixType
  | NTyLam NixType Text NixType
  | NForallTy NixType
  | NFixTy NixType
  | NSomeTy NixType
  | NTyVar Text
  | NSetTy [(Text, NixType)]
  | NAnyTy
  | NVoidTy
  | NUnionTy NixType NixType
  | NFixedStringTy Text
  | NType
  | NUntyped
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
serialiseTy' (NTyLam t v x) = do
  t' <- serialiseTy' t
  x' <- serialiseTy' x
  pure $ "(" <> TB.fromText v <> " :: " <> t' <> " : " <> x' <> ")"
serialiseTy' (NForallTy x) = do
  x' <- serialiseTy' x
  pure $ "(forall " <> x' <> ")"
serialiseTy' (NFixTy x) = do
  x' <- serialiseTy' x
  pure $ "(fix " <> x' <> ")"
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
serialiseTy' NUntyped = pure $ "(N/A)"

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
  | NDot
  | NHas
  deriving stock (Show)

data NixAST
  = NLam NixType Text NixAST
  | NOpApp NOp NixAST NixAST
  | NMkSet [(NixAST, NixAST)]
  | NString Text
  | NVar Text
  | NLet [(Text, NixAST)] NixAST
  | NIfThenElse NixAST NixAST NixAST
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

serialise :: NixAST -> Text
serialise v = TB.runBuilder $ serialise' v

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

newtype Impl' m (a :: PType) = Impl {runImpl :: M (m NixAST)}
type Impl m = 'PDSLKind (Impl' m)

mkImpl :: Applicative m => NixAST -> UnPDSLKind (Impl m) a
mkImpl x = Impl $ pure $ pure $ x

mkTerm :: Applicative m => NixAST -> Term (Impl m) a
mkTerm x = Term $ Impl $ pure $ pure $ x

runTerm :: Term (Impl m) a -> M (m NixAST)
runTerm = runImpl . unTerm

mapTerm :: Functor m => (NixAST -> NixAST) -> Term (Impl m) a -> UnPDSLKind (Impl m) b
mapTerm f x = Impl $ (f <$>) <$> runTerm x

changeTy :: UnPDSLKind (Impl m) a -> UnPDSLKind (Impl m) b
changeTy = coerce

getTy :: forall m a. IsPType (Impl m) a => Proxy m -> Proxy a -> M NixType
getTy _ _ = case isPType :: IsPTypeData (Impl m) a of IsPTypeData (IsPTypePrimData t) -> t

instance PDSL (Impl m) where
  -- FIXME: fix PIO
  newtype PIO (Impl m) a = PIO (Identity a)
    deriving newtype (Functor, Applicative, Monad)
  newtype IsPTypePrimData (Impl m) _ = IsPTypePrimData (M NixType)
  punsafePerformIO (PIO x) = runIdentity x

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (a #-> b) where
  isPTypePrim = IsPTypePrimData do
    NFunTy <$> (getTy (Proxy @m) (Proxy @a)) <*> (getTy (Proxy @m) (Proxy @b))

instance IsPTypePrim (Impl m) PAny where
  isPTypePrim = IsPTypePrimData $ pure NAnyTy

instance IsPTypePrim (Impl m) PUnit where
  isPTypePrim = IsPTypePrimData $ pure $ NSetTy []

instance IsPTypePrim (Impl m) PPType where
  isPTypePrim = IsPTypePrimData $ pure NType

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (PEither a b) where
  isPTypePrim =
    IsPTypePrimData do
      left <- getTy (Proxy @m) (Proxy @a)
      right <- getTy (Proxy @m) (Proxy @b)
      pure $
        NUnionTy
          (NSetTy [("left", left)])
          (NSetTy [("right", right)])

instance (IsPType (Impl m) a, IsPType (Impl m) b) => IsPTypePrim (Impl m) (PPair a b) where
  isPTypePrim = IsPTypePrimData do
    x <- getTy (Proxy @m) (Proxy @a)
    y <- getTy (Proxy @m) (Proxy @b)
    pure $ NSetTy [("x", x), ("y", y)]

setInfo :: SListI tys => NP (IsPTypeData (Impl m)) tys -> NP (K FieldName) tys -> M [(Text, NixType)]
setInfo tys names =
  traverse (\(name, ty) -> (name,) <$> ty) $
    collapse_NP $
      liftA2_NP (\(K name) (IsPTypeData (IsPTypePrimData ty)) -> K (pack name, ty)) names tys

data H1 tys = H1 {unH1 :: NP (K FieldName) tys, _index :: Integer}

numericFieldNames :: SListI tys => NP (K FieldName) tys
numericFieldNames = unH1 $ para_SList (H1 Nil 0) (\(H1 n i) -> H1 (K ('_' : show i) :* n) (i + 1))

fieldNames :: SListI tys => PConstructorInfo tys -> NP (K FieldName) tys
fieldNames (PRecord names) = names
fieldNames PInfix = K "left" :* K "right" :* Nil
fieldNames PConstructor = numericFieldNames

instance (IsPTypeSOP (Impl m) a) => IsPTypePrim (Impl m) (PSOPed a) where
  isPTypePrim = IsPTypePrimData t
    where
      t :: M NixType
      t = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info -> case (info.constructorNames, info.constructorInfo, info.typeInfo) of
        (Nil, Nil, POP Nil) -> pure NVoidTy
        (K _ :* Nil, c :* _, POP (tys :* Nil)) -> NSetTy <$> setInfo tys (fieldNames c)
        (cns, cs, POP tyss) ->
          -- TODO: avoid use of partial function
          foldl1' (liftA2 NUnionTy) $ collapse_NP $ cliftA3_NP (Proxy @SListI) (\(K cn) c tys -> f cn c tys) cns cs tyss
          where
            f :: SListI tys => ConstructorName -> PConstructorInfo tys -> NP (IsPTypeData (Impl m)) tys -> K (M NixType) tys
            f cn c tys = K $ (\tys' -> NSetTy $ ("_constructor", NFixedStringTy (pack cn)) : tys') <$> setInfo tys (fieldNames c)

instance (IsPType (Impl m) a) => IsPTypePrim (Impl m) (PNewtyped a) where
  isPTypePrim = IsPTypePrimData $ getTy (Proxy @m) (Proxy @a)

instance
  forall m a (f :: PHs a -> PType).
  IsPType (Impl m) ('PLam f :: PHs (a #-> PPType)) =>
  IsPTypePrim (Impl m) (PForall1 f)
  where
  isPTypePrim = IsPTypePrimData do
    body <- getTy (Proxy @m) (Proxy @('PLam f :: PHs (a #-> PPType)))
    pure $ NForallTy body

instance
  forall m (f :: PType -> PType).
  IsPType (Impl m) ('PLam f :: PHs (PPType #-> PPType)) =>
  IsPTypePrim (Impl m) (PFix f)
  where
  isPTypePrim = IsPTypePrimData do
    body <- getTy (Proxy @m) (Proxy @('PLam f :: PHs (PPType #-> PPType)))
    pure $ NFixTy body

instance
  forall m a (f :: PHs a -> PType).
  IsPType (Impl m) ('PLam f :: PHs (a #-> PPType)) =>
  IsPTypePrim (Impl m) (PSome1 f)
  where
  isPTypePrim = IsPTypePrimData do
    body <- getTy (Proxy @m) (Proxy @('PLam f :: PHs (a #-> PPType)))
    pure $ NSomeTy body

instance
  ( forall (x :: PHs a). IsPType (Impl m) x => IsPType (Impl m) (f x)
  , IsPType (Impl m) a
  ) =>
  IsPTypePrim (Impl m) @(a #-> b) ('PLam f)
  where
  isPTypePrim = IsPTypePrimData do
    argty <- getTy (Proxy @m) (Proxy @a)
    lvl <- varify <$> getLvl
    body <-
      succLvl $
        withIsPType
          (IsPTypeData $ IsPTypePrimData $ pure $ NTyVar lvl :: IsPTypeData (Impl m) (TyVar @a))
          (getTy (Proxy @m) (Proxy @(f TyVar)))
    pure $ NTyLam argty lvl body

instance (IsPType (Impl m) a, IsPType (Impl m) b, Applicative m) => PConstructablePrim (Impl m) (a #-> b) where
  pconImpl (PLam f) = Impl do
    l <- varify <$> getLvl
    body :: m NixAST <- succLvl $ runTerm $ f $ mkTerm $ NVar l
    pure <$> (flip NLam l <$> (getTy (Proxy @m) (Proxy @a))) <&> (<*> body)
  pmatchImpl x f = f (PLam g)
    where
      g :: Term (Impl m) a -> Term (Impl m) b
      g y = Term $ Impl do
        x <- runImpl x
        y <- runImpl $ unTerm y
        pure $ NOpApp NApp <$> x <*> y
  pcaseImpl = error "FIXME"

instance PConstructablePrim (Impl m) PAny where
  pconImpl (PAny Proxy x) = coerce $ unTerm x
  pmatchImpl x f = f (PAny (Proxy @PAny) (Term x))
  pcaseImpl x f = f (PAny (Proxy @PAny) (Term x))

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl $ (x *>) <$> y
  papl (Term (Impl x)) y = Term $ Impl $ (<* y) <$> x

instance PUntyped (Impl m) where
  punsafeCoerce t = coerce t
  punsafeGiveType = IsPTypeData $ IsPTypePrimData $ pure NUntyped

instance PPolymorphic (Impl m)

instance Applicative m => PConstructablePrim (Impl m) PUnit where
  pconImpl _ = mkImpl $ NMkSet []
  pmatchImpl _ f = f PUnit
  pcaseImpl = error "FIXME"

instance (Applicative m, IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PEither a b) where
  pconImpl (PLeft left) = flip mapTerm left \left -> NMkSet [(NString "left", left)]
  pconImpl (PRight right) = flip mapTerm right \right -> NMkSet [(NString "right", right)]
  pmatchImpl t f =
    Term $ Impl do
      l <- varify <$> getLvl
      t <- runImpl t
      f_left <- succLvl $ runTerm $ f $ PLeft (mkTerm $ NOpApp NDot (NVar l) (NString "left"))
      f_right <- succLvl $ runTerm $ f $ PLeft (mkTerm $ NOpApp NDot (NVar l) (NString "right"))
      let k = NIfThenElse (NOpApp NHas (NVar l) (NString "left")) <$> f_left <*> f_right
      pure $ (\t k -> NLet [(l, t)] k) <$> t <*> k
  pcaseImpl = error "FIXME"

instance (Applicative m, IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PPair a b) where
  pconImpl (PPair x y) = Impl do
    x <- runTerm x
    y <- runTerm y
    pure $ (\x y -> NMkSet [(NString "x", x), (NString "y", y)]) <$> x <*> y
  pmatchImpl t f =
    Term $ Impl do
      l <- varify <$> getLvl
      t <- runImpl t
      k <- succLvl $ runTerm $ f $ PPair (mkTerm $ NOpApp NDot (NVar l) (NString "x")) (mkTerm $ NOpApp NDot (NVar l) (NString "y"))
      pure $ (\t k -> NLet [(l, t)] k) <$> t <*> k
  pcaseImpl = error "FIXME"

setConstruct :: (Applicative m, SListI tys) => NP (Pf' (PConcreteEf (Impl m))) tys -> NP (K FieldName) tys -> M (m NixAST)
setConstruct vals names =
  let f :: forall a' b m. Functor m => (a', M (m b)) -> M (m (a', b))
      f (name, val) = ((name,) <$>) <$> val
      g :: K FieldName ty -> Pf' (PConcreteEf (Impl m)) ty -> K (NixAST, M (m NixAST)) ty
      g (K name) (Pf' v) = K (NString (pack name), runTerm v)
   in (NMkSet <$>) <$> do sequenceA_M $ fmap f $ collapse_NP $ liftA2_NP g names vals

instance (Applicative m, IsPTypeSOP (Impl m) a) => PConstructablePrim (Impl m) (PSOPed a) where
  pconImpl (PSOPed x) = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info ->
    case info.constructorInfo of
      c :* Nil ->
        case info.from x of
          SOP (Z vals) -> Impl $ setConstruct vals (fieldNames c)
          SOP (S next) -> case next of {}
      _ ->
        Impl $
          f
            info.constructorNames
            info.constructorInfo
            (unSOP $ info.from x)
        where
          f ::
            SListI2 ass =>
            NP (K ConstructorName) ass ->
            NP PConstructorInfo ass ->
            NS (NP (Pf' (PConcreteEf (Impl m)))) ass ->
            M (m NixAST)
          f (K cn :* _) (c :* _) (Z vals) = setConstruct (Pf' (mkTerm $ NString $ pack cn) :* vals) (K "_constructor" :* fieldNames c)
          f Nil Nil x = case x of {}
          f (K _ :* cns) (_ :* cs) (S next) = f cns cs next
  pmatchImpl t f =
    isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info ->
      Term $ Impl do
        l <- varify <$> getLvl
        t <- runImpl t
        let getFields :: SListI tys => PConstructorInfo tys -> NP (Pf' (PConcreteEf (Impl m))) tys
            getFields c = liftA_NP (\(K name) -> Pf' $ mkTerm $ NOpApp NDot (NVar l) (NString $ pack name)) (fieldNames c)
            ks :: POP (Pf' (PConcreteEf (Impl m))) (PCode a)
            ks = POP $ cliftA_NP (Proxy @SListI) (\c -> getFields c) info.constructorInfo
            -- TODO: use NP here too
            ks' :: [(SOP (Pf' (PConcreteEf (Impl m))) (PCode a))]
            ks' = apInjs_POP ks
            cns :: [ConstructorName]
            cns = collapse_NP info.constructorNames
            nixError :: NixAST
            nixError = NOpApp NApp (NOpApp NDot (NVar "builtins") (NString "throw")) (NString "unreachable")
            constructor :: NixAST
            constructor = NOpApp NDot (NVar l) (NString "_constructor")
        ks'' :: [m NixAST] <- succLvl $ sequenceA $ flip fmap ks' \fields -> runTerm $ f $ PSOPed $ info.to $ fields
        let k :: m NixAST = case cns of
              [_] -> head ks''
              _ -> foldl' (\acc (cn, k') -> NIfThenElse (NOpApp NEq constructor (NString $ pack cn)) <$> k' <*> acc) (pure nixError) $ zip cns ks''
        pure $ (\t k -> NLet [(l, t)] k) <$> t <*> k
  pcaseImpl = error "FIXME"

instance (IsPType (Impl m) a) => PConstructablePrim (Impl m) (PNewtyped a) where
  pconImpl (PNewtyped x) = changeTy $ unTerm x
  pmatchImpl t f = f (PNewtyped $ Term $ changeTy t)
  pcaseImpl = error "FIXME"

type family TyVar :: PHs a where

instance
  forall m a (f :: PHs a -> PType).
  IsPType (Impl m) ('PLam f :: PHs (a #-> PPType)) =>
  PConstructablePrim (Impl m) (PForall1 f)
  where
  -- TODO: Add explicit big lambda at term-level? Otherwise you get weird comments
  pconImpl t' = Impl do
    lvl <- varify <$> getLvl
    let d :: IsPTypeData (Impl m) (TyVar @a) = IsPTypeData $ IsPTypePrimData $ pure $ NTyVar lvl
    withIsPType d $ case pHs_inverse @a of
      Refl -> do
        let PForall1 (t :: Term (Impl m) (f (TyVar @a))) = t'
        succLvl $ runTerm t
  pmatchImpl t f = f (PForall1 (Term $ changeTy t))
  pcaseImpl = error "FIXME"

instance
  forall m (f :: PType -> PType).
  IsPType (Impl m) ('PLam f :: PHs (PPType #-> PPType)) =>
  PConstructablePrim (Impl m) (PFix f)
  where
  pconImpl (PFix t) = Impl $ runTerm t
  pmatchImpl t f = f (PFix (Term $ changeTy t))
  pcaseImpl = error "FIXME"

instance
  forall m a (f :: PHs a -> PType).
  IsPType (Impl m) ('PLam f :: PHs (a #-> PPType)) =>
  PConstructablePrim (Impl m) (PSome1 f)
  where
  -- TODO: Add explicit big lambda at term-level? Otherwise you get weird comments
  pconImpl t' = Impl case t' of
    PSome1 (Proxy @x) t -> runTerm t
  pmatchImpl t f = case pHs_inverse @a of
    Refl -> Term $ Impl do
      lvl <- varify <$> getLvl
      let d :: IsPTypeData (Impl m) (TyVar @a) = IsPTypeData $ IsPTypePrimData $ pure $ NTyVar lvl
      withIsPType d $ runTerm $ f (PSome1 (Proxy @(TyVar @a)) (Term $ changeTy t))
  pcaseImpl = error "FIXME"

instance PHasNewtypes (Impl m)
instance Applicative m => PSOP (Impl m)
instance PRecursion (Impl m)
instance Applicative m => PNix (Impl m)

compileTy' :: forall a. (IsPType (Impl Identity) a) => Proxy a -> Text
compileTy' _ = serialiseTy (runM (getTy (Proxy @Identity) (Proxy @a)) initialState)

compileTy :: CompileTy PNix Text
compileTy x = compileTy' x

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m Text
compile' (Term t) =
  flip fmap (runM (runImpl t) initialState) $
    ("/* Type: " <>)
      . (serialiseTy (runM (getTy (Proxy @m) (Proxy @a)) initialState) <>)
      . (" */ \n" <>)
      . serialise

compileAp :: CompileAp PNix Text
compileAp _ x = compile' x
