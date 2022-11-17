{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- FIXME remove
{-# OPTIONS_GHC -Wno-missing-methods #-}

module Plutarch.Backends.Nix (compileAp) where

import Data.Coerce (coerce)
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Text (Text, pack)
import Generics.SOP (
  All2,
  ConstructorInfo (Constructor, Infix, Record),
  DatatypeInfo (ADT, Newtype),
  FieldInfo (FieldInfo),
  K (K),
  NP (Nil, (:*)),
 )
import Generics.SOP.GGP (gdatatypeInfo)
import Generics.SOP.NP (POP (POP), collapse_NP, collapse_POP, liftA2_NP, liftA_NP, liftA_POP)
import Plutarch.Core (
  CompileAp,
  IsPTypePrim (isPTypePrim),
  PAp (papl, papr),
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
import Plutarch.PType (PCode, PGeneric, PTypeF)
import Plutarch.Prelude
import Plutarch.Repr.SOP (PSOPed)

newtype Lvl = Lvl Int
  deriving newtype (Show)

sc :: Lvl -> Lvl
sc (Lvl l) = Lvl (l + 1)

data NixType
  = NFunTy NixType NixType
  | NForallTy Text NixType
  | NTyVar Text
  | NSetTy [(Text, NixType)]
  | NAnyTy
  | NUnionTy NixType NixType
  | NFixedStringTy Text
  deriving stock (Show)

serialiseTy :: NixType -> Text
serialiseTy (NFunTy a b) = serialiseTy a <> " -> " <> serialiseTy b
serialiseTy (NSetTy kvs) = foldl' f "{" kvs <> "}"
  where
    f acc (k, v) = acc <> k <> " = " <> serialiseTy v <> ";\n"
serialiseTy (NTyVar v) = v
serialiseTy (NForallTy v x) = "(forall " <> v <> ". " <> serialiseTy x <> ")"
serialiseTy NAnyTy = "Any"
serialiseTy (NUnionTy a b) = "(" <> serialiseTy a <> "|" <> serialiseTy b <> ")"
serialiseTy (NFixedStringTy s) = "\"" <> s <> "\""

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

serialise :: NixAST -> Text
serialise (NLam ty v a) = "(" <> v <> " /* :: " <> serialiseTy ty <> " */ : " <> serialise a <> ")"
serialise (NMkSet kvs) = foldl' f "{" kvs <> "}"
  where
    f acc (k, v) = acc <> "${" <> serialise k <> "} = " <> serialise v <> ";\n"
serialise (NString t) = "\"" <> t <> "\"" -- FIXME escape string
serialise (NVar v) = v
serialise (NLet kvs k) = foldl' f "(let " kvs <> "in " <> serialise k <> ")"
  where
    f acc (k, v) = acc <> k <> " = " <> serialise v <> ";\n"
serialise (NIfThenElse cond x y) = "(if " <> serialise cond <> " then " <> serialise x <> " else " <> serialise y <> ")"
serialise (NDot x y) = serialise x <> ".{" <> serialise y <> "}"
serialise (NOpApp op x y) = "(" <> serialise x <> s <> serialise y <> ")"
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

newtype Impl' m (a :: PType) = Impl {runImpl :: Lvl -> m NixAST}
type Impl m = 'PDSLKind (Impl' m)

getTy :: forall m a. IsPType (Impl m) a => Proxy m -> Proxy a -> NixType
getTy m a = isPType (Proxy @(Impl m)) a \(IsPTypePrimData t) -> t

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

type family OpaqueEf :: PTypeF where

instance (IsPTypeSOP (Impl m) a) => IsPTypePrim (Impl m) (PSOPed a) where
  isPTypePrim = IsPTypePrimData t
    where
      -- TODO: improve type
      elms :: [[NixType]]
      elms = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \_ x -> collapse_POP $ liftA_POP (\(IsPTypePrimData t) -> K t) x
      t :: NixType
      t = isPTypeSOP (Proxy @(Impl m)) (Proxy @a) \info elems -> case (info, elems) of
        (IsPTypeSOPData _ _ (K con :* Nil) (PRecord fields :* Nil), POP (tys :* Nil)) -> NSetTy $ collapse_NP $ liftA2_NP (\(K name) (IsPTypePrimData ty) -> K (pack name, ty)) fields tys

{-
ADT _ _ (Constructor _ :* Nil) _ -> NSetTy $ zip (pack . ('_' :) . show <$> iterate (+ 1) (0 :: Integer)) (head elms)
ADT _ _ (Infix _ _ _ :* Nil) _ -> let [[x, y]] = elms in NSetTy [("left", x), ("right", y)]
ADT _ _ (Record _ fields :* Nil) _ ->
  NSetTy $ zip (collapse_NP $ liftA_NP (\(FieldInfo x) -> K (pack x)) fields) (head elms)
ADT _ _ _ _ -> error "sums not supported yet"
Newtype _ _ _ -> error "impossible"
-}

instance IsPTypePrim (Impl m) (PForall f)

instance IsPTypePrim (Impl m) @(a #-> b) ( 'PLam f)

instance (IsPType (Impl m) a, IsPType (Impl m) b, Applicative m) => PConstructablePrim (Impl m) (a #-> b) where
  pconImpl (PLam f) = Impl \l ->
    let n = fromString $ 'x' : show l
     in NLam (getTy (Proxy @m) (Proxy @a)) n <$> (flip runImpl (sc l) $ unTerm $ f $ Term $ Impl $ const $ pure $ NVar n)
  pmatchImpl x f = f (PLam g)
    where
      g :: Term (Impl m) a -> Term (Impl m) b
      g y = Term $ Impl \l -> NOpApp NApp <$> runImpl x l <*> runImpl (unTerm y) l

instance PConstructablePrim (Impl m) PAny where
  pconImpl (PAny Proxy x) = coerce $ unTerm x
  pmatchImpl x f = f (PAny (Proxy @PAny) (Term x))
  pcaseImpl x f = f (PAny (Proxy @PAny) (Term x))

instance PDSL (Impl m) where
  newtype PEffect (Impl m) a = PEffect (Identity a)
    deriving newtype (Functor, Applicative, Monad)
  newtype IsPTypePrimData (Impl m) x = IsPTypePrimData NixType

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl \lvl -> x *> y lvl
  papl (Term (Impl x)) y = Term $ Impl \lvl -> x lvl <* y

instance PUntyped (Impl m) where
  punsafeCoerce t = coerce t

instance PPolymorphic (Impl m)

instance PConstructablePrim (Impl m) PUnit

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PEither a b)

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PPair a b)

instance (IsPTypeSOP (Impl m) a) => PConstructablePrim (Impl m) (PSOPed a)

instance PConstructablePrim (Impl m) (PForall f)

instance Applicative m => PNix (Impl m)

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m Text
compile' (Term t) = serialise <$> runImpl t (Lvl 0)

compileAp :: CompileAp PNix Text
compileAp _ x = compile' x
