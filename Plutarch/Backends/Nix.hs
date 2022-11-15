{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Backends.Nix (compileAp) where

import Data.Coerce (coerce)
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.List (foldl')
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Text (Text)
import Plutarch.Core (
  CompileAp,
  IsPTypePrim,
  PAp (papl, papr),
  PConstructablePrim (pcaseImpl, pconImpl, pmatchImpl),
  PDSL (PEffect),
  PDSLKind (PDSLKind),
  Term (Term),
  unTerm,
 )
import Plutarch.Frontends.Data (PAny (PAny), PEither (PLeft, PRight), PPair (PPair))
import Plutarch.Frontends.LC (PPolymorphic)
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce))
import Plutarch.PType (PGeneric)
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
  deriving stock (Show)

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

serialiseTy :: NixType -> Text
serialiseTy (NFunTy a b) = serialiseTy a <> " -> " <> serialiseTy b
serialiseTy (NSetTy kvs) = foldl' f "{" kvs <> "}"
  where
    f acc (k, v) = acc <> k <> " = " <> serialiseTy v <> ";\n"
serialiseTy (NTyVar v) = v
serialiseTy (NForallTy v x) = "(forall " <> v <> ". " <> serialiseTy x <> ")"

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

type TypeInfo :: (Type -> Type) -> forall k. PHs k -> Constraint
class TypeInfo (m :: Type -> Type) (x :: PHs a)

instance TypeInfo m (a #-> b)

instance TypeInfo m PAny

instance TypeInfo m PUnit

instance TypeInfo m PPType

instance (IsPType (Impl m) a, IsPType (Impl m) b) => TypeInfo m (PEither a b)

instance (IsPType (Impl m) a, IsPType (Impl m) b) => TypeInfo m (PPair a b)

instance PGeneric a => TypeInfo m (PSOPed a)

instance TypeInfo m (PForall f)

instance TypeInfo m @(a #-> b) ( 'PLam f)

instance Applicative m => PConstructablePrim (Impl m) (a #-> b) where
  pconImpl (PLam f) = Impl \l ->
    let n = fromString $ 'x' : show l
     in NLam undefined n <$> (flip runImpl (sc l) $ unTerm $ f $ Term $ Impl $ const $ pure $ NVar n)
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
  type IsPTypePrim (Impl m) = TypeInfo m

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl \lvl -> x *> y lvl
  papl (Term (Impl x)) y = Term $ Impl \lvl -> x lvl <* y

instance PUntyped (Impl m) where
  punsafeCoerce t = coerce t

instance PPolymorphic (Impl m)

instance PConstructablePrim (Impl m) PUnit

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PEither a b)

instance (IsPType (Impl m) a, IsPType (Impl m) b) => PConstructablePrim (Impl m) (PPair a b)

instance PGeneric a => PConstructablePrim (Impl m) (PSOPed a)

instance PConstructablePrim (Impl m) (PForall f)

instance Applicative m => PNix (Impl m)

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m Text
compile' (Term t) = serialise <$> runImpl t (Lvl 0)

compileAp :: CompileAp PNix Text
compileAp x = compile' x
