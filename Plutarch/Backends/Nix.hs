{-# LANGUAGE FlexibleInstances #-}

module Plutarch.Backends.Nix (compileAp, serialise, NixAST) where

import Data.Coerce (coerce)
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Text (Text)
import Plutarch.Core (
  CompileAp,
  IsPType',
  PAp (papl, papr),
  PConstructable' (pcaseImpl, pconImpl, pmatchImpl),
  PDSL (PEffect),
  PDSLKind (PDSLKind),
  Term (Term),
  unTerm,
 )
import Plutarch.Frontends.Data (PAny (PAny), PEither (PLeft, PRight), PPair (PPair))
import Plutarch.Frontends.Nix (PNix)
import Plutarch.Frontends.Untyped (PUntyped (punsafeCoerce))
import Plutarch.Prelude

newtype Lvl = Lvl Int
  deriving newtype (Show)

sc :: Lvl -> Lvl
sc (Lvl l) = Lvl (l + 1)

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
  | NSelect
  deriving stock (Show)

data NixAST
  = NLam Text NixAST
  | NOpApp NOp NixAST NixAST
  | NMkSet [(NixAST, NixAST)]
  | NString Text
  | NVar Text
  | NLet [(Text, NixAST)] NixAST
  deriving stock (Show)

serialise :: NixAST -> Text
serialise = fromString . show

newtype Impl' m (a :: PType) = Impl {runImpl :: Lvl -> m NixAST}
type Impl m = 'PDSLKind (Impl' m)

type TypeInfo :: (Type -> Type) -> forall k. PHs k -> Constraint
class TypeInfo (m :: Type -> Type) (x :: PHs a)

instance TypeInfo m (a #-> b)

instance TypeInfo m PAny

instance TypeInfo m PUnit

instance TypeInfo m PPType

instance (TypeInfo m a, TypeInfo m b) => TypeInfo m (PEither a b)

instance (TypeInfo m a, TypeInfo m b) => TypeInfo m (PPair a b)

instance Applicative m => PConstructable' (Impl m) (a #-> b) where
  pconImpl (PLam f) = Impl \l ->
    let n = fromString $ 'x' : show l
     in NLam n <$> (flip runImpl (sc l) $ unTerm $ f $ Term $ Impl $ const $ pure $ NVar n)
  pmatchImpl x f = f (PLam g)
    where
      g :: Term (Impl m) a -> Term (Impl m) b
      g y = Term $ Impl \l -> NOpApp NApp <$> runImpl x l <*> runImpl (unTerm y) l

instance PConstructable' (Impl m) PAny where
  pconImpl (PAny Proxy x) = coerce $ unTerm x
  pmatchImpl x f = f (PAny (Proxy @PAny) (Term x))
  pcaseImpl x f = f (PAny (Proxy @PAny) (Term x))

instance PDSL (Impl m) where
  newtype PEffect (Impl m) a = PEffect (Identity a)
    deriving newtype (Functor, Applicative, Monad)
  type IsPType' (Impl m) = TypeInfo m

instance Applicative m => PAp m (Impl m) where
  papr x (Term (Impl y)) = Term $ Impl \lvl -> x *> y lvl
  papl (Term (Impl x)) y = Term $ Impl \lvl -> x lvl <* y

instance PUntyped (Impl m) where
  punsafeCoerce t = coerce t

instance PConstructable' (Impl m) PUnit

instance (TypeInfo m a, TypeInfo m b) => PConstructable' (Impl m) (PEither a b)

instance (TypeInfo m a, TypeInfo m b) => PConstructable' (Impl m) (PPair a b)

instance Applicative m => PNix (Impl m)

compile' :: forall a m. (Applicative m, IsPType (Impl m) a) => Term (Impl m) a -> m NixAST
compile' (Term t) = runImpl t (Lvl 0)

compileAp :: CompileAp PNix NixAST
compileAp x = compile' x
