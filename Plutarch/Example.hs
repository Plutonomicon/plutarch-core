{-# LANGUAGE TypeFamilyDependencies #-}

module Plutarch.Example where

import Data.Functor.Compose (Compose)
import Plutarch.Core
import Plutarch.Internal.Utilities
import Data.Kind (Type)
import qualified GHC.TypeLits as TL

newtype PTypeF = PTypeF (PType -> Type)
type PType = PTypeF -> Type
-- data PPType f

data Uni = Free | Lin

type NumLinVars = Nat

-- An expression in the context S.
-- This is necessary because of linearity.
-- TODO: Figure out better solution
data Expr :: NumLinVars -> PType -> Tag

-- Contains information about the type.
-- This is necessary in nodes that don't mention all
-- input type variables in the output type, e.g. function application.
-- Assume you apply undefined to flip const and want to compile to the STLC,
-- an undefined of what?
data TypeInfo :: PType -> Tag

data PBool p = PFalse | PTrue
data PUnit p = PUnit
data PPair a b f = PPair (f ## a) (f ## b)
data PEither a b f = PLeft (f ## a) | PRight (f ## b)

infixr 0 ##
type family (##) (f :: PTypeF) (a :: PType) = (r :: Type) | r -> f a where
  ('PTypeF PHsW) ## a = PHs a
  ('PTypeF (PInstW ls tagger)) ## a = Term ls (tagger a)
  ('PTypeF f) ## a = f a

data PHsW a
type PHs a = a ('PTypeF PHsW)

-- Morally equivalent to `Compose (Term ls) tagger`
data PInstW ls tagger a
type PInst ls tagger a = a ('PTypeF (PInstW ls tagger))

type family (+) (x :: Nat) (y :: Nat) :: Nat where
  N + y = y
  (S x) + y = S (x + y)

data Bools' :: SimpleLanguage where
  And :: Bools' '[Expr lv0 PBool, Expr lv1 PBool] (Expr (lv0 + lv1) PBool)
  Not :: Bools' '[Expr lv0 PBool] (Expr lv0 PBool)
  BoolLit :: PHs PBool -> Bools' '[] (Expr N PBool)
  BoolTypeInfo :: Bools' '[] (TypeInfo PBool)
type Bools = InstSimpleLanguage Bools'

data PInt p

data Ints' :: SimpleLanguage where
  Mult :: Ints' '[Expr lv0 PInt, Expr lv1 PInt] (Expr (lv0 + lv1) PInt)
  Negate :: Ints' '[Expr lv0 PInt] (Expr lv0 PInt)
  IntLit :: PHs PInt -> Ints' '[] (Expr N PInt)
  IntTypeInfo :: Ints' '[] (TypeInfo PInt)
type Ints = InstSimpleLanguage Ints'

-- Something like this
data If :: Language where
data instance L If ls tag where
  If ::
    Term ls0 (Expr lv0 PBool) ->
    Term ls1 (Expr lv1 a) ->
    Term ls1 (Expr lv1 a) ->
    Catenation ls0 ls1 ls2 ->
    L If ls2 (Expr (lv0 + lv1) a)

data PFun :: Uni -> PType -> PType -> PType where

type (#->) = PFun Free
type (#->.) = PFun Lin
infixr 0 #->
infixr 0 #->.

-- Reverse order but irrelevant
data CatAll' :: [a] -> [[a]] -> [a] -> Type where
  CatAll'N :: CatAll' xs '[] xs
  CatAll'S :: Catenation ys xs xs' -> CatAll' xs' yss zs -> CatAll' xs (ys : yss) zs

type CatAll = CatAll' '[]

data LCBase :: Language where
data instance L LCBase ls tag where
  ExpandLCBase ::
    Term ls tag ->
    L LCBase ls tag
  ContractLCBase ::
    Term (LCBase : LCBase : ls) tag ->
    L LCBase ls tag
  -- Given a (free) function we can apply to it an expression
  -- that does not consume any linear variables.
  AppFree ::
    Term ls0 (TypeInfo a) ->
    Term ls1 (Expr lv0 (PFun w a b)) ->
    Term ls2 (Expr N a) ->
    CatAll '[ls0, ls1, ls2] ls3 ->
    L LCBase ls3 (Expr lv0 b)
  -- Given a linear function, we can apply to it any expression.
  AppLin ::
    Term ls0 (TypeInfo a) ->
    Term ls1 (Expr lv0 (PFun Lin a b)) ->
    Term ls2 (Expr lv1 a) ->
    CatAll '[ls0, ls1, ls2] ls3 ->
    L LCBase ls3 (Expr (lv0 + lv1) b)

-- A term with LCDB free_vars lin_vars s represents
-- a term that depends on free variabes free_vars,
-- and *consumes* the linear variables in lin_vars, in
-- the context s.
data LCDB :: [PType] -> [PType] -> Language where
data instance L (LCDB free_vars lin_vars) ls tag where
  -- We aren't consuming any linear variables here.
  ExpandLCDB ::
    Term ls tag ->
    L (LCDB free_vars '[]) ls tag
  -- We must consume the linear variables in both.
  ContractLCDB ::
    Term (LCDB free_vars lin_vars0 : LCDB free_vars lin_vars1 : ls) tag ->
    Catenation lin_vars0 lin_vars1 lin_vars2 ->
    L (LCDB free_vars lin_vars2) ls tag
  -- Given a context of any free variables,
  -- we can select any of them.
  VarFree ::
    ElemOf free_vars a ->
    L (LCDB free_vars '[]) '[] (Expr N a)
  -- We can construct linear variables, but the
  -- context is restricted, since we can only use them once.
  VarLin ::
    L (LCDB '[] '[a]) '[] (Expr (S N) a)
  -- Given an expression in the same context that depends on some linear
  -- variable of type a, we can turn it into a linear lambda.
  ExpandVarFree ::
    Term (LCDB free_vars0 lin_vars : ls) tag ->
    Catenation free_vars1 free_vars0 free_vars2 ->
    L (LCDB free_vars2 lin_vars) ls tag
  LamDBLin ::
    Term (LCDB free_vars (a : lin_vars) : ls) (Expr (S lv) b) ->
    L (LCDB free_vars lin_vars) ls (Expr lv (PFun Lin a b))
  -- Given an expression in the same context that depends on some free
  -- variable of type a, we can turn it into a free lambda.
  -- It must not depend on any linear variables, since otherwise
  -- those linear variables would be consumed more than once potentially.
  LamFree ::
    Term (LCDB (a : free_vars) '[] : ls) (Expr N b) ->
    L (LCDB free_vars '[]) ls (Expr N (PFun Free a b))

data LCHOAS :: Language where
-- A term with the `LCHOAS sf sl` language, where `sf` and `sl` are rigid,
-- is an open term. If they are ambiguous, it is a closed term.
-- They are split up to differentiate between linear and free variables.
data instance L LCHOAS ls tag where
  ExpandLCHOAS ::
    Term ls tag ->
    L LCHOAS ls tag
  ContractLCHOAS ::
    Term (LCHOAS : LCHOAS : ls) tag ->
    L LCHOAS ls tag
  -- | An embedded function defined by HOAS.
  -- The Haskell-level function can use the argument arbitrarily, but it is inherently
  -- opaque. It only knows it is a term of one language, but since it does not know it,
  -- it can not inspect it, preventing the issue plaguing HOAS with GADTs.
  -- The language must however be contractible, since if we use the argument twice,
  -- we might have the language twice, hence we need to contract it.
  LamHOASFree ::
    (forall var. Term '[var] (Expr N a) -> Contractible var -> Term (var : ls) (Expr N b)) ->
    L LCHOAS ls (Expr N (PFun Free a b))
  -- | A *linear* embedded function defined by HOAS.
  -- Similar to 'LamFree' with the difference that the language isn't contractible, and the
  -- expression is marked as linear.
  -- This prevents you from using it in a non-linear fashion, while still allowing
  -- each branch to use the same linear variable.
  LamHOASLin ::
    (forall var. Term '[var] (Expr (S N) a) -> Term (var : ls) (Expr (S lv) b)) ->
    L LCHOAS ls (Expr lv (PFun Lin a b))

data PSOPHOAS :: Language where
data instance L PSOPHOAS ls tag where
  ExpandPSOPHOAS ::
    Term ls tag ->
    L PSOPHOAS ls tag
  ContractPSOPHOAS ::
    Term (PSOPHOAS : PSOPHOAS : ls) tag ->
    L PSOPHOAS ls tag
  MatchHOASFree ::
    Term ls0 (Expr N a) ->
    (forall var. PInst '[var] (Expr N) a -> Contractible var -> Term (var : ls) (Expr N b)) ->
    L PSOPHOAS ls (Expr N b)


type family Any where

-- FIXME: Make existential
intr_HOAS_to_DB :: InterpretIn ls ls' LCHOAS (LCDB Any Any)
intr_HOAS_to_DB = InterpretIn \subls (Term' node intrs perm) ->
  case node of
    ExpandLCHOAS term -> undefined $ Term' (ExpandLCDB term) intrs perm
    LamHOASFree term ->
      let
        term' = term (flip Term ListEqMod1N $ Term' (VarFree ElemOfN) (InterpretAscN LengthOfTwoN) PermutationN) undefined
      in
      undefined $ Term' (LamFree term') (idInterpretation undefined) (idPermutation undefined)
    ContractLCHOAS term ->
      let
        term' = interpretTerm (interpretOne undefined intr_HOAS_to_DB) term
        term'' = interpretTerm (interpretOne undefined intr_HOAS_to_DB) (bringTerm (ListEqMod1S ListEqMod1N) term')
      in
      undefined term''
      --undefined $ Term' (LamFree (term $ VarFree ElemOfN))
    --ContractLCDB

{-
pnotNode :: Term ls (Expr w PBool) -> Term ls' (Expr w PBool)
pnotNode term = undefined

pnot :: Term '[] [Expr Free (PBool #-> PBool)]
pnot = undefined
-}
