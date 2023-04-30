{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Internal.Utilities (
  insertPermutation,
  invPermutation,
  cmpListEqMod1,
  bringPermutation,
  transListEqMod1,
  idxPermutation,
  transPermutation,
  SimpleLanguage,
  InstSimpleLanguage,
  L (..),
  InterpretSomeIn (..),
  translateSimpleLanguage,
  extractSimpleLanguage,
  EmbedTwo,
  interpretTerm',
  interpretSome,
) where

import Data.Kind (Type)
import Data.SOP (K, NP)
import Data.Type.Equality ((:~:) (Refl))
import Plutarch.Core

insertPermutation :: ListEqMod1 xs xs' y -> Permutation xs ys -> Permutation xs' (y : ys)
insertPermutation ListEqMod1N perm = PermutationS ListEqMod1N perm
insertPermutation (ListEqMod1S idx) (PermutationS idx' rest) = PermutationS (ListEqMod1S idx') $ insertPermutation idx rest

invPermutation :: Permutation xs ys -> Permutation ys xs
invPermutation PermutationN = PermutationN
invPermutation (PermutationS idx rest) = insertPermutation idx $ invPermutation rest

cmpListEqMod1 ::
  ListEqMod1 new' new x ->
  ListEqMod1 tail new y ->
  ( forall tail'.
    Either
      (x :~: y, new' :~: tail)
      (ListEqMod1 tail' tail x, ListEqMod1 tail' new' y) ->
    r
  ) ->
  r
cmpListEqMod1 ListEqMod1N ListEqMod1N k = k (Left (Refl, Refl))
cmpListEqMod1 ListEqMod1N (ListEqMod1S idx) k = k (Right (ListEqMod1N, idx))
cmpListEqMod1 (ListEqMod1S idx) ListEqMod1N k = k (Right (idx, ListEqMod1N))
cmpListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') k = cmpListEqMod1 idx idx' \case
  Left (x, Refl) -> k (Left (x, Refl))
  Right (idx2, idx'2) -> k (Right (ListEqMod1S idx2, ListEqMod1S idx'2))

bringPermutation :: ListEqMod1 new' new x -> Permutation old new -> Permutation old (x : new')
bringPermutation ListEqMod1N x = x
bringPermutation idx (PermutationS idx' tail) =
  cmpListEqMod1 idx idx' \case
    Left (Refl, Refl) -> PermutationS ListEqMod1N tail
    Right (idx2, idx'2) ->
      PermutationS (ListEqMod1S idx'2) $
        bringPermutation idx2 $
          tail

transListEqMod1 ::
  ListEqMod1 xs ys x ->
  ListEqMod1 ys zs y ->
  (forall xs'. ListEqMod1 xs' zs x -> ListEqMod1 xs xs' y -> b) ->
  b
transListEqMod1 idx ListEqMod1N k = k (ListEqMod1S idx) ListEqMod1N
transListEqMod1 ListEqMod1N (ListEqMod1S idx) k = k ListEqMod1N idx
transListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') k =
  transListEqMod1 idx idx' \idx'' idx''' -> k (ListEqMod1S idx'') (ListEqMod1S idx''')

idxPermutation ::
  ListEqMod1 xs' xs x ->
  Permutation xs ys ->
  (forall ys'. ListEqMod1 ys' ys x -> Permutation xs' ys' -> b) ->
  b
idxPermutation ListEqMod1N (PermutationS idx rest) k = k idx rest
idxPermutation (ListEqMod1S idx) (PermutationS idx' rest) k =
  idxPermutation idx rest \idx'' rest' -> transListEqMod1 idx'' idx' \idx''' idx'''' ->
    k idx''' (PermutationS idx'''' rest')

transPermutation :: Permutation xs ys -> Permutation ys zs -> Permutation xs zs
transPermutation PermutationN perm = case perm of
  PermutationN -> PermutationN
transPermutation (PermutationS idx rest) perm = idxPermutation idx perm \idx' perm' -> PermutationS idx' (transPermutation rest perm')

data SameShapeAs xs ys where
  SameShapeAsN :: SameShapeAs '[] '[]
  SameShapeAsS :: SameShapeAs xs ys -> SameShapeAs (x : xs) (y : ys)

extractShape :: InterpretAllIn xs ys zs ws -> SameShapeAs zs ws
extractShape InterpretAllInN = SameShapeAsN
extractShape (InterpretAllInS _ rest) = SameShapeAsS (extractShape rest)

transInterpretIn :: SameShapeAs ys zs -> InterpretIn xs ys x y -> InterpretIn ys zs y z -> InterpretIn xs zs x z
transInterpretIn =
  \shape xy yz -> InterpretIn \subls term ->
    helper shape subls \subls0 subls1 ->
      runInterpreter yz subls1 $ runInterpreter xy subls0 term
  where
    helper ::
      SameShapeAs ys zs ->
      SubLS ls0 ls2 xs zs (Just '(x, z)) ->
      (forall ls1. SubLS ls0 ls1 xs ys (Just '(x, y)) -> SubLS ls1 ls2 ys zs (Just '(y, z)) -> b) ->
      b
    helper (SameShapeAsS shape) (SubLSSkip rest) k = helper shape rest \subls0 subls1 -> k (SubLSSkip subls0) (SubLSSkip subls1)
    helper (SameShapeAsS shape) (SubLSSwap rest) k = helper shape rest \subls0 subls1 -> k (SubLSSwap subls0) (SubLSSwap subls1)
    helper shape'@(SameShapeAsS shape) subls@(SubLSExcept rest) k = helper' shape rest \subls0 subls1 -> k (undefined subls0) undefined
    helper' ::
      SameShapeAs ys zs ->
      SubLS ls0 ls2 xs zs Nothing ->
      (forall ls1. SubLS ls0 ls1 xs ys Nothing -> SubLS ls1 ls2 ys zs Nothing -> b) ->
      b
    helper' SameShapeAsN SubLSBase k = k SubLSBase SubLSBase
    helper' (SameShapeAsS shape) (SubLSSkip rest) k = helper' shape rest \subls0 subls1 -> k (SubLSSkip subls0) (SubLSSkip subls1)
    helper' (SameShapeAsS shape) (SubLSSwap rest) k = helper' shape rest \subls0 subls1 -> k (SubLSSwap subls0) (SubLSSwap subls1)

transInterpret :: Interpret xs ys -> Interpret ys zs -> Interpret xs zs
transInterpret = \(Interpret xys) (Interpret yzs) -> Interpret $ go xys yzs
  where
    go :: InterpretAllIn xs ys xs ys -> InterpretAllIn ys zs ys zs -> InterpretAllIn xs zs xs zs
    go InterpretAllInN yzs = case yzs of
      InterpretAllInN -> InterpretAllInN
    go (InterpretAllInS xy xys) (InterpretAllInS yz yzs) = InterpretAllInS (transInterpretIn (SameShapeAsS $ extractShape yzs) xy yz) undefined

swapInterpretPermutation :: Permutation xs ys -> Interpret ys zs -> (forall ws. Interpret xs ws -> Permutation ws zs -> r) -> r
swapInterpretPermutation _ _ _ = undefined

interpretTerm' :: Interpret ls ls' -> Term' l ls tag -> Term' l ls' tag
interpretTerm' intrs' (Term' node intrs perm) =
  swapInterpretPermutation
    perm
    intrs'
    \intrs'' perm' -> Term' node (transInterpret intrs intrs'') perm'

interpret1 :: InterpretIn (l : ls) (l' : ls) l l' -> Interpret (l : ls) (l' : ls)
interpret1 = undefined

data InterpretSomeIn ls0 ls1 ls2 ls3 where
  InterpretSomeInN :: Catenation ls0' ls2 ls0 -> Catenation ls1' ls2 ls1 -> InterpretSomeIn ls0 ls1 ls2 ls2
  InterpretSomeInS :: InterpretIn ls0 ls1 l l' -> InterpretSomeIn ls0 ls1 ls2 ls3 -> InterpretSomeIn ls0 ls1 (l : ls2) (l' : ls3)

interpretSome :: InterpretSomeIn ls ls' ls ls' -> Interpret ls ls'
interpretSome = undefined

data Catenation xs ys zs where
  CatenationN :: Catenation '[] ys ys
  CatenationS :: Catenation xs ys zs -> Catenation (x : xs) ys (x : zs)

data Contains subnodes ls where
  ContainsN :: Contains '[] '[]
  ContainsS :: Catenation ls ls' ls'' -> Term ls tag -> Contains subnodes ls' -> Contains (tag : subnodes) ls''

type SimpleLanguage = [Tag] -> Tag -> Type
data InstSimpleLanguage :: SimpleLanguage -> Language
data instance L (InstSimpleLanguage l) ls tag where
  SimpleLanguageNode :: Contains subnodes ls -> l subnodes tag -> L (InstSimpleLanguage l) ls tag
  ContractSimpleLanguage :: Term (InstSimpleLanguage l : InstSimpleLanguage l : ls) tag -> L (InstSimpleLanguage l) ls tag
  ExpandSimpleLanguage :: Term ls tag -> L (InstSimpleLanguage l) ls tag

extractSimpleLanguage ::
  (l subnodes tag -> NP (K a) subnodes -> a) ->
  Term '[InstSimpleLanguage l] tag ->
  a
extractSimpleLanguage = undefined

translateSimpleLanguage ::
  (forall ls' tag' subnodes. NP (K a) subnodes -> Contains subnodes ls' -> l subnodes tag' -> (Term' l' ls' tag', a)) ->
  Term (InstSimpleLanguage l : ls) tag ->
  (Term (l' : ls) tag, Maybe a)
translateSimpleLanguage _ _ = undefined

data EmbedTwo lx ly :: Language
data instance L (EmbedTwo lx ly) ls tag where
  EmbedTwo :: Term (lx : ly : ls) tag -> L (EmbedTwo lx ly) ls tag

---- examples

type PType = Type

data Expr :: PType -> Tag

data BoolsTag :: SimpleLanguage where
  Xor :: BoolsTag '[Expr Bool, Expr Bool] (Expr Bool)
  Not :: BoolsTag '[Expr Bool] (Expr Bool)
  BoolLit :: Bool -> BoolsTag '[] (Expr Bool)
type Bools = InstSimpleLanguage BoolsTag

class CCatenation xs ys zs | xs ys -> zs where
  ccatenation :: Catenation xs ys zs

instance CCatenation '[] ys ys where
  ccatenation = CatenationN

instance CCatenation xs ys zs => CCatenation (x : xs) ys (x : zs) where
  ccatenation = CatenationS ccatenation

type family Append (xs :: [a]) (ys :: [a]) :: [a] where
  Append '[] ys = ys
  Append (x : xs) ys = x : Append xs ys

data SList :: [a] -> Type where
  SNil :: SList '[]
  SCons :: SList xs -> SList (x : xs)

catenationInv :: SList xs -> Catenation xs '[] xs
catenationInv SNil = CatenationN
catenationInv (SCons xs) = CatenationS (catenationInv xs)

termToSList :: Term ls tag -> SList ls
termToSList = undefined

idPermutation :: SList xs -> Permutation xs xs
idPermutation SNil = PermutationN
idPermutation (SCons xs) = PermutationS ListEqMod1N (idPermutation xs)

idInterpretation :: SList xs -> Interpret xs xs
idInterpretation = Interpret . f
  where
    f :: SList ys -> InterpretAllIn xs xs ys ys
    f SNil = InterpretAllInN
    f (SCons xs) = InterpretAllInS g $ f xs
    g :: InterpretIn ls ls l l
    g = InterpretIn \subls x -> case i subls of Refl -> x
    h ::
      SubLS ls0 ls1 ls ls except ->
      Term' l ls0 tag ->
      Term' l ls1 tag
    h subls x = case i subls of Refl -> x
    i :: SubLS xs ys zs zs except -> xs :~: ys
    i SubLSBase = Refl
    i (SubLSSkip rest) = case i rest of Refl -> Refl
    i (SubLSSwap rest) = case i rest of Refl -> Refl
    i (SubLSExcept rest) = case i rest of Refl -> Refl

pnot :: Term ls0 (Expr Bool) -> Term (Bools : ls0) (Expr Bool)
pnot x = Term (Term' (SimpleLanguageNode (ContainsS (catenationInv slist) x ContainsN) Not) (idInterpretation slist) (idPermutation slist)) ListEqMod1N
  where
    slist = termToSList x

data ElemOf :: [a] -> a -> Type where
  ElemOfN :: ElemOf (x : xs) x
  ElemOfS :: ElemOf xs x -> ElemOf (y : xs) x

newtype Contractible :: Language -> Type where
  Contractible :: (forall ls tag. Term (l : l : ls) tag -> L l ls tag) -> Contractible l

runContractible :: Contractible l -> Term (l : l : ls) tag -> L l ls tag
runContractible (Contractible f) = f

data MultiContractible :: [Language] -> [Language] -> Type where
  MultiContractibleBase :: MultiContractible '[] '[]
  MultiContractibleContract :: Contractible l -> ElemOf ls l -> MultiContractible ls ls' -> MultiContractible (l : ls) ls'
  MultiContractibleSkip :: MultiContractible ls ls' -> MultiContractible (l : ls) (l : ls')

contract :: Contractible l -> Term (l : l : ls) tag -> Term (l : ls) tag
contract c term = Term (Term' node intrs perm) ListEqMod1N
  where
    node = runContractible c term
    intrs = idInterpretation slist
    perm = idPermutation slist
    SCons (SCons slist) = termToSList term

bringTerm :: ListEqMod1 ls' ls l -> Term ls tag -> Term (l : ls') tag
bringTerm = undefined

unbringTerm :: ListEqMod1 ls' ls l -> Term (l : ls') tag -> Term ls tag
unbringTerm = undefined

contractThere' :: ListEqMod1 ls' ls l -> Contractible l -> Term (l : ls) tag -> Term (l : ls') tag
contractThere' idx c term = contract c $ bringTerm (ListEqMod1S idx) term

elemOf_to_listEqMod1 :: ElemOf xs x -> (forall xs'. ListEqMod1 xs' xs x -> r) -> r
elemOf_to_listEqMod1 ElemOfN k = k ListEqMod1N
elemOf_to_listEqMod1 (ElemOfS rest) k = elemOf_to_listEqMod1 rest (k . ListEqMod1S)

listEqMod1_to_elemOf :: ListEqMod1 xs' xs x -> ElemOf xs x
listEqMod1_to_elemOf ListEqMod1N = ElemOfN
listEqMod1_to_elemOf (ListEqMod1S x) = ElemOfS $ listEqMod1_to_elemOf x

contractThere :: ElemOf ls l -> Contractible l -> Term (l : ls) tag -> Term ls tag
contractThere idx c term = elemOf_to_listEqMod1 idx \idx' -> unbringTerm idx' $ contractThere' idx' c term

data ReverseCatenation :: [a] -> [a] -> [a] -> Type where
  ReverseCatenationN :: ReverseCatenation '[] ys ys
  ReverseCatenationS :: ReverseCatenation xs (x : ys) zs -> ReverseCatenation (x : xs) ys zs

{-
catenationToNilIsInput :: Catenation xs '[] ys -> xs :~: ys
catenationToNilIsInput CatenationN = Refl
catenationToNilIsInput (CatenationS rest) = case catenationToNilIsInput rest of Refl -> Refl
-}

reverseCatenationFunctional :: ReverseCatenation xs suffix ys -> ReverseCatenation xs suffix zs -> ys :~: zs
reverseCatenationFunctional ReverseCatenationN ReverseCatenationN = Refl
reverseCatenationFunctional (ReverseCatenationS ys) (ReverseCatenationS zs) =
  case reverseCatenationFunctional ys zs of Refl -> Refl

multicontract' ::
  ReverseCatenation prefix ls0 ls0' ->
  ReverseCatenation prefix ls1 ls1' ->
  MultiContractible ls0 ls1 ->
  Term ls0' tag ->
  Term ls1' tag
multicontract' cnx cny MultiContractibleBase term =
  case reverseCatenationFunctional cnx cny of Refl -> term
multicontract' cnx cny (MultiContractibleSkip rest) term =
  multicontract' (ReverseCatenationS cnx) (ReverseCatenationS cny) rest term
multicontract' cnx cny (MultiContractibleContract c idx rest) term = finalterm
  where
    shifted = bringTerm (util cnx ListEqMod1N) term
    contracted = elemOf_to_listEqMod1 idx \idx' -> contractThere (listEqMod1_to_elemOf $ util cnx (ListEqMod1S idx')) c shifted
    finalterm = multicontract' (_ cnx) cny rest contracted
    util :: ReverseCatenation xs ys zs -> ListEqMod1 ys' ys x -> ListEqMod1 zs' zs x
    util = undefined

multicontract :: MultiContractible ls ls' -> Term ls tag -> Term ls' tag
multicontract = multicontract' ReverseCatenationN ReverseCatenationN

-- contractThere _ c $ multicontract' _ _ rest term
-- multicontract' _ _ (MultiContractibleSkip rest) term = _

-- pxor' :: Term ls0 (Expr Bool) -> Term ls1 (Expr Bool) -> Term (Bools : Append ls0 ls1) (Expr Bool)
-- pxor' x y = Term (Term' (SimpleLanguageNode _ Xor) _ _) ListEqMod1N
