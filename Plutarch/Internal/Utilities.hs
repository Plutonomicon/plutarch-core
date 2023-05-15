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
  translateSimpleLanguage,
  extractSimpleLanguage,
  EmbedTwo,
  interpretTerm',
  multicontract,
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

data SameShapeAs :: [a] -> [a] -> Type where
  SameShapeAsN :: SameShapeAs '[] '[]
  SameShapeAsS :: SameShapeAs xs ys -> SameShapeAs (x : xs) (y : ys)

extractShape :: InterpretAllIn xs ys zs ws idx -> SameShapeAs zs ws
extractShape InterpretAllInN = SameShapeAsN
extractShape (InterpretAllInS _ _ _ rest) = SameShapeAsS (extractShape rest)

{-
-- Given SubLS xs zs xs' zs' (Just '(x, z)),
-- we know that xs zs share a common _suffix_,
-- while the distinct prefixes of equal length are xs' and zs',
-- module x in xs' and z in zs', at the same index.
-- If there is another list ys' of the same length
-- as xs' and zs', then we can construct ys such that
-- SubLS xs ys xs' ys' (Just '(x, y)) and SubLS ys zs ys' zs' (Just '(y, z)),
-- i.e., xs and ys share the same suffix (obviously),
-- but the prefix for ys is ys' modulo y (at the same index as x and y)
-- instead of xs' modulo x. The same applies for the case of ys and zs.
jxjuu ::
  SubLS ls0 ls2 xs zs (Just '(x, z)) ->
  (forall ls1. SubLS ls0 ls1 xs ys (Just '(x, y)) -> SubLS ls1 ls2 ys zs (Just '(y, z)) -> b) ->
  b
jxjuu (SameShapeAsS shape) (SubLSSkip rest) k = jxjuu shape rest \subls0 subls1 -> k (SubLSSkip subls0) (SubLSSkip subls1)
jxjuu (SameShapeAsS shape) (SubLSSwap rest) k = jxjuu shape rest \subls0 subls1 -> k (SubLSSwap subls0) (SubLSSwap subls1)
helper (SameShapeAsJust shape) (SubLSExcept rest) k = helper' shape rest \subls0 subls1 -> k (SubLSExcept subls0) (SubLSExcept subls1)
-}

transInterpretIn ::
  SameShapeAs ys zs -> InterpretIn xs ys x y -> InterpretIn ys zs y z -> InterpretIn xs zs x z
transInterpretIn =
  \shape xy yz -> InterpretIn \subls term ->
    helper shape subls \subls0 subls1 ->
      runInterpreter yz subls1 $ runInterpreter xy subls0 term
  where
    helper ::
      SameShapeAs ys zs ->
      SubLS ls0 ls2 xs zs ->
      (forall ls1. SubLS ls0 ls1 xs ys -> SubLS ls1 ls2 ys zs -> b) ->
      b
    helper (SameShapeAsS shape) (SubLSSkip rest) k = helper shape rest \subls0 subls1 -> k (SubLSSkip subls0) (SubLSSkip subls1)
    helper (SameShapeAsS shape) (SubLSSwap rest) k = helper shape rest \subls0 subls1 -> k (SubLSSwap subls0) (SubLSSwap subls1)
    helper SameShapeAsN SubLSBase k = k SubLSBase SubLSBase

data SameShapeWithSuffix :: [a] -> [a] -> [a] -> [a] -> Type where
  SameShapeWithSuffixN :: SameShapeAs xs ys -> SameShapeWithSuffix xs ys xs ys
  SameShapeWithSuffixS :: SameShapeWithSuffix xs ys (z : zs) (w : ws) -> SameShapeWithSuffix xs ys zs ws

{-
sameShapeUnJust :: SameShapeAs xs ys m -> SameShapeAs xs ys Nothing
sameShapeUnJust SameShapeAsN = SameShapeAsN
sameShapeUnJust (SameShapeAsS x) = SameShapeAsS $ sameShapeUnJust x
sameShapeUnJust (SameShapeAsJust x) = SameShapeAsS x

data IndexTwo :: [a] -> [a] -> a -> a -> Type where
  IndexTwoN :: IndexTwo (x : xs) (y : ys) x y
  IndexTwoS :: IndexTwo xs ys x y -> IndexTwo (z : xs) (w : ys) x y
-}

sameShapeFromSuffix :: SameShapeWithSuffix xs ys zs ws -> SameShapeAs xs ys
sameShapeFromSuffix (SameShapeWithSuffixN shape) = shape
sameShapeFromSuffix (SameShapeWithSuffixS shape) = sameShapeFromSuffix shape

removeFromSameShapeAs :: ListEqMod1Idx xs' xs idx -> ListEqMod1Idx ys' ys idx -> SameShapeAs xs ys -> SameShapeAs xs' ys'
removeFromSameShapeAs ListEqMod1IdxN ListEqMod1IdxN (SameShapeAsS s) = s
removeFromSameShapeAs (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (SameShapeAsS s) =
  SameShapeAsS $ removeFromSameShapeAs idx idx' s

listEqMod1IdxInjective :: ListEqMod1Idx xs' xs idx -> ListEqMod1Idx ys' xs idx -> xs' :~: ys'
listEqMod1IdxInjective ListEqMod1IdxN ListEqMod1IdxN = Refl
listEqMod1IdxInjective (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') = case listEqMod1IdxInjective idx idx' of
  Refl -> Refl

transInterpret :: Interpret xs ys -> Interpret ys zs -> Interpret xs zs
transInterpret = \(Interpret xys) (Interpret yzs) -> Interpret $ go (SameShapeWithSuffixN $ extractShape yzs) xys yzs
  where
    go ::
      SameShapeWithSuffix ys zs ys' zs' ->
      InterpretAllIn xs ys xs' ys' idx ->
      InterpretAllIn ys zs ys' zs' idx ->
      InterpretAllIn xs zs xs' zs' idx
    go _ InterpretAllInN InterpretAllInN = InterpretAllInN
    go shape (InterpretAllInS lidx lidx' xy xys) (InterpretAllInS ridx ridx' yz yzs) =
      case listEqMod1IdxInjective lidx' ridx of
        Refl ->
          InterpretAllInS
            lidx
            ridx'
            (transInterpretIn (removeFromSameShapeAs lidx' ridx' $ sameShapeFromSuffix shape) xy yz)
            $ go (SameShapeWithSuffixS shape) xys yzs

swapInterpretPermutation ::
  Permutation xs ys ->
  Interpret ys zs ->
  (forall ws. Interpret xs ws -> Permutation ws zs -> r) ->
  r
swapInterpretPermutation _ _ _ = undefined

interpretTerm' :: Interpret ls ls' -> Term' l ls tag -> Term' l ls' tag
interpretTerm' intrs' (Term' node intrs perm) =
  swapInterpretPermutation
    perm
    intrs'
    \intrs'' perm' -> Term' node (transInterpret intrs intrs'') perm'

{-
interpretInOther :: InterpretIn xs ys x y -> InterpretIn zs ws x y
interpretInOther = undefined

extendInterpretOne :: Interpret '[x] '[y] -> Interpret (x : xs) (y : ys)
extendInterpretOne = undefined

interpretTwo :: forall x y z. InterpretIn '[x, y] '[x, z] y z -> Interpret '[x, y] '[x, z]
interpretTwo gi@(InterpretIn g) = Interpret $ InterpretAllInS (InterpretIn f) $ InterpretAllInS (InterpretIn g) InterpretAllInN where
  f :: SubLS ls0 ls1 '[x, y] '[x, z] (Just '(x, x)) -> Term' x ls0 tag -> Term' x ls1 tag
  f (SubLSExcept (SubLSSkip SubLSBase)) term = term
  f (SubLSExcept (SubLSSwap SubLSBase)) term = interpretTerm' (extendInterpretOne $ Interpret $ InterpretAllInS (interpretInOther gi) InterpretAllInN) term

data SamePrefix :: [a] -> [a] -> [a] -> [a] -> Type where
  SamePrefixN :: SamePrefix xs ys xs ys
  SamePrefixS :: SamePrefix xs ys zs ws -> SamePrefix (x : xs) (x : ys) zs ws

extendInterpretAllIn ::
  SamePrefix xs ys zs ws ->
  InterpretAllIn xs ys zs ws ->
  InterpretAllIn xs ys xs ys
extendInterpretAllIn SamePrefixN intrs = intrs
-}
{-
extendInterpretAllIn (SamePrefixS SamePrefixN) intrs = InterpretAllInS (InterpretIn intr) intrs where
  intr :: SubLS ls0 ls1 (x : zs) (x : ws) (Just '(x, x)) -> Term' x ls0 tag -> Term' x ls1 tag
  intr (SubLSExcept SubLSBase) (Term' node intrs perm) = Term' node intrs perm
  intr (SubLSExcept (SubLSSkip SubLSBase)) (Term' node intrs perm) = Term' node intrs perm
  intr (SubLSExcept (SubLSSwap SubLSBase)) t@(Term' node intrs perm) = _ -- Term' node _ _
-}

data Catenation xs ys zs where
  CatenationN :: Catenation '[] ys ys
  CatenationS :: Catenation xs ys zs -> Catenation (x : xs) ys (x : zs)

data Contains subnodes ls

-- ContainsN :: Contains '[] '[]
-- ContainsS :: Catenation ls ls' ls'' -> Term ls tag -> Contains subnodes ls' -> Contains (tag : subnodes) ls''

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

{-
type PType = Type

data Expr :: PType -> Tag

data BoolsTag :: SimpleLanguage where
  And :: BoolsTag '[Expr Bool, Expr Bool] (Expr Bool)
  Not :: BoolsTag '[Expr Bool] (Expr Bool)
  BoolLit :: Bool -> BoolsTag '[] (Expr Bool)
type Bools = InstSimpleLanguage BoolsTag
-}

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

termToSList :: Term ls tag -> SList ls
termToSList (Term (Term' _ _ perm) idx) = g idx $ f $ invPermutation perm
  where
    f :: Permutation xs ys -> SList xs
    f PermutationN = SNil
    f (PermutationS _ rest) = SCons $ f rest
    g :: ListEqMod1 xs ys x -> SList xs -> SList ys
    g ListEqMod1N s = SCons s
    g (ListEqMod1S x) (SCons s) = SCons $ g x s

idPermutation :: SList xs -> Permutation xs xs
idPermutation SNil = PermutationN
idPermutation (SCons xs) = PermutationS ListEqMod1N (idPermutation xs)

data IndexInto :: [a] -> Nat -> Type where
  IndexIntoN :: IndexInto (x : xs) N
  IndexIntoS :: IndexInto xs idx -> IndexInto (x : xs) (S idx)

data SuffixOf :: [a] -> [a] -> Nat -> Type where
  SuffixOfN :: SuffixOf xs xs N
  SuffixOfS :: SuffixOf xs (y : ys) idx -> SuffixOf xs ys (S idx)

data Add :: Nat -> Nat -> Nat -> Type where
  AddN :: Add N n n
  AddS :: Add n m o -> Add (S n) m (S o)

data SNat :: Nat -> Type where
  SN :: SNat N
  SS :: SNat n -> SNat (S n)

add_n_N_n :: SNat n -> Add n N n
add_n_N_n SN = AddN
add_n_N_n (SS n) = AddS $ add_n_N_n n

addInjective :: Add n m o -> Add n m o' -> o :~: o'
addInjective AddN AddN = Refl
addInjective (AddS x) (AddS y) = case addInjective x y of
  Refl -> Refl

undoAddSFlipped :: Add n (S m) o -> (forall o'. o :~: S o' -> Add n m o' -> r) -> r
undoAddSFlipped AddN k = k Refl AddN
undoAddSFlipped (AddS add) k = undoAddSFlipped add \Refl add' -> k Refl (AddS add')

addSFlipped' :: Add n m o -> Add n' m m' -> Add n' o o' -> Add n m' o'
addSFlipped' AddN x y = case addInjective x y of Refl -> AddN
addSFlipped' (AddS add) x y = undoAddSFlipped y \Refl y' -> AddS $ addSFlipped' add x y'

addSFlipped :: Add n m o -> Add n (S m) (S o)
addSFlipped a = addSFlipped' a (AddS AddN) (AddS AddN)

suffixOf_to_IndexInto' :: IndexInto ys idx -> SuffixOf xs ys idx' -> Add idx' idx idx'' -> IndexInto xs idx''
suffixOf_to_IndexInto' idx SuffixOfN AddN = idx
suffixOf_to_IndexInto' idx (SuffixOfS suffix) (AddS add) = suffixOf_to_IndexInto' (IndexIntoS idx) suffix (addSFlipped add)

-- Logically equal to `(-) 1`
suffixOf_to_IndexInto :: SuffixOf xs ys (S idx) -> IndexInto xs idx
suffixOf_to_IndexInto (SuffixOfS suffix) = suffixOf_to_IndexInto' IndexIntoN suffix (add_n_N_n $ suffixOf_to_SNat suffix)

suffixOf_to_SNat :: SuffixOf xs ys idx -> SNat idx
suffixOf_to_SNat SuffixOfN = SN
suffixOf_to_SNat (SuffixOfS x) = SS (suffixOf_to_SNat x)

indexInto_to_ListEqMod1Idx :: IndexInto xs idx -> (forall xs'. ListEqMod1Idx xs' xs idx -> r) -> r
indexInto_to_ListEqMod1Idx IndexIntoN k = k ListEqMod1IdxN
indexInto_to_ListEqMod1Idx (IndexIntoS idx) k = indexInto_to_ListEqMod1Idx idx (k . ListEqMod1IdxS)

suffixOf_to_ListEqMod1Idx :: SuffixOf xs ys (S idx) -> (forall xs'. ListEqMod1Idx xs' xs idx -> r) -> r
suffixOf_to_ListEqMod1Idx suffix k = indexInto_to_ListEqMod1Idx (suffixOf_to_IndexInto suffix) k

idInterpretation :: SList xs -> Interpret xs xs
idInterpretation = Interpret . f SuffixOfN
  where
    f :: SuffixOf xs ys idx -> SList ys -> InterpretAllIn xs xs ys ys idx
    f _ SNil = InterpretAllInN
    f suffix (SCons xs) =
      suffixOf_to_ListEqMod1Idx (SuffixOfS suffix) \idx ->
        InterpretAllInS idx idx g $ f (SuffixOfS suffix) xs
    g :: InterpretIn ls ls l l
    g = InterpretIn \subls x -> case i subls of Refl -> x
    i :: SubLS xs ys zs zs -> xs :~: ys
    i SubLSBase = Refl
    i (SubLSSkip rest) = case i rest of Refl -> Refl
    i (SubLSSwap rest) = case i rest of Refl -> Refl

{-
pnot :: Term ls0 (Expr Bool) -> Term (Bools : ls0) (Expr Bool)
pnot x = Term (Term' (SimpleLanguageNode (ContainsS (catenationInv slist) x ContainsN) Not) (idInterpretation slist) (idPermutation slist)) ListEqMod1N
  where
    slist = termToSList x
-}

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
multicontract' cnx _cny (MultiContractibleContract c idx rest) term = finalterm
  where
    shifted = bringTerm (util cnx ListEqMod1N) term
    contracted = elemOf_to_listEqMod1 idx \idx' -> contractThere (listEqMod1_to_elemOf $ util cnx (ListEqMod1S idx')) c shifted
    finalterm = multicontract' undefined undefined rest contracted
    util :: ReverseCatenation xs ys zs -> ListEqMod1 ys' ys x -> ListEqMod1 zs' zs x
    util = undefined

multicontract :: MultiContractible ls ls' -> Term ls tag -> Term ls' tag
multicontract = multicontract' ReverseCatenationN ReverseCatenationN

-- contractThere _ c $ multicontract' _ _ rest term
-- multicontract' _ _ (MultiContractibleSkip rest) term = _

-- pand' :: Term ls0 (Expr Bool) -> Term ls1 (Expr Bool) -> Term (Bools : Append ls0 ls1) (Expr Bool)
-- pand' x y = Term (Term' (SimpleLanguageNode _ And) _ _) ListEqMod1N
