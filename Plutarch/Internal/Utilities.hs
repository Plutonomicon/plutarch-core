{-# LANGUAGE UndecidableInstances #-}

module Plutarch.Internal.Utilities (
  bringTerm,
  ElemOf(..),
  idInterpretation,
  idPermutation,
  Contractible,
  interpretOne,
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
  extractSimpleLanguage,
  interpretTerm',
  interpretTerm,
  permuteTerm,
  permuteTerm',
  multicontract,
  Catenation(..),
) where

import Data.Kind (Type)
import Data.SOP (NP ((:*), Nil))
import Data.Type.Equality ((:~:) (Refl))
import Plutarch.Core

insertPermutation :: ListEqMod1 xs xs' y -> Permutation xs ys -> Permutation xs' (y : ys)
insertPermutation ListEqMod1N perm = PermutationS ListEqMod1N perm
insertPermutation (ListEqMod1S idx) (PermutationS idx' rest) = PermutationS (ListEqMod1S idx') $ insertPermutation idx rest

invPermutation :: Permutation xs ys -> Permutation ys xs
invPermutation PermutationN = PermutationN
invPermutation (PermutationS idx rest) = insertPermutation idx $ invPermutation rest

-- Return the difference
cmpListEqMod1 ::
  ListEqMod1 new' new x ->
  ListEqMod1 tail new y ->
  ( forall tail'.
    Either
      ('(x, new') :~: '(y, tail))
      (ListEqMod1 tail' tail x, ListEqMod1 tail' new' y) ->
    r
  ) ->
  r
cmpListEqMod1 ListEqMod1N ListEqMod1N k = k (Left Refl)
cmpListEqMod1 ListEqMod1N (ListEqMod1S idx) k = k (Right (ListEqMod1N, idx))
cmpListEqMod1 (ListEqMod1S idx) ListEqMod1N k = k (Right (idx, ListEqMod1N))
cmpListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') k = cmpListEqMod1 idx idx' \case
  Left Refl -> k (Left Refl)
  Right (idx2, idx'2) -> k (Right (ListEqMod1S idx2, ListEqMod1S idx'2))

cmpListEqMod1Idx ::
  ListEqMod1Idx ys xs x idx ->
  ListEqMod1Idx zs xs y idx' ->
  ( forall ws idx''.
    Either
      -- idx = idx'
      ('(x, ys, idx) :~: '(y, zs, idx'))
      (Either
        -- idx < idx'
        (S idx'' :~: idx', ListEqMod1Idx ws zs x idx, ListEqMod1Idx ws ys y idx'')
        --- idx > idx'
        (S idx'' :~: idx, ListEqMod1Idx ws zs x idx'', ListEqMod1Idx ws ys y idx')
      ) ->
    r
  ) ->
  r
cmpListEqMod1Idx _ _ _ = undefined
cmpListEqMod1Idx ListEqMod1IdxN ListEqMod1IdxN k = k (Left Refl)
cmpListEqMod1Idx ListEqMod1IdxN (ListEqMod1IdxS idx) k = k (Right $ Left (Refl, ListEqMod1IdxN, idx))
cmpListEqMod1Idx (ListEqMod1IdxS idx) ListEqMod1IdxN k = k (Right $ Right (Refl, idx, ListEqMod1IdxN))
cmpListEqMod1Idx (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') k = cmpListEqMod1Idx idx idx' \case
  Left Refl -> k (Left Refl)
  Right (Left (Refl, idx0, idx'0)) -> k (Right $ Left (Refl, ListEqMod1IdxS idx0, ListEqMod1IdxS idx'0))
  Right (Right (Refl, idx0, idx'0)) -> k (Right $ Right (Refl, ListEqMod1IdxS idx0, ListEqMod1IdxS idx'0))

bringPermutation :: ListEqMod1 new' new x -> Permutation old new -> Permutation old (x : new')
bringPermutation ListEqMod1N x = x
bringPermutation idx (PermutationS idx' tail) =
  cmpListEqMod1 idx idx' \case
    Left Refl -> PermutationS ListEqMod1N tail
    Right (idx2, idx'2) ->
      PermutationS (ListEqMod1S idx'2) $
        bringPermutation idx2 $
          tail

listEqMod1_to_Permutation ::
  SList xs' ->
  ListEqMod1 xs' xs x ->
  Permutation (x : xs') xs
listEqMod1_to_Permutation slist idx = PermutationS idx (idPermutation slist)

unbringPermutation :: ListEqMod1 new' new x -> Permutation old (x : new') -> Permutation old new
unbringPermutation idx perm =
  transPermutation perm
    $ listEqMod1_to_Permutation
      (case permutationToSList (invPermutation perm) of SCons slist -> slist)
      idx

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
transPermutation PermutationN PermutationN = PermutationN
transPermutation (PermutationS idx rest) perm =
  idxPermutation
    idx
    perm
    \idx' perm' -> PermutationS idx' (transPermutation rest perm')

interpret_to_LengthOfTwo :: InterpretAsc xs ys idx -> (forall n. LengthOfTwo xs ys n -> r) -> r
interpret_to_LengthOfTwo (InterpretAscN l) k = k l
interpret_to_LengthOfTwo (InterpretAscS _ _ _ rest) k = interpret_to_LengthOfTwo rest k

transInterpretIn ::
  LengthOfTwo ys zs len -> InterpretIn xs ys x y -> InterpretIn ys zs y z -> InterpretIn xs zs x z
transInterpretIn =
  \shape xy yz -> InterpretIn \subls term ->
    helper shape subls \subls0 subls1 ->
      runInterpreter yz subls1 $ runInterpreter xy subls0 term
  where
    helper ::
      LengthOfTwo ys zs len ->
      SubLS ls0 ls2 xs zs ->
      (forall ls1. SubLS ls0 ls1 xs ys -> SubLS ls1 ls2 ys zs -> b) ->
      b
    helper (LengthOfTwoS shape) (SubLSSkip rest) k = helper shape rest \subls0 subls1 -> k (SubLSSkip subls0) (SubLSSkip subls1)
    helper (LengthOfTwoS shape) (SubLSSwap rest) k = helper shape rest \subls0 subls1 -> k (SubLSSwap subls0) (SubLSSwap subls1)
    helper LengthOfTwoN SubLSBase k = k SubLSBase SubLSBase

removeFromLengthOfTwo ::
  ListEqMod1Idx xs' xs x idx ->
  ListEqMod1Idx ys' ys y idx ->
  LengthOfTwo xs ys len ->
  (forall len'. LengthOfTwo xs' ys' len' -> r) ->
  r
removeFromLengthOfTwo ListEqMod1IdxN ListEqMod1IdxN (LengthOfTwoS s) k = k s
removeFromLengthOfTwo (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (LengthOfTwoS s) k =
  removeFromLengthOfTwo idx idx' s (k . LengthOfTwoS)

listEqMod1IdxFunctional :: ListEqMod1Idx xs' xs x idx -> ListEqMod1Idx ys' xs y idx -> '(xs', x) :~: '(ys', y)
listEqMod1IdxFunctional ListEqMod1IdxN ListEqMod1IdxN = Refl
listEqMod1IdxFunctional (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') = case listEqMod1IdxFunctional idx idx' of
  Refl -> Refl

transLengthOfTwo :: LengthOfTwo xs ys n -> LengthOfTwo ys zs n' -> (LengthOfTwo xs zs n, n :~: n')
transLengthOfTwo LengthOfTwoN LengthOfTwoN = (LengthOfTwoN, Refl)
transLengthOfTwo (LengthOfTwoS l) (LengthOfTwoS l') =
  case transLengthOfTwo l l' of (length, Refl) -> (LengthOfTwoS length, Refl)

lengthOfTwo_add_ListEqMod1 :: ListEqMod1 ys ys' y -> LengthOfTwo xs ys len -> LengthOfTwo (x : xs) ys' (S len)
lengthOfTwo_add_ListEqMod1 ListEqMod1N l = LengthOfTwoS l
lengthOfTwo_add_ListEqMod1 (ListEqMod1S idx) (LengthOfTwoS l) = LengthOfTwoS $ lengthOfTwo_add_ListEqMod1 idx l

lengthOfTwo_add_ListEqMod1_both ::
  ListEqMod1 xs xs' x ->
  ListEqMod1 ys ys' y ->
  LengthOfTwo xs ys len ->
  LengthOfTwo xs' ys' (S len)
lengthOfTwo_add_ListEqMod1_both idx idx' len =
  case flipLengthOfTwo $ lengthOfTwo_add_ListEqMod1 idx' len of
    LengthOfTwoS len' -> flipLengthOfTwo $ lengthOfTwo_add_ListEqMod1 idx len'

permutation_to_LengthOfTwo :: Permutation xs ys -> (forall len. LengthOfTwo xs ys len -> r) -> r
permutation_to_LengthOfTwo PermutationN k = k LengthOfTwoN
permutation_to_LengthOfTwo (PermutationS idx perm) k =
  permutation_to_LengthOfTwo perm \len -> k (lengthOfTwo_add_ListEqMod1 idx len)

transInterpret :: Interpret xs ys -> Interpret ys zs -> Interpret xs zs
transInterpret = go
  where
    go ::
      InterpretAsc xs ys idx ->
      InterpretAsc ys zs idx ->
      InterpretAsc xs zs idx
    go (InterpretAscN length) (InterpretAscN length') = InterpretAscN $ fst $ transLengthOfTwo length length'
    go (InterpretAscN length) yzs = interpret_to_LengthOfTwo yzs \length' -> InterpretAscN $ fst $ transLengthOfTwo length length'
    go xys (InterpretAscN length) =
      interpret_to_LengthOfTwo xys \length' -> case transLengthOfTwo length' length of
        (length, Refl) -> InterpretAscN length
    go (InterpretAscS lidx lidx' xy xys) (InterpretAscS ridx ridx' yz yzs) =
      case listEqMod1IdxFunctional lidx' ridx of
        Refl ->
          InterpretAscS
            lidx
            ridx'
            (interpret_to_LengthOfTwo yzs \len' -> removeFromLengthOfTwo lidx' ridx' len' \shape -> transInterpretIn shape xy yz)
            $ go xys yzs

data InterpretIdxs :: [Language] -> [Language] -> [Nat] -> Type where
  InterpretIdxsN :: LengthOfTwo ls0 ls1 len -> InterpretIdxs ls0 ls1 '[]
  InterpretIdxsS ::
    ListEqMod1Idx ls0' ls0 l idx ->
    ListEqMod1Idx ls1' ls1 l' idx ->
    InterpretIn ls0' ls1' l l' ->
    InterpretIdxs ls0 ls1 idxs ->
    InterpretIdxs ls0 ls1 (idx : idxs)

-- FIXME: make total
partialMakeUnIdxed :: InterpretIdxs xs ys idxs -> Interpret xs ys
partialMakeUnIdxed = go SN
  where
    cmpIdx ::
      SNat idx ->
      ListEqMod1Idx xs' xs x idx' ->
      Maybe (idx :~: idx')
    cmpIdx SN ListEqMod1IdxN = Just Refl
    cmpIdx (SS idx) (ListEqMod1IdxS idx') =
      (\Refl -> Refl) <$> cmpIdx idx idx'
    cmpIdx SN (ListEqMod1IdxS _) = Nothing
    cmpIdx (SS _) ListEqMod1IdxN = Nothing
    cmpLengthOfTwo ::
      SNat idx ->
      LengthOfTwo xs ys len ->
      Maybe (idx :~: len)
    cmpLengthOfTwo SN LengthOfTwoN = Just Refl
    cmpLengthOfTwo (SS idx) (LengthOfTwoS len) =
      (\Refl -> Refl) <$> cmpLengthOfTwo idx len
    cmpLengthOfTwo SN (LengthOfTwoS _) = Nothing
    cmpLengthOfTwo (SS _) LengthOfTwoN = Nothing
    getIdx ::
      SNat idx ->
      InterpretIdxs xs ys idxs ->
      ( forall xs' ys' l l' idxs'.
        Either
          ( ListEqMod1Idx xs' xs l idx
          , ListEqMod1Idx ys' ys l' idx
          , -- , ListEqMod1 idxs' idxs idx
            InterpretIn xs' ys' l l'
          , InterpretIdxs xs ys idxs'
          )
          (LengthOfTwo xs ys idx) ->
        r
      ) ->
      r
    getIdx idx (InterpretIdxsN len) k =
      case cmpLengthOfTwo idx len of
        Just Refl -> k (Right len)
        Nothing -> k (error "should be unreachable, FIXME: partialMakeUnIdxed is partial")
    getIdx idx (InterpretIdxsS lidx ridx intr intrs) k =
      case cmpIdx idx lidx of
        Just Refl -> k (Left (lidx, ridx, intr, intrs))
        Nothing -> getIdx idx intrs k
    go :: SNat idx -> InterpretIdxs xs ys idxs -> InterpretAsc xs ys idx
    go idx intrs =
      getIdx idx intrs \case
        Left (lidx, ridx, intr, intrs') ->
          InterpretAscS lidx ridx intr $ go (SS idx) intrs'
        Right len -> InterpretAscN len

makeIdxed ::
  InterpretAsc ls ls' idx ->
  (forall idxs. InterpretIdxs ls ls' idxs -> r) ->
  r
makeIdxed (InterpretAscN len) k = k (InterpretIdxsN len)
makeIdxed (InterpretAscS idx idx' intr intrs) k =
  makeIdxed intrs \intrs' ->
    k (InterpretIdxsS idx idx' intr intrs')

insertSubLSSwap ::
  ListEqMod1Idx xs xs' x idx ->
  ListEqMod1Idx ys ys' y idx ->
  SubLS zs ws xs ys ->
  ( forall zs' ws' idx'.
    ListEqMod1Idx zs zs' x idx' ->
    ListEqMod1Idx ws ws' y idx' ->
    SubLS zs' ws' xs' ys' ->
    r
  ) ->
  r
insertSubLSSwap ListEqMod1IdxN ListEqMod1IdxN subls k =
  k ListEqMod1IdxN ListEqMod1IdxN (SubLSSwap subls)
insertSubLSSwap (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (SubLSSwap subls) k =
  insertSubLSSwap idx idx' subls \idx'' idx''' subls' ->
    k (ListEqMod1IdxS idx'') (ListEqMod1IdxS idx''') (SubLSSwap subls')
insertSubLSSwap (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (SubLSSkip subls) k =
  insertSubLSSwap idx idx' subls \idx'' idx''' subls' ->
    k idx'' idx''' (SubLSSkip subls')

insertSubLSSkip ::
  ListEqMod1Idx xs xs' x idx ->
  ListEqMod1Idx ys ys' y idx ->
  SubLS zs ws xs ys ->
  SubLS zs ws xs' ys'
insertSubLSSkip ListEqMod1IdxN ListEqMod1IdxN subls = SubLSSkip subls
insertSubLSSkip (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (SubLSSwap subls) =
  SubLSSwap $ insertSubLSSkip idx idx' subls
insertSubLSSkip (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (SubLSSkip subls) =
  SubLSSkip $ insertSubLSSkip idx idx' subls

fja' ::
  SList ls0 ->
  Permutation2 xs ys zs ws ->
  SubLS ls0 ls1 xs zs ->
  ( forall ls0' ls1'.
    SubLS ls0' ls1' ys ws ->
    Permutation2 ls0 ls0' ls1 ls1' ->
    r
  ) ->
  r
fja' ls0 perm2 SubLSBase k = case perm2 of
  Permutation2N -> k SubLSBase (idPermutation2 ls0)
fja' (SCons ls0) (Permutation2S idx idx' perm2) (SubLSSwap subls) k =
  fja' ls0 perm2 subls \subls' perm2' ->
    insertSubLSSwap idx idx' subls' \idx'' idx''' subls'' ->
      k subls'' (Permutation2S idx'' idx''' perm2')
fja' ls0 (Permutation2S idx idx' perm2) (SubLSSkip subls) k =
  fja' ls0 perm2 subls \subls' perm2' ->
    let subls'' = insertSubLSSkip idx idx' subls'
     in k subls'' perm2'

insertPermutation2 ::
  ListEqMod1Idx xs xs' x idx ->
  ListEqMod1Idx zs zs' z idx ->
  Permutation2 xs ys zs ws ->
  Permutation2 xs' (x : ys) zs' (z : ws)
insertPermutation2 ListEqMod1IdxN ListEqMod1IdxN perm =
  Permutation2S ListEqMod1IdxN ListEqMod1IdxN perm
insertPermutation2
  (ListEqMod1IdxS idx)
  (ListEqMod1IdxS idx')
  (Permutation2S idx'' idx''' perm2) =
    Permutation2S (ListEqMod1IdxS idx'') (ListEqMod1IdxS idx''') $
      insertPermutation2 idx idx' perm2

invPermutation2 ::
  Permutation2 xs ys zs ws ->
  Permutation2 ys xs ws zs
invPermutation2 Permutation2N = Permutation2N
invPermutation2 (Permutation2S idx idx' perm2) =
  insertPermutation2 idx idx' $ invPermutation2 perm2

permuteInterpretIn ::
  Permutation2 xs ys zs ws ->
  InterpretIn xs zs x y ->
  InterpretIn ys ws x y
permuteInterpretIn perm2 intr =
  InterpretIn \subls term@(Term' _ _ termperm) ->
    fja'
      (permutationToSList $ invPermutation termperm)
      (invPermutation2 perm2)
      subls
      \subls' perm2' ->
        let (perm, perm') = permutation2_to_Permutation perm2'
         in permuteTerm' (invPermutation perm') $ runInterpreter intr subls' (permuteTerm' perm term)

-- TODO: Remove
-- Should be replaced with type-level permutations.
-- You can't do a transitive relation with this either,
-- since Permutation2 xs0 xs1 ys0 ys1 and
--       Permutation2 ys0 ys1 zs0 zs1
-- does not imply that there is a single
-- permutation that carries xs0 to xs1 and
-- zs0 to zs1. This is evident by the fact that
-- ys0 might be made of only one element, meaning
-- there are many ways of going from ys0 to ys1.
-- If there were only one way, the above would hold.
data Permutation2 :: [a] -> [a] -> [b] -> [b] -> Type where
  Permutation2N :: Permutation2 '[] '[] '[] '[]
  Permutation2S ::
    ListEqMod1Idx ys ys' x idx ->
    ListEqMod1Idx ws ws' z idx ->
    Permutation2 xs ys zs ws ->
    Permutation2 (x : xs) ys' (z : zs) ws'

mkListEqMod1Idx :: ListEqMod1 xs xs' x -> (forall idx. ListEqMod1Idx xs xs' x idx -> r) -> r
mkListEqMod1Idx ListEqMod1N k = k ListEqMod1IdxN
mkListEqMod1Idx (ListEqMod1S x) k = mkListEqMod1Idx x \y -> k (ListEqMod1IdxS y)

unListEqMod1Idx :: ListEqMod1Idx xs xs' x idx -> ListEqMod1 xs xs' x
unListEqMod1Idx ListEqMod1IdxN = ListEqMod1N
unListEqMod1Idx (ListEqMod1IdxS idx) = ListEqMod1S $ unListEqMod1Idx idx

flipLengthOfTwo :: LengthOfTwo xs ys len -> LengthOfTwo ys xs len
flipLengthOfTwo LengthOfTwoN = LengthOfTwoN
flipLengthOfTwo (LengthOfTwoS len) = LengthOfTwoS $ flipLengthOfTwo len

transferListEqMod1Idx ::
  LengthOfTwo xs ys len ->
  ListEqMod1Idx xs xs' x idx ->
  (forall ys'. ListEqMod1Idx ys ys' y idx -> r) ->
  r
transferListEqMod1Idx _ ListEqMod1IdxN k = k ListEqMod1IdxN
transferListEqMod1Idx (LengthOfTwoS len) (ListEqMod1IdxS idx) k =
  transferListEqMod1Idx len idx (k . ListEqMod1IdxS)

permutation_to_Permutation2' ::
  LengthOfTwo xs zs len ->
  Permutation xs ys ->
  (forall ws. Permutation2 xs ys zs ws -> LengthOfTwo ys ws len -> r) ->
  r
permutation_to_Permutation2' LengthOfTwoN PermutationN k = k Permutation2N LengthOfTwoN
permutation_to_Permutation2' (LengthOfTwoS len) (PermutationS idx perm) k =
  permutation_to_Permutation2' len perm \perm' len' ->
    mkListEqMod1Idx idx \idx' ->
      transferListEqMod1Idx len' idx' \idx'' ->
        k
          (Permutation2S idx' idx'' perm')
          (lengthOfTwo_add_ListEqMod1_both (unListEqMod1Idx idx') (unListEqMod1Idx idx'') len')

permutation_to_Permutation2 ::
  LengthOfTwo xs zs len ->
  Permutation xs ys ->
  (forall ws. Permutation2 xs ys zs ws -> r) ->
  r
permutation_to_Permutation2 len perm k = permutation_to_Permutation2' len perm \perm' _ -> k perm'

permutation2_to_Permutation :: Permutation2 xs ys zs ws -> (Permutation xs ys, Permutation zs ws)
permutation2_to_Permutation Permutation2N = (PermutationN, PermutationN)
permutation2_to_Permutation (Permutation2S idx idx' perm2) =
  case permutation2_to_Permutation perm2 of
    (perm, perm') -> (PermutationS (unListEqMod1Idx idx) perm, PermutationS (unListEqMod1Idx idx') perm')

flipListEqMod1 ::
  ListEqMod1 xs ys x ->
  ListEqMod1 ys zs y ->
  (forall ws. ListEqMod1 xs ws y -> ListEqMod1 ws zs x -> r) ->
  r
flipListEqMod1 idx ListEqMod1N k = k ListEqMod1N (ListEqMod1S idx)
flipListEqMod1 ListEqMod1N (ListEqMod1S idx) k = k idx ListEqMod1N
flipListEqMod1 (ListEqMod1S idx) (ListEqMod1S idx') k =
  flipListEqMod1 idx idx' \idx'' idx''' -> k (ListEqMod1S idx'') (ListEqMod1S idx''')

remove_from_Permutation ::
  ListEqMod1 xs xs' x ->
  Permutation xs' ys' ->
  (forall ys. Permutation xs ys -> ListEqMod1 ys ys' x -> r) ->
  r
remove_from_Permutation ListEqMod1N (PermutationS idx perm) k = k perm idx
remove_from_Permutation (ListEqMod1S idx0) (PermutationS idx1 perm) k =
  remove_from_Permutation idx0 perm \perm' idx2 ->
    flipListEqMod1 idx2 idx1 \idx1' idx2' ->
      k (PermutationS idx1' perm') idx2'

flip2ListEqMod1Idx ::
  ListEqMod1Idx xs ys x idx ->
  ListEqMod1Idx ys zs y idx' ->
  ListEqMod1Idx xs' ys' x' idx ->
  ListEqMod1Idx ys' zs' y' idx' ->
  ( forall ws ws' idx0 idx'0.
    ListEqMod1Idx xs ws y idx0 ->
    ListEqMod1Idx ws zs x idx'0 ->
    ListEqMod1Idx xs' ws' y' idx0 ->
    ListEqMod1Idx ws' zs' x' idx'0 ->
    r
  ) ->
  r
flip2ListEqMod1Idx idx ListEqMod1IdxN idx' ListEqMod1IdxN k =
  k
    ListEqMod1IdxN
    (ListEqMod1IdxS idx)
    ListEqMod1IdxN
    (ListEqMod1IdxS idx')
flip2ListEqMod1Idx ListEqMod1IdxN (ListEqMod1IdxS idx) ListEqMod1IdxN (ListEqMod1IdxS idx') k =
  k idx ListEqMod1IdxN idx' ListEqMod1IdxN
flip2ListEqMod1Idx (ListEqMod1IdxS idx0) (ListEqMod1IdxS idx1) (ListEqMod1IdxS idx2) (ListEqMod1IdxS idx3) k =
  flip2ListEqMod1Idx idx0 idx1 idx2 idx3 \idx0' idx1' idx2' idx3' ->
    k
      (ListEqMod1IdxS idx0')
      (ListEqMod1IdxS idx1')
      (ListEqMod1IdxS idx2')
      (ListEqMod1IdxS idx3')

remove_from_Permutation2 ::
  ListEqMod1Idx xs xs' x idx ->
  ListEqMod1Idx zs zs' z idx ->
  Permutation2 xs' ys' zs' ws' ->
  (forall ys ws idx'. Permutation2 xs ys zs ws -> ListEqMod1Idx ys ys' x idx' -> ListEqMod1Idx ws ws' z idx' -> r) ->
  r
remove_from_Permutation2 ListEqMod1IdxN ListEqMod1IdxN (Permutation2S idx idx' perm2) k = k perm2 idx idx'
remove_from_Permutation2 (ListEqMod1IdxS idx0) (ListEqMod1IdxS idx1) (Permutation2S idx2 idx3 perm2) k =
  remove_from_Permutation2 idx0 idx1 perm2 \perm2' idx4 idx5 ->
    flip2ListEqMod1Idx idx4 idx2 idx5 idx3 \idx2' idx4' idx3' idx5' ->
      k (Permutation2S idx2' idx3' perm2') idx4' idx5'

permuteInterpretIdxs' ::
  Permutation2 xs ys zs ws ->
  InterpretIdxs xs zs idxs ->
  (forall idxs'. InterpretIdxs ys ws idxs' -> r) ->
  r
permuteInterpretIdxs' perm2 (InterpretIdxsN l) k =
  let (perm, perm') = permutation2_to_Permutation perm2
   in permutation_to_LengthOfTwo (invPermutation perm) \l' ->
        permutation_to_LengthOfTwo perm' \l'' ->
          k
            (InterpretIdxsN $ fst $ transLengthOfTwo (fst $ transLengthOfTwo l' l) l'')
permuteInterpretIdxs' perm2 (InterpretIdxsS idx0 idx1 intr intrs) k =
  permuteInterpretIdxs' perm2 intrs \intrs' ->
    remove_from_Permutation2 idx0 idx1 perm2 \perm2' idx2 idx3 ->
      let intr' = permuteInterpretIn perm2' intr
       in k (InterpretIdxsS idx2 idx3 intr' intrs')

extractLength_from_InterpretIdxs :: InterpretIdxs xs ys idxs -> (forall len. LengthOfTwo xs ys len -> r) -> r
extractLength_from_InterpretIdxs (InterpretIdxsN len) k = k len
extractLength_from_InterpretIdxs (InterpretIdxsS _ _ _ intrs) k = extractLength_from_InterpretIdxs intrs k

permuteInterpretIdxs ::
  Permutation xs ys ->
  InterpretIdxs xs zs idxs ->
  (forall ws idxs'. InterpretIdxs ys ws idxs' -> Permutation ws zs -> r) ->
  r
permuteInterpretIdxs perm intrs k =
  extractLength_from_InterpretIdxs intrs \len ->
    permutation_to_Permutation2 len perm \perm2 ->
      permuteInterpretIdxs' perm2 intrs \intrs' ->
        k intrs' (invPermutation $ snd $ permutation2_to_Permutation perm2)

permuteInterpretation ::
  Permutation xs ys ->
  Interpret xs zs ->
  (forall ws. Interpret ys ws -> Permutation ws zs -> r) ->
  r
permuteInterpretation perm intrs k =
  makeIdxed intrs \intrs' ->
    permuteInterpretIdxs
      perm
      intrs'
      \intrs'' perm' -> k (partialMakeUnIdxed intrs'') perm'

-- If we can interpret from ys to zs,
-- but ys is a permutation of xs,
-- then it follows that we can also interpret  from xs to zs.
-- An interpretation is a list of interpreters,
-- for each interpreter in the list, we must switch its
-- position in the list, in addition to permuting its input
-- and output since the interpreter expected the languages ys
-- while we are giving it xs, and the output must be ws,
-- which is a permutation of zs.
--
-- Implementation:
-- The permutation is a list of indices,
-- which can be visualised as bijective arrows between elements of
-- xs and ys.
-- We must follow each arrow, such that the interpreter at the end of
-- each arrow is put at the position noted by the beginning of the arrow.
-- We can understand this as looking up an index in the list of interpreters.
-- The interpreter has a shape that is incompatible, it is expecting a term
-- with languages ys, when in fact it receives xs, a permutation of ys.
--
-- If you squint enough, this function is similar to transPermutation.
--
-- We start with a InterpretAsc, which we then turn into a
-- InterpretIdxs _ _ _, that contains the same information.
-- This form is much more amenable to permutation.
-- We do two steps of recursion, one within the other.
-- We permute the InterpretIdxs such that the type-level indices
-- are permuted.
-- The goal is then to reorganise the language list such that
-- we can turn it back into another InterpretAsc.
-- We do this by splitting up the work:
-- Given a list of indices idx : idxs, we first handle
-- the tail. If the tail is empty, it is a no-op, otherwise,
-- the tail must be reordered into an ascending order.

swapInterpretPermutation ::
  Permutation xs ys ->
  Interpret ys zs ->
  (forall ws. Interpret xs ws -> Permutation ws zs -> r) ->
  r
swapInterpretPermutation perm intr k =
  permuteInterpretation
    (invPermutation perm)
    intr
    \intr' perm' -> k intr' perm'

permuteTerm' :: Permutation xs ys -> Term' l xs tag -> Term' l ys tag
permuteTerm' perm' (Term' node intrs perm) =
  Term' node intrs (transPermutation perm perm')

permuteTerm :: Permutation xs ys -> Term xs tag -> Term ys tag
permuteTerm perm' (Term (Term' node intrs perm) idx) =
  remove_from_Permutation idx perm' \perm'' idx' ->
    Term (Term' node intrs (transPermutation perm perm'')) idx'

interpretTerm' :: Interpret ls ls' -> Term' l ls tag -> Term' l ls' tag
interpretTerm' intrs' (Term' node intrs perm) =
  swapInterpretPermutation
    perm
    intrs'
    \intrs'' perm' -> Term' node (transInterpret intrs intrs'') perm'

eqListEqMod1Idx ::
  ListEqMod1Idx ls0 ls1 x idx ->
  ListEqMod1Idx ls0' ls1 y idx ->
  ('(ls0, x) :~: '(ls0', y))
eqListEqMod1Idx ListEqMod1IdxN ListEqMod1IdxN = Refl
eqListEqMod1Idx (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') =
  case eqListEqMod1Idx idx idx' of
    Refl -> Refl

data LTE :: Nat -> Nat -> Type where
  LTEN :: LTE x x
  LTES :: LTE (S x) y -> LTE x y

idxInterpret' ::
  LTE idx' idx ->
  ListEqMod1Idx ls0' ls0 l idx ->
  InterpretAsc ls0 ls1 idx' ->
  (forall ls1' l'. ListEqMod1Idx ls1' ls1 l' idx -> InterpretIn ls0' ls1' l l' -> r) ->
  r
idxInterpret'
  LTEN
  idx
  (InterpretAscS idx' idx'' intr _)
  k = case eqListEqMod1Idx idx idx' of
    Refl -> k idx'' intr
idxInterpret'
  (LTES lte)
  idx
  (InterpretAscS _ _ _ intrs)
  k = idxInterpret' lte idx intrs k
idxInterpret' lte idx (InterpretAscN len) _ = absurd lte idx len
  where
    absurd :: LTE idx' idx -> ListEqMod1Idx xs xs' x idx -> LengthOfTwo xs' ys idx' -> a
    absurd _ _ _ = error "FIXME"

data LTEInv :: Nat -> Nat -> Type where
  LTEInvN :: LTEInv x x
  LTEInvS :: LTEInv x y -> LTEInv x (S y)

lteInv_to_LTE :: LTEInv x y -> LTE x y
lteInv_to_LTE LTEInvN = LTEN
lteInv_to_LTE (LTEInvS lte) = step $ lteInv_to_LTE lte
  where
    step :: LTE x y -> LTE x (S y)
    step LTEN = LTES LTEN
    step (LTES lte) = LTES $ step lte

zero_LTEInv :: SNat x -> LTEInv N x
zero_LTEInv SN = LTEInvN
zero_LTEInv (SS x) = LTEInvS $ zero_LTEInv x

zero_LTE :: SNat x -> LTE N x
zero_LTE = lteInv_to_LTE . zero_LTEInv

listEqMod1Idx_to_SNat ::
  ListEqMod1Idx xs xs' x idx ->
  SNat idx
listEqMod1Idx_to_SNat ListEqMod1IdxN = SN
listEqMod1Idx_to_SNat (ListEqMod1IdxS idx) =
  SS $ listEqMod1Idx_to_SNat idx

idxInterpret ::
  ListEqMod1Idx ls0' ls0 l idx ->
  Interpret ls0 ls1 ->
  (forall ls1' l'. ListEqMod1Idx ls1' ls1 l' idx -> InterpretIn ls0' ls1' l l' -> r) ->
  r
idxInterpret idx intrs k = idxInterpret' (zero_LTE (listEqMod1Idx_to_SNat idx)) idx intrs k

idSubLS :: LengthOfTwo ls ls' len -> SubLS ls ls' ls ls'
idSubLS LengthOfTwoN = SubLSBase
idSubLS (LengthOfTwoS len) = SubLSSwap $ idSubLS len

interpretTerm :: Interpret ls ls' -> Term ls tag -> Term ls' tag
interpretTerm intrs (Term term idx) =
  mkListEqMod1Idx idx \idx' ->
    idxInterpret idx' intrs \idx'' intr ->
      interpret_to_LengthOfTwo intrs \len ->
        removeFromLengthOfTwo idx' idx'' len \len' ->
          Term (runInterpreter intr (idSubLS len') term) (unListEqMod1Idx idx'')

indexInto_over_LengthOfTwo ::
  LengthOfTwo xs ys len ->
  IndexInto xs idx ->
  IndexInto ys idx
indexInto_over_LengthOfTwo (LengthOfTwoS _) IndexIntoN = IndexIntoN
indexInto_over_LengthOfTwo (LengthOfTwoS len) (IndexIntoS idx) =
  IndexIntoS $ indexInto_over_LengthOfTwo len idx
indexInto_over_LengthOfTwo LengthOfTwoN idx = case idx of {}

incIndexInto ::
  LengthOfTwo xs ys len ->
  IndexInto xs idx ->
  Either
    (S idx :~: len)
    (IndexInto xs (S idx))
incIndexInto (LengthOfTwoS (LengthOfTwoS _)) IndexIntoN = Right (IndexIntoS IndexIntoN)
incIndexInto (LengthOfTwoS len) (IndexIntoS idx) =
  case incIndexInto len idx of
    Left Refl -> Left Refl
    Right idx -> Right $ IndexIntoS idx
incIndexInto LengthOfTwoN idx = case idx of {}
incIndexInto (LengthOfTwoS LengthOfTwoN) IndexIntoN = Left Refl

-- Given an InterpretIn xs xs x y,
-- we can expand this into an Interpret (x : xs) (y : xs).
-- For the case of the `x` language, trivially we use the
-- given interpreter.
-- For the other cases, we don't _do_ any real work:
-- Given some x' which we preserve as x', we are given
-- a node which might contain any of the languages in (x : xs)
-- modulo x'.
-- For the languages beside x, we simply preserve them,
-- however, if x is present in the input term, we must translate
-- this into an x'. We do this through the very function we are
-- defining now, i.e. recursion.
--
-- We can expand this principle to more than a single pair of languages.
-- Given some xs and ys, given for each x and y in xs and ys an
-- InterpretIn (xs - x <> xs') (ys - y <> ys') x y,
-- we can transform this into an
-- Interpret (xs <> xs') (ys <> ys').
-- The logic follows the same pattern,
-- for the languages for which we have an interpreter, use it,
-- for the others, use recursion to delay the interpretation.

transSubLS ::
  SubLS xs ys zs ws ->
  SubLS zs ws as bs ->
  SubLS xs ys as bs
transSubLS SubLSBase SubLSBase = SubLSBase
transSubLS (SubLSSwap subls) (SubLSSwap subls') = SubLSSwap $ transSubLS subls subls'
transSubLS (SubLSSkip subls) (SubLSSwap subls') = SubLSSkip $ transSubLS subls subls'
transSubLS subls (SubLSSkip subls') = SubLSSkip $ transSubLS subls subls'
transSubLS subls SubLSBase = case eqSubLS subls of
  Refl -> SubLSBase

sublsInterpretIn ::
  SubLS zs ws xs ys ->
  InterpretIn xs ys x y ->
  InterpretIn zs ws x y
sublsInterpretIn subls intr =
  InterpretIn \subls' term -> runInterpreter intr (transSubLS subls' subls) term

data Filter :: [a] -> [a] -> Type where
  FilterN :: Filter '[] '[]
  FilterInc :: Filter xs ys -> Filter (x : xs) (y : ys)
  FilterExc :: Filter xs ys -> Filter xs (y : ys)

{-
data Filter :: [Bool] -> [a] -> [a] -> Type where
  FilterN :: Filter '[] '[] '[]
  FilterInc :: Filter bs xs ys -> Filter (True : bs) (x : xs) (y : ys)
  FilterExc :: Filter bs xs ys -> Filter (False : bs) xs (y : ys)
-}

data Zip :: [a] -> [b] -> [(a, b)] -> Type where
  ZipN :: Zip '[] '[] '[]
  ZipS :: Zip xs ys xys -> Zip (x : xs) (y : ys) ('(x, y) : xys)

filterInterpret ::
  Zip xs ys xys ->
  Zip zs ws zws ->
  Filter xys zws ->
  Interpret xs ys ->
  Interpret zs ws
filterInterpret = undefined

sublsInterpret ::
  LengthOfTwo xs ys len ->
  SubLS xs ys zs ws ->
  Interpret zs ws ->
  Interpret xs ys
sublsInterpret len subls intrs = undefined

removeInterpretIn ::
  ListEqMod1Idx xs' xs x' idx ->
  ListEqMod1Idx ys' ys y' idx ->
  InterpretIn xs ys x y ->
  InterpretIn xs' ys' x y
removeInterpretIn idx idx' intr =
  InterpretIn \subls term -> runInterpreter intr (insertSubLSSkip idx idx' subls) term

eqSubLS :: SubLS xs ys zs zs -> (xs :~: ys)
eqSubLS SubLSBase = Refl
eqSubLS (SubLSSwap subls) = case eqSubLS subls of Refl -> Refl
eqSubLS (SubLSSkip subls) = case eqSubLS subls of Refl -> Refl

interpretOne :: LengthOfTwo xs xs len -> InterpretIn xs xs x y -> Interpret (x : xs) (y : xs)
interpretOne len@(LengthOfTwoS _) intr = InterpretAscS ListEqMod1IdxN ListEqMod1IdxN intr (go intr len IndexIntoN)
  where
    go ::
      InterpretIn xs xs x y ->
      LengthOfTwo xs xs len ->
      IndexInto xs idx ->
      InterpretAsc (x : xs) (y : xs) (S idx)
    go intr len idx =
      removeListEqMod1Idx idx \lidx ->
        InterpretAscS (ListEqMod1IdxS lidx) (ListEqMod1IdxS lidx) (redir intr lidx) $
          case incIndexInto len idx of
            Right idx' -> go intr len idx'
            Left Refl -> InterpretAscN (LengthOfTwoS len)
    redir ::
      InterpretIn xs xs x y ->
      ListEqMod1Idx xs' xs x' idx ->
      InterpretIn (x : xs') (y : xs') x' x'
    redir intr idx =
      InterpretIn \subls term@(Term' _ _ perm) ->
        case subls of
          SubLSSwap subls' -> case eqSubLS subls' of
            Refl -> permutationToLengthOfTwo (invPermutation perm) \(LengthOfTwoS len') ->
              interpretTerm' (interpretOne len' $ sublsInterpretIn subls' $ removeInterpretIn idx idx intr) term
          SubLSSkip subls' -> case eqSubLS subls' of Refl -> term
interpretOne LengthOfTwoN intr =
  InterpretAscS ListEqMod1IdxN ListEqMod1IdxN intr $
    InterpretAscN (LengthOfTwoS LengthOfTwoN)

term'_to_length :: Term' l ls tag -> (forall len. LengthOf ls len -> r) -> r
term'_to_length (Term' _ _ perm) k = permutationToLengthOfTwo (invPermutation perm) k

length_subls ::
  SubLS xs ys zs ws ->
  LengthOf xs len ->
  LengthOfTwo xs ys len
length_subls SubLSBase len = len
length_subls (SubLSSwap subls) (LengthOfTwoS len) = LengthOfTwoS $ length_subls subls len
length_subls (SubLSSkip subls) len = length_subls subls len

-- FIXME: generalise
-- Interpreters form something like a monoid
interpretExpand :: Interpret xs ys -> Interpret (z : xs) (z : ys)
interpretExpand intrs = InterpretAscS ListEqMod1IdxN ListEqMod1IdxN (intr intrs) $ go intrs where
  intr :: Interpret xs ys -> InterpretIn xs ys z z
  intr intrs =
    InterpretIn \subls term ->
      term'_to_length term \len ->
        interpretTerm' (sublsInterpret (length_subls subls len) subls intrs) term
  addSubLS ::
    SList xs ->
    SubLS xs ys zs ws ->
    (forall xs' ys'. SubLS xs' ys' zs ws ->
      Permutation (x : xs) xs' ->
      Permutation (x : ys) ys' ->
      r
    ) ->
    r
  addSubLS slist SubLSBase k =
    let
      perm = idPermutation (SCons slist)
    in
      k SubLSBase perm perm
  addSubLS slist (SubLSSkip subls) k =
    addSubLS slist subls \subls' perm perm' ->
      k (SubLSSkip subls') perm perm'
  addSubLS (SCons slist) (SubLSSwap subls) k =
    addSubLS slist subls \subls' (PermutationS idx perm) (PermutationS idx' perm') ->
      k
        (SubLSSwap subls')
        (PermutationS (ListEqMod1S idx) $ PermutationS ListEqMod1N perm)
        (PermutationS (ListEqMod1S idx') $ PermutationS ListEqMod1N perm')
  helper :: InterpretIn xs ys x y -> InterpretIn (z : xs) (z : ys) x y
  helper intr = InterpretIn \case
    SubLSSwap subls -> \term@(Term' _ _ perm) ->
      case permutationToSList $ invPermutation perm of
        SCons slist -> addSubLS slist subls \subls' perm perm' ->
          permuteTerm' (invPermutation perm')
            $ runInterpreter intr subls'
            $ permuteTerm' perm term
    SubLSSkip subls -> \term -> runInterpreter intr subls term
  go :: InterpretAsc xs ys idx -> InterpretAsc (z : xs) (z : ys) (S idx)
  go (InterpretAscN len) = InterpretAscN (LengthOfTwoS len)
  go (InterpretAscS idx idx' intr rest) = InterpretAscS (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') (helper intr) (go rest)

data Catenation xs ys zs where
  CatenationN :: Catenation '[] ys ys
  CatenationS :: Catenation xs ys zs -> Catenation (x : xs) ys (x : zs)

-- Simple languages simplify working with Plutarch.
-- In most cases, you do not need any exotic power.
-- A simple language has simple constructors that do not
-- care about inner languages and catenates them all.
type SimpleLanguage = [Tag] -> Tag -> Type
data InstSimpleLanguage :: SimpleLanguage -> Language

-- FIXME: Generalise to arbitrary node arities
data instance L (InstSimpleLanguage l) ls tag where
  SimpleLanguageNode0 :: l '[] tag -> L (InstSimpleLanguage l) '[] tag
  SimpleLanguageNode1 :: l '[arg] tag -> Term ls arg -> L (InstSimpleLanguage l) ls tag
  SimpleLanguageNode2 ::
    l '[arg, arg'] tag ->
    Term ls arg ->
    Term ls' arg' ->
    Catenation ls ls' ls'' ->
    L (InstSimpleLanguage l) ls'' tag
  ContractSimpleLanguage ::
    Term (InstSimpleLanguage l : InstSimpleLanguage l : ls) tag ->
    L (InstSimpleLanguage l) ls tag
  ExpandSimpleLanguage :: Term ls tag -> L (InstSimpleLanguage l) ls tag

-- How do we extract the AST from the term?
-- We have a root node of our language which we open up.
-- Inside, we have subnodes of unknown languages, which
-- we interpret into our known language using the embedded
-- information.
-- Now we have a node of our language along with subnodes of known languages.
-- We perform a recursive step on each subnode and accumulate the results.
-- Each subnode might have one or more known languages, hence we must support
-- operating on multiples of our known languages.

data Repeated :: a -> [a] -> Type where
  RepeatedN :: Repeated x '[]
  RepeatedS :: Repeated x xs -> Repeated x (x : xs)

newtype SimpleFolder l r = SimpleFolder (forall args tag. l args tag -> NP r args -> r tag)

runSimpleFolder ::
  SimpleFolder l r ->
  l args tag ->
  NP r args ->
  r tag
runSimpleFolder (SimpleFolder f) node children = f node children

data InterpretDesc :: [Language] -> [Language] -> Nat -> Type where
  InterpretDescN :: LengthOfTwo ls0 ls1 len -> InterpretDesc ls0 ls1 N
  InterpretDescS ::
    ListEqMod1Idx ls0' ls0 l idx ->
    ListEqMod1Idx ls1' ls1 l' idx ->
    InterpretIn ls0' ls1' l l' ->
    InterpretDesc ls0 ls1 idx ->
    InterpretDesc ls0 ls1 (S idx)

data Drop :: Nat -> [a] -> [a] -> Type where
  DropN :: Drop N xs xs
  DropS :: Drop n xs ys -> Drop (S n) (x : xs) ys

data Take :: Nat -> [a] -> [a] -> Type where
  TakeN :: Take N xs '[]
  TakeS :: Take n xs ys -> Take (S n) (x : xs) (x : ys)

data TakeInv :: Nat -> [a] -> [a] -> Type where
  TakeInvN :: LengthOf xs len -> TakeInv len xs xs
  TakeInvS :: TakeInv (S n) xs ys -> ListEqMod1Idx zs ys x n -> TakeInv n xs zs

type LengthOf xs len = LengthOfTwo xs xs len

data LTE' :: Nat -> Nat -> Type where
  LTE'N :: LTE' N y
  LTE'S :: LTE' x y -> LTE' (S x) (S y)

length_to_snat ::
  LengthOfTwo xs ys len ->
  SNat len
length_to_snat LengthOfTwoN = SN
length_to_snat (LengthOfTwoS len) = SS $ length_to_snat len

combineLengthOfTwo ::
  LengthOfTwo xs ys len ->
  LengthOfTwo zs ws len ->
  LengthOfTwo xs zs len
combineLengthOfTwo LengthOfTwoN LengthOfTwoN = LengthOfTwoN
combineLengthOfTwo (LengthOfTwoS len) (LengthOfTwoS len') = LengthOfTwoS $ combineLengthOfTwo len len'

-- You can imagine this function as taking an interpretation
-- from xs to ys, and _splitting it up_, such that you
-- have two separate interpretations, one from the lower half of
-- xs to the lower half of ys, and the other from the upper half of xs
-- to the upper half of ys.
-- This works by marking every language that is discluded in one part with SubLSSkip.
-- Thus, if you split two interpretations apart then join them again, the interpreters
-- inherently lose context. What was there is no longer there.
-- FIXME: Is there a way to fix the above?
interpretSplit ::
  Catenation xs ys zs ->
  Interpret zs ws ->
  (forall xs' ys'. Interpret xs xs' -> Interpret ys ys' -> Catenation xs' ys' ws -> r) ->
  r
interpretSplit cat intr k =
  catenation_to_length cat \len ->
    let snat = length_to_snat len in
      interpret_to_LengthOfTwo intr \len' ->
        let lte = prove_LTE cat len len' in
        case go len' snat (add_n_N_n snat) lte (InterpretDescN len') intr of
          (desc, asc) -> prove_split (length_to_snat len) len' lte \x y z ->
            case (cutDesc (prove_Take cat len) x desc, cutAsc (prove_Drop cat len) y asc) of
              (lower, upper) -> k lower upper z
  where
  prove_split ::
    SNat n ->
    LengthOfTwo zs ws len ->
    LTE' n len ->
    (forall xs ys. Take n ws xs -> Drop n ws ys -> Catenation xs ys ws -> r) ->
    r
  prove_split SN _ LTE'N k = k TakeN DropN CatenationN
  prove_split (SS SN) (LengthOfTwoS _) (LTE'S LTE'N) k = k (TakeS TakeN) (DropS DropN) (CatenationS CatenationN)
  prove_split (SS n) (LengthOfTwoS len) (LTE'S lte) k =
    prove_split n len lte \take drop cat -> k (TakeS take) (DropS drop) (CatenationS cat)
  prove_split (SS _) LengthOfTwoN lte _ = case lte of
  prove_Take ::
    Catenation xs ys zs ->
    LengthOf xs len ->
    Take len zs xs
  prove_Take CatenationN LengthOfTwoN = TakeN
  prove_Take (CatenationS cat) (LengthOfTwoS len) = TakeS $ prove_Take cat len
  prove_Drop ::
    Catenation xs ys zs ->
    LengthOf xs len ->
    Drop len zs ys
  prove_Drop CatenationN LengthOfTwoN = DropN
  prove_Drop (CatenationS cat) (LengthOfTwoS len) = DropS $ prove_Drop cat len
  prove_LTE ::
    Catenation xs ys zs ->
    LengthOf xs len ->
    LengthOfTwo zs zs' len' ->
    LTE' len len'
  prove_LTE CatenationN LengthOfTwoN _ = LTE'N
  prove_LTE (CatenationS cat) (LengthOfTwoS len) (LengthOfTwoS len') =
    LTE'S $ prove_LTE cat len len'
  catenation_to_length ::
    Catenation xs ys zs ->
    (forall len. LengthOf xs len -> r) ->
    r
  catenation_to_length CatenationN k = k LengthOfTwoN
  catenation_to_length (CatenationS cat) k =
    catenation_to_length cat (k . LengthOfTwoS)
  cutAscSingle ::
    InterpretAsc (x : xs) (y : ys) (S idx) ->
    InterpretAsc xs ys idx
  cutAscSingle (InterpretAscN (LengthOfTwoS len)) = InterpretAscN len
  cutAscSingle (InterpretAscS (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') intr intrs) =
    InterpretAscS idx idx' (removeInterpretIn ListEqMod1IdxN ListEqMod1IdxN intr) $ cutAscSingle intrs
  cutAsc ::
    Drop idx xs xs' ->
    Drop idx ys ys' ->
    InterpretAsc xs ys idx ->
    Interpret xs' ys'
  cutAsc DropN DropN intrs = intrs
  cutAsc (DropS dx) (DropS dy) intrs =
    cutAsc dx dy (cutAscSingle intrs)
  -- cutDescSingle (InterpretDescN (LengthOfTwoS len)) = InterpretDescN len
  --cutDescSingle (InterpretDescS (ListEqMod1IdxS idx) (ListEqMod1IdxS idx') intr intrs) =
  --  InterpretDescS idx idx' (removeInterpretIn ListEqMod1IdxN ListEqMod1IdxN intr) $ cutDescSingle intrs
  {-
  cutDesc' ::
    TakeInv idx xs xs' ->
    TakeInv idx ys ys' ->
    InterpretDesc xs ys idx ->
    Interpret xs' ys'
  cutDesc' (TakeInvN len) (TakeInvN len') intrs = _ intrs
  -}
  cutDesc ::
    Take idx xs xs' ->
    Take idx ys ys' ->
    InterpretDesc xs ys idx ->
    Interpret xs' ys'
  cutDesc TakeN TakeN (InterpretDescN len) = InterpretAscN LengthOfTwoN
  -- cutDesc (TakeS tx) (TakeS ty) intrs =
  go ::
    LengthOfTwo xs ys len ->
    SNat count ->
    Add count idx idx' ->
    LTE' idx' len ->
    InterpretDesc xs ys idx ->
    InterpretAsc xs ys idx ->
    (InterpretDesc xs ys idx', InterpretAsc xs ys idx')
  go _ SN AddN _ desc asc = (desc, asc)
  go len (SS count) (AddS add) lte desc (InterpretAscS idx idx' intr asc) =
    go len count (addSFlipped add) lte (InterpretDescS idx idx' intr desc) asc
  go _ (SS _) (AddS _) _ _ (InterpretAscN _) = error "FIXME: prove impossible"

repeatedOverPermutation ::
  Permutation xs ys ->
  Repeated x xs ->
  Repeated x ys
repeatedOverPermutation PermutationN RepeatedN = RepeatedN
repeatedOverPermutation (PermutationS idx perm) (RepeatedS rep) =
  insertRepeated idx $ repeatedOverPermutation perm rep

insertRepeated ::
  ListEqMod1 xs xs' x ->
  Repeated x xs ->
  Repeated x xs'
insertRepeated ListEqMod1N rep = RepeatedS rep
insertRepeated (ListEqMod1S idx) (RepeatedS rep) = RepeatedS $ insertRepeated idx rep

repeatedOverCatenation ::
  Catenation xs ys zs ->
  Repeated x zs ->
  (Repeated x xs, Repeated x ys)
repeatedOverCatenation CatenationN rep = (RepeatedN, rep)
repeatedOverCatenation (CatenationS cat) (RepeatedS rep) =
  case repeatedOverCatenation cat rep of
    (x, y) -> (RepeatedS x, y)

removeRepeated ::
  ListEqMod1 xs' xs y ->
  Repeated x xs ->
  Repeated x xs'
removeRepeated ListEqMod1N (RepeatedS rep) = rep
removeRepeated (ListEqMod1S idx) (RepeatedS rep) = RepeatedS $ removeRepeated idx rep

inRepeated ::
  ListEqMod1 xs' xs y ->
  Repeated x xs ->
  (x :~: y)
inRepeated ListEqMod1N (RepeatedS _) = Refl
inRepeated (ListEqMod1S idx) (RepeatedS rep) = inRepeated idx rep

extractSimpleLanguage ::
  SimpleFolder l r ->
  Term '[InstSimpleLanguage l] tag ->
  r tag
extractSimpleLanguage = go' (RepeatedS RepeatedN) where
  go' ::
    Repeated (InstSimpleLanguage l) ls ->
    SimpleFolder l r ->
    Term ls tag ->
    r tag
  go' rep folder (Term term idx) =
    case inRepeated idx rep of
      Refl -> go (removeRepeated idx rep) folder term
  go ::
    Repeated (InstSimpleLanguage l) ls ->
    SimpleFolder l r ->
    Term' (InstSimpleLanguage l) ls tag ->
    r tag
  go _ folder (Term' (SimpleLanguageNode0 node) _ _) = runSimpleFolder folder node Nil
  go rep folder (Term' (SimpleLanguageNode1 node arg) intr perm) =
    case go' rep folder (permuteTerm perm $ interpretTerm intr arg) of
      arg' -> runSimpleFolder folder node (arg' :* Nil)
  go rep folder (Term' (SimpleLanguageNode2 node argx argy cat) intr perm) =
    interpretSplit cat intr \intrx intry catx ->
        let
          rep' = repeatedOverPermutation (invPermutation perm) rep
          (repx, repy) = repeatedOverCatenation catx rep'
          argx' = go' repx folder (interpretTerm intrx argx)
          argy' = go' repy folder (interpretTerm intry argy)
        in runSimpleFolder folder node (argx' :* argy' :* Nil)
  go rep folder (Term' (ExpandSimpleLanguage term) intr perm) =
    go' rep folder $ permuteTerm perm $ interpretTerm intr term
  go rep folder (Term' (ContractSimpleLanguage term) intr perm) =
    go' (RepeatedS $ RepeatedS rep) folder
      $ permuteTerm (PermutationS ListEqMod1N
      $ PermutationS ListEqMod1N perm)
      $ interpretTerm (interpretExpand
      $ interpretExpand intr) term

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

permutationToSList :: Permutation xs ys -> SList xs
permutationToSList PermutationN = SNil
permutationToSList (PermutationS _ perm) = SCons $ permutationToSList perm

insertSList :: ListEqMod1 xs ys x -> SList xs -> SList ys
insertSList ListEqMod1N s = SCons s
insertSList (ListEqMod1S x) (SCons s) = SCons $ insertSList x s

removeSList :: ListEqMod1 xs ys x -> SList ys -> SList xs
removeSList ListEqMod1N (SCons s) = s
removeSList (ListEqMod1S x) (SCons s) = SCons $ removeSList x s

termToSList :: Term ls tag -> SList ls
termToSList (Term (Term' _ _ perm) idx) =
  insertSList idx $ permutationToSList $ invPermutation perm

permutationToLengthOfTwo :: Permutation xs ys -> (forall len. LengthOfTwo xs xs len -> r) -> r
permutationToLengthOfTwo PermutationN k = k LengthOfTwoN
permutationToLengthOfTwo (PermutationS _ perm) k = permutationToLengthOfTwo perm (k . LengthOfTwoS)

idPermutation :: SList xs -> Permutation xs xs
idPermutation SNil = PermutationN
idPermutation (SCons xs) = PermutationS ListEqMod1N (idPermutation xs)

idPermutation2 :: SList xs -> Permutation2 xs xs xs xs
idPermutation2 SNil = Permutation2N
idPermutation2 (SCons xs) = Permutation2S ListEqMod1IdxN ListEqMod1IdxN (idPermutation2 xs)

lengthOfTwo_to_SList :: LengthOfTwo xs ys len -> (SList xs, SList ys)
lengthOfTwo_to_SList LengthOfTwoN = (SNil, SNil)
lengthOfTwo_to_SList (LengthOfTwoS len) =
  case lengthOfTwo_to_SList len of (x, y) -> (SCons x, SCons y)

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

addFunctional :: Add n m o -> Add n m o' -> o :~: o'
addFunctional AddN AddN = Refl
addFunctional (AddS x) (AddS y) = case addFunctional x y of
  Refl -> Refl

undoAddSFlipped :: Add n (S m) o -> (forall o'. o :~: S o' -> Add n m o' -> r) -> r
undoAddSFlipped AddN k = k Refl AddN
undoAddSFlipped (AddS add) k = undoAddSFlipped add \Refl add' -> k Refl (AddS add')

addSFlipped' :: Add n m o -> Add n' m m' -> Add n' o o' -> Add n m' o'
addSFlipped' AddN x y = case addFunctional x y of Refl -> AddN
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

-- insertListEqMod1Idx :: IndexInto xs idx -> (forall xs' x. ListEqMod1Idx xs xs' x idx -> r) -> r
-- insertListEqMod1Idx IndexIntoN k = k ListEqMod1IdxN
-- insertListEqMod1Idx (IndexIntoS idx) k = insertListEqMod1Idx idx (k . ListEqMod1IdxS)

removeListEqMod1Idx :: IndexInto xs idx -> (forall xs' x. ListEqMod1Idx xs' xs x idx -> r) -> r
removeListEqMod1Idx IndexIntoN k = k ListEqMod1IdxN
removeListEqMod1Idx (IndexIntoS idx) k = removeListEqMod1Idx idx (k . ListEqMod1IdxS)

suffixOf_to_ListEqMod1Idx :: SuffixOf xs ys (S idx) -> (forall xs' x. ListEqMod1Idx xs' xs x idx -> r) -> r
suffixOf_to_ListEqMod1Idx suffix k = removeListEqMod1Idx (suffixOf_to_IndexInto suffix) k

idInterpretation :: SList xs -> Interpret xs xs
idInterpretation = f SuffixOfN
  where
    extractLength :: LengthOf ys len -> Add len len' len'' -> SuffixOf xs ys len' -> LengthOf xs len''
    extractLength (LengthOfTwoS len) (AddS add) SuffixOfN = LengthOfTwoS $ extractLength len add SuffixOfN
    extractLength len add (SuffixOfS suffix) =
      undoAddSFlipped add \Refl add' ->
        extractLength (LengthOfTwoS len) (AddS add') suffix
    extractLength LengthOfTwoN AddN SuffixOfN = LengthOfTwoN
    f :: SuffixOf xs ys idx -> SList ys -> InterpretAsc xs xs idx
    f suffix SNil = InterpretAscN (extractLength LengthOfTwoN AddN suffix)
    f suffix (SCons xs) =
      suffixOf_to_ListEqMod1Idx (SuffixOfS suffix) \idx ->
        InterpretAscS idx idx g $ f (SuffixOfS suffix) xs
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

runContractible' :: Contractible l -> Term (l : l : ls) tag -> Term (l : ls) tag
runContractible' c term = flip Term ListEqMod1N $ Term' (runContractible c term) (idInterpretation slist) (idPermutation slist) where
  SCons (SCons slist) = termToSList term

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

bringTerm' :: ListEqMod1 ls' ls l' -> Term' l ls tag -> Term' l (l' : ls') tag
bringTerm' idx (Term' node intrs perm) = Term' node intrs (bringPermutation idx perm)

bringTerm :: ListEqMod1 ls' ls l -> Term ls tag -> Term (l : ls') tag
bringTerm idx (Term term idx') =
  cmpListEqMod1 idx idx' \case
    Left Refl -> Term term ListEqMod1N
    Right (idx'', idx''') -> Term (bringTerm' idx'' term) (ListEqMod1S idx''')

unbringTerm' :: ListEqMod1 ls' ls l' -> Term' l (l' : ls') tag -> Term' l ls tag
unbringTerm' idx (Term' node intrs perm) = Term' node intrs (unbringPermutation idx perm)

unbringTerm :: ListEqMod1 ls' ls l -> Term (l : ls') tag -> Term ls tag
unbringTerm idx term =
  flip permuteTerm term
    $ listEqMod1_to_Permutation
      (case termToSList term of SCons slist -> slist)
      idx

contractThere' :: ListEqMod1 ls' ls l -> Contractible l -> Term (l : ls) tag -> Term (l : ls') tag
contractThere' idx c term = contract c $ bringTerm (ListEqMod1S idx) term

elemOf_to_listEqMod1 :: ElemOf xs x -> (forall xs'. ListEqMod1 xs' xs x -> r) -> r
elemOf_to_listEqMod1 ElemOfN k = k ListEqMod1N
elemOf_to_listEqMod1 (ElemOfS rest) k = elemOf_to_listEqMod1 rest (k . ListEqMod1S)

elemOf_to_listEqMod1Idx :: ElemOf xs x -> (forall xs' idx. ListEqMod1Idx xs' xs x idx -> r) -> r
elemOf_to_listEqMod1Idx ElemOfN k = k ListEqMod1IdxN
elemOf_to_listEqMod1Idx (ElemOfS rest) k = elemOf_to_listEqMod1Idx rest (k . ListEqMod1IdxS)

listEqMod1_to_elemOf :: ListEqMod1 xs' xs x -> ElemOf xs x
listEqMod1_to_elemOf ListEqMod1N = ElemOfN
listEqMod1_to_elemOf (ListEqMod1S x) = ElemOfS $ listEqMod1_to_elemOf x

listEqMod1Idx_to_elemOf :: ListEqMod1Idx xs' xs x idx -> ElemOf xs x
listEqMod1Idx_to_elemOf = listEqMod1_to_elemOf . unListEqMod1Idx

contractThere :: ElemOf ls l -> Contractible l -> Term (l : ls) tag -> Term ls tag
contractThere idx c term = elemOf_to_listEqMod1 idx \idx' -> unbringTerm idx' $ contractThere' idx' c term

data ReverseCatenation :: [a] -> [a] -> [a] -> Type where
  ReverseCatenationN :: ReverseCatenation '[] ys ys
  ReverseCatenationS :: ReverseCatenation xs (x : ys) zs -> ReverseCatenation (x : xs) ys zs

type Reverse :: [a] -> [a] -> Type
type Reverse xs ys = ReverseCatenation xs '[] ys

{-
catenationToNilIsInput :: Catenation xs '[] ys -> xs :~: ys
catenationToNilIsInput CatenationN = Refl
catenationToNilIsInput (CatenationS rest) = case catenationToNilIsInput rest of Refl -> Refl
-}

reverseCatenationFunctional :: ReverseCatenation xs suffix ys -> ReverseCatenation xs suffix zs -> ys :~: zs
reverseCatenationFunctional ReverseCatenationN ReverseCatenationN = Refl
reverseCatenationFunctional (ReverseCatenationS ys) (ReverseCatenationS zs) =
  case reverseCatenationFunctional ys zs of Refl -> Refl

reverseCatenation_to_length ::
  ReverseCatenation xs ys zs ->
  (forall len. LengthOf xs len -> r) ->
  r
reverseCatenation_to_length ReverseCatenationN k = k LengthOfTwoN
reverseCatenation_to_length (ReverseCatenationS cat) k =
  reverseCatenation_to_length cat (k . LengthOfTwoS)

snat_to_Add :: SNat x -> (forall z. Add x y z -> r) -> r
snat_to_Add SN k = k AddN
snat_to_Add (SS x) k = snat_to_Add x (k . AddS)

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
multicontract' cnx cny (MultiContractibleContract c elmof rest) term =
  reverseCatenation_to_length cnx \len ->
    elemOf_to_listEqMod1Idx elmof \idx ->
      let snat = length_to_snat len in
      snat_to_Add snat \add ->
        util cnx len add (ListEqMod1IdxS idx) \idx' ->
          util cnx len (add_n_N_n snat) ListEqMod1IdxN \idx'' ->
            createPerms (termToSList term) add idx' idx'' \perm perm' ->
              multicontract' (removeRevCat len (add_n_N_n snat) ListEqMod1IdxN idx'' cnx) cny rest
                $ permuteTerm perm' $ runContractible' c $ permuteTerm (invPermutation perm) term
  where
    createPerms ::
      SList xs ->
      Add idx' (S diff) idx ->
      ListEqMod1Idx ys xs x idx ->
      ListEqMod1Idx zs xs x idx' ->
      (forall ws.
        Permutation (x : x : ws) xs ->
        Permutation (x : ws) zs ->
        r
      ) ->
      r
    createPerms slist add idx idx' k =
      cmpListEqMod1Idx idx idx' \case
        Left eq -> error "prove absurd" eq add
        Right (Left (eq, idx'', idx''')) -> error "prove absurd" eq idx'' idx''' add
        Right (Right (Refl, idx'', idx''')) ->
          let
            uidx = unListEqMod1Idx idx''
            perm =
              listEqMod1_to_Permutation
                (removeSList uidx $ removeSList (unListEqMod1Idx idx') $ slist)
                uidx
          in
            k (PermutationS (unListEqMod1Idx idx') perm) perm
    removeRevCat ::
      LengthOf xs len ->
      Add len idx idx' ->
      ListEqMod1Idx ys' ys y idx ->
      ListEqMod1Idx zs' zs y idx' ->
      ReverseCatenation xs ys zs ->
      ReverseCatenation xs ys' zs'
    removeRevCat LengthOfTwoN AddN idx idx' ReverseCatenationN =
      case listEqMod1IdxFunctional idx idx' of Refl -> ReverseCatenationN
    removeRevCat (LengthOfTwoS len) (AddS add) idx idx' (ReverseCatenationS cat) =
      ReverseCatenationS $ removeRevCat len (addSFlipped add) (ListEqMod1IdxS idx) idx' cat
    util ::
      ReverseCatenation xs ys zs ->
      LengthOf xs len ->
      Add len idx idx' ->
      ListEqMod1Idx ys' ys x idx ->
      (forall zs'. ListEqMod1Idx zs' zs x idx' -> r) ->
      r
    util ReverseCatenationN LengthOfTwoN AddN idx k = k idx
    util (ReverseCatenationS cat) (LengthOfTwoS len) (AddS add) idx k =
      util cat len (addSFlipped add) (ListEqMod1IdxS idx) k

multicontract :: MultiContractible ls ls' -> Term ls tag -> Term ls' tag
multicontract = multicontract' ReverseCatenationN ReverseCatenationN



-- contractThere _ c $ multicontract' _ _ rest term
-- multicontract' _ _ (MultiContractibleSkip rest) term = _

-- pand' :: Term ls0 (Expr Bool) -> Term ls1 (Expr Bool) -> Term (Bools : Append ls0 ls1) (Expr Bool)
-- pand' x y = Term (Term' (SimpleLanguageNode _ And) _ _) ListEqMod1N
