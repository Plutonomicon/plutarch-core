-- | Compile into Lua
module Plutarch.Frontends.Lua () where

import Plutarch.Prelude

data PTable k v ef
data PMutableTable k v ef

class PLuaRaw e where
  punsafeLuaRaw :: String -> [T e a] -> T e b
  punsafeLuaEffectfulRaw :: String -> [T e a] -> ET e (T e b)

-- Impure function
data (#!->) (a :: PType) (b :: PType) (ef :: PTypeF)
  deriving (PHasRepr) via PHasReprDerive PReprPrimitive

f :: PLua e => T e (PMutableTable PInteger PInteger) -> ETC e (T e PInteger)
f = \(t :: T _ (PMutableTable PInteger PInteger)) -> P.do
  x <- pbind $ plam \(_ :: T _ PUnit) -> plamImpure \i -> pshareTable t \t' -> ppureTerm $ pgetField t' i
  x <- P.do
    t <- pshareTable t
    c <- plet $ plam $ pgetField t
    n <- plet $ c # 5
    n' <- plet $ c # 5
    -- n = n'
    n
  psetField t 5 2
  line <- preadLine
  line' <- preadLine
  eterm $ x

class
  ( PLC e
  , PSOP e
  , PLuaRaw e
  , IsPType e PAny
  , IsPType2 e PTable
  , IsPType2 e PMutableTable
  , PConstructable2 e (#!->)
  , PMutable e
  ) =>
  PLuaTerm e
  where
  pmkTable :: [(T e k, T e v)] -> T e (PTable k v)
  pgetField :: T e (PTable k v) -> T e k -> T e v
  pshareTable :: T e (PMutableTable k v) -> ETC e (PTable k v)
  pgetGlobal :: String -> T e PAny
  psetField :: T e (PMutableTable k v) -> T e k -> T e v -> ETC e ()
  plamImpure :: (T e a -> ETC e (T e b)) -> T e (a #!-> b)
  (#!) :: T e (a #!-> b) -> T e a -> ETC e (T e b)

pplusLua :: PLuaTerm e => T e PInteger -> T e PInteger -> T e PInteger
pplusLua = phoistAcyclic $ \x y -> punsafeLuaRaw "$1 + $2" [x, y]
