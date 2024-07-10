{-# LANGUAGE UnboxedTuples, MagicHash, UnliftedNewtypes #-}

import Data.Kind (Type)
import GHC.Exts (ZeroBitType)

type Unit :: ZeroBitType
type Unit = (# #)

type TwoUnits :: ZeroBitType
newtype TwoUnits = TwoUnits (# Unit, Unit #)
