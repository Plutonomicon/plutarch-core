{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Examples.ULC (result) where

import Plutarch.Prelude
import Plutarch.ULC (compile, ULC)
import Data.Functor.Identity (runIdentity)

pid :: PConstructable edsl (PUnit #-> PUnit) => Term edsl (PUnit #-> PUnit)
pid = pcon $ PLam \x -> x

result :: ULC
result = runIdentity $ compile pid
