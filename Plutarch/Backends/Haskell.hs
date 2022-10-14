module Plutarch.Backends.Haskell (compile) where

import Data.Text (Text)

class PHaskell

newtype Impl

compile' :: forall a m. (Applicative m, IsEType (Impl m) a) => Term (Impl m) a -> m Text
compile' (Term t) = (,) <$> runImpl t SN <*> pure (typeInfo (Proxy @m) (Proxy @a) SN)

compile :: Compile EDSL (SFTerm, SFType)
compile t = let _unused = callStack in compile' t
