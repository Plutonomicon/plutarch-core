{-# LANGUAGE NoFieldSelectors #-}

module Examples.C (example) where

import Data.Functor.Identity (runIdentity)
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Type.Equality ((:~:) (Refl))
--import Plutarch.Backends.C (compileAp)
import Plutarch.Frontends.C
import Plutarch.Prelude
import Generics.SOP (NP ((:*), Nil))

pinc1 :: PC e => Term e (PProc '[PInt] PInt '[PC])
pinc1 = pmkProc \(x :* Nil) -> pure $ x + 1

pprint :: PC e => Term e (PProc '[PInt] PUnit '[PC, PCFFIProc "printf" '[PString, PInt] PUnit '[]])
pprint = pmkProc \(x :* Nil) -> do
  x' <- pcall pinc1 (x :* Nil)
  let printf = pFFIProc (Proxy @"printf")
  pcall printf ("some number %i\n" :* x' :* Nil)

pmain :: PC e => Term e PMain
pmain = pmkProc \Nil -> do
  _ <- punsafeFFIProc (Proxy @"printf") $ pcall pprint (5 :* Nil)
  pure 0

data PMyModule ef = PMyModule
  { pinc1 :: ef /$ PUnit
  }

example :: Text
example = undefined -- runIdentity $ compileAp (Proxy @PLib) plib
