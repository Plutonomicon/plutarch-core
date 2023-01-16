module Main (main) where

import Data.Text.IO (writeFile)
import Examples.Nix qualified
import System.Directory (createDirectoryIfMissing)
import Prelude hiding (writeFile)

main :: IO ()
main = do
  createDirectoryIfMissing False "generated"
  writeFile "generated/p.nix" Examples.Nix.example
