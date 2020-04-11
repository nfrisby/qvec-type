module Main (main) where

import qualified CurrentTestCase
import qualified Givens
import qualified UomPluginTests
import qualified Variants
import qualified Wanteds

main :: IO ()
main = do
  CurrentTestCase.main
  Givens.main
  UomPluginTests.main
  Variants.main
  Wanteds.main
