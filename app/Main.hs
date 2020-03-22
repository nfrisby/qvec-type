module Main (main) where

import qualified CurrentTestCase
import qualified Givens
import qualified UomPluginTests
import qualified Wanteds

main :: IO ()
main = do
  CurrentTestCase.main
  Givens.main
  UomPluginTests.main
  Wanteds.main
