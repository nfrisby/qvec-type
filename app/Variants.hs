{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fplugin=Plugin.QVec #-}

module Variants (module Variants) where

import           Data.Dynamic
import           GHC.Stack (HasCallStack)

import           Defns

-- | A polymorphic variant, storing one of the types that occurs in
-- the index vector

newtype V (u :: QVec *) = UnsafeV Dynamic
  deriving (Show)

mkV :: (Typeable a, FixCoord 1 1 a u ~ MkProved) => a -> V u
mkV = UnsafeV . toDyn

absurdV :: HasCallStack => V Nil -> a
absurdV _ = error "impossible!"

caseV :: (Typeable a, FixCoord 0 1 a u ~ MkProved) => (a -> r) -> (V u -> r) -> V (u :+ a) -> r
caseV hit miss (UnsafeV dyn) = case fromDynamic dyn of
    Just x  -> hit x
    Nothing -> miss (UnsafeV dyn)

infixr `caseV`

-----

readList' :: Read [a] => String -> [a]
readList' = read

readMaybe :: Read (Maybe a) => String -> Maybe a
readMaybe = read

testPrint =
    (\x -> print (x :: Int)) `caseV`
    (\x -> print (x :: Maybe Bool)) `caseV`
    (\x -> print (x :: String)) `caseV`
    absurdV

main :: IO ()
main = do
    testPrint $ mkV (readMaybe "Just True")
    testPrint $ mkV (readList' "\"Complete\"")
    testPrint $ mkV (3 :: Int)
