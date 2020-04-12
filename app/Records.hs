{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fplugin=Plugin.QVec #-}

{-# OPTIONS_GHC -Wwarn=missing-signatures #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Records (module Records) where

import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Typeable
import           GHC.Exts (Any)
import           GHC.Stack (HasCallStack)
import           Unsafe.Coerce (unsafeCoerce)

import           Defns

-- | A polymorphic variant, storing one of the types that occurs in
-- the index vector

newtype R (u :: QVec Type) = UnsafeR (Map TypeRep Any)

instance Show (R Nil) where show _ = "{}"

nilR :: R Nil
nilR = UnsafeR Map.empty

extR :: (Typeable a, FixCoord 0 1 a u ~ MkProved) => R u -> a -> R (u :+ a)
extR (UnsafeR m) a = UnsafeR $ Map.insert (typeOf a) (unsafeCoerce a) m

splitR :: (HasCallStack, Typeable a, FixCoord 0 1 a u ~ MkProved) => R (u :+ a) -> (a, R u)
splitR (UnsafeR m) = (a, UnsafeR (Map.delete (typeOf a) m))
  where
    a = case Map.lookup (typeOf a) m of
        Nothing -> error "impossible"
        Just x  -> unsafeCoerce x

main :: IO ()
main = do
  let r_bi = nilR `extR` Just False `extR` 7

      (b, r_i) = splitR r_bi
      (i, r_0) = splitR r_i

  print (i :: Int, b, r_0 :: R Nil)
