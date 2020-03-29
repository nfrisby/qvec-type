{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Vectors over the field of rationals, indexed by a type that
-- indexes the space's basis
--
-- The operators are all closed type families with no instances
-- because all of their semantics are given by the "Plugin.QVec"
-- typechecker plugin.

module Data.QVec (
  -- * Vector space signature
  QVec (Nil, Bv1),
  type (:+:),
  Inv,
  ScQ,
  -- * Abbreviations
  type (:-:),
  type (:+),
  type (:-),
  ScN, 
  BvQ, 
  BvN,
  -- * Conversion
  Coords (..),
  ToCoords,
  -- * Miscellany
  KnownSign (..),
  Sign (..),
  SSign (..),
  signVal,
  ) where

import           GHC.Generics (Generic)
import           Data.Data (Data)
import           Data.Type.Equality ((:~:) (..), TestEquality (..))
import           GHC.TypeLits

{------------------------------------------------------------------------------
    Signature
------------------------------------------------------------------------------}

-- | Vector space over the field of rationals

data QVec k =

    -- | The zero vector

    Nil

  |

    -- | The basis vector with the given index

    Bv1 k

-- | Vector addition

type family (:+:) (v1 :: QVec k) (v2 :: QVec k) :: QVec k where {}
infixl 7 :+:

-- | Additive inverse

type family Inv (v :: QVec k) :: QVec k where {}

-- | Scalar multiplication
--
-- This family is uninterpretable unless the naturals are both
-- literals and the denominator is non-zero.

type family ScQ (n :: Nat) (d :: Nat) (v :: QVec k) :: QVec k where {}

{------------------------------------------------------------------------------
    Abbreviations
------------------------------------------------------------------------------}

-- | Vector subtraction

type family (:-:) (v1 :: QVec k) (v2 :: QVec k) :: QVec k where {}
infixl 7 :-:

-- | Basis vector addition

type family (:+) (v :: QVec k) (e :: k) :: QVec k where {}
infixl 7 :+

-- | Basis vector subtraction

type family (:-) (v :: QVec k) (e :: k) :: QVec k where {}
infixl 7 :-

-- | Scalar multiplication (natural)

type family ScN (n :: Nat) (v :: QVec k) :: QVec k where {}

-- | Scalar multiplication of a basis vector (rational)

type family BvQ (n :: Nat) (d :: Nat) (e :: k) :: QVec k where {}

-- | Scalar multiplication of a basis vector (natural)

type family BvN (n :: Nat) (e :: k) :: QVec k where {}

{------------------------------------------------------------------------------
    Conversion
------------------------------------------------------------------------------}

-- | Basis coordinates of a vector
--
-- We use GHC's arbitrary-but-deterministic internal total order over
-- concrete types, which ensures the basis is an /ordered/ /basis/
-- once the indices are sufficiently concrete.

data Coords k =

      -- | The coordinates of the empty vector

      NilCoords

    |

      -- | The /next/ non-zero coordinate
      --
      -- INVARIANT: the numerator and denominator are both not @0@.

      ConsCoords Sign Nat Nat k (Coords k)

type family ToCoords (v :: QVec k) :: Coords k where {}

data Sign = Neg | Pos
  deriving (Data, Eq, Generic, Ord, Show)

data SSign :: Sign -> * where
  SNeg :: SSign Neg
  SPos :: SSign Pos

class KnownSign (s :: Sign) where signSing :: SSign s

instance KnownSign Neg where signSing = SNeg
instance KnownSign Pos where signSing = SPos

signVal :: forall sign proxy. KnownSign sign => proxy sign -> Sign
signVal _prx = case signSing :: SSign sign of
    SNeg -> Neg
    SPos -> Pos

instance TestEquality SSign where
  testEquality SNeg SNeg = Just Refl
  testEquality SPos SPos = Just Refl
  testEquality _       _       = Nothing

instance Eq (SSign s) where
  _ == _ = True

instance Ord (SSign s) where
  compare _ _ = EQ

instance Show (SSign s) where
  show = \case
    SNeg -> "SNeg"
    SPos -> "SPos"
