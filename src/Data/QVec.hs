{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE PolyKinds #-}
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
  BvN, 
  BvQ, 
  ) where

import           GHC.TypeNats (Nat)

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

-- | Basis vector addition

type family (:+) (v :: QVec k) (e :: k) :: QVec k where {}
infixl 7 :+

-- | Basis vector subtraction

type family (:-) (v :: QVec k) (e :: k) :: QVec k where {}
infixl 7 :-

-- | Scalar multiplication
--
-- This family is uninterpretable unless the naturals are both
-- literals and the denominator is non-zero.

type family ScQ (n :: Nat) (d :: Nat) (v :: QVec k) :: QVec k where {}

-- | Vector subtraction

type family (:-:) (v1 :: QVec k) (v2 :: QVec k) :: QVec k where {}
infixl 7 :-:

-- | Scalar multiplication (natural)

type family ScN (n :: Nat) (v :: QVec k) :: QVec k where {}

-- | Coefficient multiplication (rational)

type family BvQ (n :: Nat) (d :: Nat) (e :: k) :: QVec k where {}

-- | Coefficient multiplication (natural)

type family BvN (n :: Nat) (e :: k) :: QVec k where {}
