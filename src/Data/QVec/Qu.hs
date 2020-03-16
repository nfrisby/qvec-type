{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.QVec.Qu (
  -- *
  Qu (..),
  minusQu,
  negateQu,
  overQu,
  plusQu,
  recipQu,
  timesQu,
  -- *
  UnitCoercion (..),
  coerceUnit,
  reflUnitCoercion,
  symUnitCoercion,
  transUnitCoercion,
  -- *
  quDouble,
  quFloat,
  quInt,
  quInteger,
  quRational,
  -- *
  fromIntegerQu,
  fromRationalQu,
  realToFracQu,
  ) where

import           Data.QVec

newtype Qu (u :: QVec k) a = UnsafeQu a
  deriving (Eq, Ord)

infixl 7 `timesQu`

timesQu :: Num a => Qu u1 a -> Qu u2 a -> Qu (u1 :+: u2) a
timesQu (UnsafeQu l) (UnsafeQu r) = UnsafeQu (l * r)

infixl 7 `overQu`

overQu :: Fractional a => Qu u1 a -> Qu u2 a -> Qu (u1 :-: u2) a
overQu (UnsafeQu l) (UnsafeQu r) = UnsafeQu (l / r)

infixl 6 `plusQu`

plusQu :: Num a => Qu u a -> Qu u a -> Qu u a
plusQu (UnsafeQu l) (UnsafeQu r) = UnsafeQu (l + r)

infixl 6 `minusQu`

minusQu :: Num a => Qu u a -> Qu u a -> Qu u a
minusQu (UnsafeQu l) (UnsafeQu r) = UnsafeQu (l - r)

negateQu :: Num a => Qu u a -> Qu u a
negateQu (UnsafeQu x) = UnsafeQu (negate x)

recipQu :: Fractional a => Qu u a -> Qu (Inv u) a
recipQu (UnsafeQu x) = UnsafeQu (recip x)

data ShowQu a = Qu a
  deriving (Show)

instance (Nil ~ u, Show a) => Show (Qu u a) where
  showsPrec p (UnsafeQu x) = showsPrec p (Qu x)

deriving newtype instance (Nil ~ u, Num a) => Num (Qu u a)
deriving newtype instance (Nil ~ u, Fractional a) => Fractional (Qu u a)

fromIntegerQu :: Num a => Qu u Integer -> Qu u a
fromIntegerQu (UnsafeQu x) = UnsafeQu $ fromInteger x

fromRationalQu :: Fractional a => Qu u Rational -> Qu u a
fromRationalQu (UnsafeQu x) = UnsafeQu $ fromRational x

realToFracQu :: (Real a, Fractional b) => Qu u a -> Qu u b
realToFracQu (UnsafeQu x) = UnsafeQu $ realToFrac x

quRational :: Qu u Rational -> Qu u Rational
quRational = id

quInteger :: Qu u Integer -> Qu u Integer
quInteger = id

quInt :: Qu u Int -> Qu u Int
quInt = id

quDouble :: Qu u Double -> Qu u Double
quDouble = id

quFloat :: Qu u Float -> Qu u Float
quFloat = id

data UnitCoercion (u1 :: QVec k) (u2 :: QVec k) = UnsafeUnitCoercion

reflUnitCoercion :: UnitCoercion u u
reflUnitCoercion = UnsafeUnitCoercion

symUnitCoercion :: UnitCoercion u1 u2 -> UnitCoercion u2 u1
symUnitCoercion UnsafeUnitCoercion = UnsafeUnitCoercion

transUnitCoercion :: UnitCoercion u1 u -> UnitCoercion u u2 -> UnitCoercion u1 u2
transUnitCoercion UnsafeUnitCoercion UnsafeUnitCoercion = UnsafeUnitCoercion

coerceUnit :: UnitCoercion u1 u2 -> Qu u a -> Qu (u :-: u1 :+: u2) a
coerceUnit UnsafeUnitCoercion (UnsafeQu x) = UnsafeQu x
