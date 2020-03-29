{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.QVec.Qu (
  -- *
  Qu (..),
  minusQu,
  natPowerQu,
  negateQu,
  overQu,
  plusQu,
  qPowerQu,
  recipQu,
  timesQu,
  zeroQu,
  mkQu,
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
  -- *
  DefaultShowsUnitPriority,
  ShowUnit (..),
  ShowUnits (..),
  ShowsUnitPriority,
  mkShowsUnit,
  mkShowsUnitPriority,
  ) where

import           Data.List (sortOn)
import           Data.Proxy (Proxy (..))
import           GHC.Real (denominator, numerator)
import           GHC.Show (appPrec, appPrec1, showSpace)
import           GHC.TypeLits

import           Data.QVec

newtype Qu (u :: QVec k) a = UnsafeQu a
  deriving (Eq, Ord)

zeroQu :: Num a => Qu u a
zeroQu = UnsafeQu 0

mkQu :: a -> Qu u a
mkQu = UnsafeQu

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

natPowerQu :: (KnownNat n, Num a) => proxy n -> Qu u a -> Qu (ScN n u) a
natPowerQu n (UnsafeQu x) = UnsafeQu (x ^ natVal n)

qPowerQu ::
    (KnownNat n, KnownNat d, Floating a) =>
    nProxy n -> dProxy d -> Qu u a -> Qu (ScQ n d u) a
qPowerQu n d (UnsafeQu x) = UnsafeQu (x ** p)
  where
    p = fromInteger (natVal n) / fromInteger (natVal d)

-----

deriving newtype instance (Nil ~ u, Num a) => Num (Qu u a)
deriving newtype instance (Nil ~ u, Fractional a) => Fractional (Qu u a)

instance
  (Ord (ShowsUnitPriority k), ShowUnits (ToCoords u), Show a) =>
  Show (Qu (u :: QVec k) a) where
  showsPrec p (UnsafeQu x) =
      case srt $ showsUnits (Proxy :: Proxy (ToCoords u)) of
        [] -> showsPrec p x
        us -> showParen (p > appPrec) $
              foldl snoc (showsPrec appPrec1 x) us
          where
            snoc acc u = acc . showSpace . u 0
    where
      -- ascending by absolute magnitude, positives first
      srt = map snd . sortOn fst

-- | lesser means more leftmost

type family ShowsUnitPriority k

type DefaultShowsUnitPriority = (Rational, Rational)

class Ord (ShowsUnitPriority k) => ShowUnit (u :: k) where
  showsUnit         :: proxy u -> Rational -> Int -> ShowS
  showsUnitPriority :: proxy u -> Rational -> ShowsUnitPriority k

  default showsUnitPriority ::
      (ShowsUnitPriority k ~ DefaultShowsUnitPriority) =>
      proxy u -> Rational -> ShowsUnitPriority k
  showsUnitPriority = mkShowsUnitPriority 0

mkShowsUnitPriority ::
    (ShowsUnitPriority k ~ DefaultShowsUnitPriority) =>
    Rational -> proxy (u :: k) -> Rational -> ShowsUnitPriority k
mkShowsUnitPriority q1 _prx q = (q1, if q < 0 then abs q else negate (recip q))

class ShowUnits (coords :: Coords k) where
  showsUnits ::
      proxy coords ->
      [((ShowsUnitPriority k), Int -> ShowS)]

instance ShowUnits NilCoords where
  showsUnits _ = []

instance
  (ShowUnit u, KnownSign s, KnownNat n, KnownNat d, ShowUnits coords) =>
  ShowUnits (ConsCoords s n d u coords) where
  showsUnits _prx = (prio, u) : showsUnits (Proxy :: Proxy coords)
    where
      n = natVal (Proxy :: Proxy n) * case signVal (Proxy :: Proxy s) of
          Neg -> -1
          Pos -> 1
      d = natVal (Proxy :: Proxy d)

      q = fromInteger n / fromInteger d

      prio = showsUnitPriority (Proxy :: Proxy u) q
      u = showsUnit (Proxy :: Proxy u) q

mkShowsUnit :: (Int -> ShowS) -> proxy u -> Rational -> Int -> ShowS
mkShowsUnit base _prx q p
    | q == 1    = base p

    | d == 1    = showParen (p > expPrec) $
      base (expPrec+1)
    . (showString "^" . showsPrec 0 n)

    | otherwise = showParen (p > expPrec) $
      base (expPrec+1)
    . showString "^"
    .
      showParen True (showsPrec 0 n . showString "/" . showsPrec 0 d)
  where
    n = numerator q
    d = denominator q
    expPrec = 8

-----

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
