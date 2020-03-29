{- This module was hastily copied and adopted from https://github.com/adamgundry/uom-plugin/blob/98bdba5cc51fa2b952fdd05e02af4f20512f19fd/uom-plugin/tests/Tests.hs -}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin Plugin.QVec #-}

{-# OPTIONS_GHC -Wno-type-defaults #-}

module UomPluginTests where

import Data.QVec
import Data.QVec.Qu

import Data.List
import Data.Ratio ((%))

import Defns

type Kg = BvN 3 Deca :+ G

-- Some basic examples

infixl 6 *:, /:

infixl 5 +:, -:

mk :: a -> Qu (Nil :: QVec SI) a
mk = mkQu

(+:) :: Num a => Qu u a -> Qu u a -> Qu u a
(+:) = plusQu

(-:) :: Num a => Qu u a -> Qu u a -> Qu u a
(-:) = minusQu

(*:) :: Num a => Qu u1 a -> Qu u2 a -> Qu (u1 :+: u2) a
(*:) = timesQu

(/:) :: Fractional a => Qu u1 a -> Qu u2 a -> Qu (u1 :-: u2) a
(/:) = overQu

type Quantity a u = Qu (u :: QVec SI) a

myMass :: Quantity Double Kg
myMass = 65 *: kilo *: gram

gravityOnEarth :: Quantity Double (Nil :+ M :- S :- S)
gravityOnEarth = 9.808 *: meter *: invSecond *: invSecond

forceOnGround :: Quantity Double (Nil :+ N)
forceOnGround = coerceUnit (symUnitCoercion baseNewton) $ gravityOnEarth *: myMass

inMetresPerSecond :: a -> Quantity a (Nil :+ M :- S)
inMetresPerSecond = UnsafeQu

showQu ::
    (Ord (ShowsUnitPriority k), Show a, ShowUnits (ToCoords u)) =>
    Qu (u :: QVec k) a -> String
showQu = show

attract
    :: Fractional a
    => Quantity a Kg
    -> Quantity a Kg
    -> Quantity a (Nil :+ M)
    -> Quantity a (Nil :+ N)
attract
    (m1 :: Quantity a Kg)
    (m2 :: Quantity a Kg)
    (r :: Quantity a (Nil :+ M))
    = _G *: m1 *: m2 /: (r *: r) :: Quantity a (Nil :+ N)
  where
    _G = 6.67384e-11 *: newton *: meter *: meter /: (let kg = (kilo *: gram) in kg *: kg)

sum' :: [Quantity Double u] -> Quantity Double u
sum' = foldr (+:) zeroQu

mean :: [Quantity Double u] -> Quantity Double u
mean xs = sum' xs /: mk (genericLength xs)

foo :: Num a => Quantity a u -> Quantity a v -> Quantity a (u :+: v)
foo x y = x *: y +: y *: x

foo' :: Num a => Quantity a u -> Quantity a v -> Quantity a (u :+: v)
foo' = foo

{-
-- thanks to expipiplus1, https://github.com/adamgundry/uom-plugin/issues/14
angularSpeed :: Quantity Rational (Nil :+ Rad :- S)
angularSpeed = z x
  where x :: Quantity Rational (Nil :- S)
        x = undefined
-}

-- Check that the abelian group laws hold

associativity :: Quantity a (u :+: (v :+: w)) -> Quantity a ((u :+: v) :+: w)
associativity = id

commutativity :: Quantity a (u :+: v) -> Quantity a (v :+: u)
commutativity = id

unit :: Quantity a (u :+: Nil) -> Quantity a u
unit = id

inverse :: Quantity a (u :+: (Nil :-: u)) -> Quantity a Nil
inverse = id

inverse2 :: proxy b -> Quantity a (Bv1 b :-: Bv1 b) -> Quantity a Nil
inverse2 _ = id

-- Gingerly now...

-- w^-2 ~ kg^-2  =>  w ~ kg
f :: ((Nil :-: (ScN 2 w)) ~ (Nil :-: ScN 2 Kg))  => Quantity a w -> Quantity a Kg
f = id

-- u ~ v * w, v^2 ~ v  =>  u ~ w
g :: (u ~ (v :+: w), (ScN 2 v) ~ v) => Quantity a u -> Quantity a w
g = id

-- a*a ~ 1  =>  a ~ 1
givens :: ((a :+: a) ~ Nil) => Quantity Double a -> Quantity Double Nil
givens = id

-- a^2 ~ b^3, b^6 ~ 1 => a ~ 1
givens2 :: ((ScN 2 a) ~ (ScN 3 b), (ScN 6 b) ~ Nil) => Quantity Double a -> Quantity Double Nil
givens2 = id

-- a^2 ~ b^3, b^37 ~ 1 => b ~ 1
givens3 :: ((ScN 2 a) ~ (ScN 3 b), (ScN 37 b) ~ Nil) => Quantity Double b -> Quantity Double Nil
givens3 = id

-- in baf, c is uniquely determined to be a^3 (or b^2)
baz :: (a ~ (ScN 3 c), b ~ (ScN 2 c)) => Quantity Double a -> Quantity Double b -> Quantity Double c -> Int
baz _ _ _ = 3
baf :: ((ScN 2 a) ~ (ScN 3 b)) => Quantity Double a -> Quantity Double b -> Int
baf qa qb = baz qa qb undefined

-- Miscellaneous bits and bobs
{- TODO
-- Pattern splices are supported, albeit with restricted types
patternSplice :: Quantity Integer (Nil :+ M) -> Quantity Rational (Kg :- S) -> Bool
patternSplice [u| 2 m |] [u| 0.0 kg / s |] = True
patternSplice (1 *: meter) [u| 0.1 kg / s |] = True
patternSplice _          _                 = False
-}
-- Andrew's awkward generalisation example is accepted only with a
-- type signature, even with NoMonoLocalBinds
tricky
    :: forall a u . Num a
    => Quantity a u
    -> (Quantity a (u :+: (Nil :+ M)), Quantity a (u :+: Kg))
tricky x =
    let h :: Quantity a v -> Quantity a (u :+: v)
        h = (x *:)
    in (h (3 *: meter), h (5 *: kilo *: gram))

{- TODO this one fails on the ambiguity check since i is not a literal

-- Test that basic constraints involving exponentiation work
pow :: Quantity a (u :+: ScN i v) -> Quantity a (ScN i v :+: u)
pow = id

-}

-- This declares a synonym for Nil
type Dimensionless = Nil
dimensionless :: Quantity a Dimensionless -> Quantity a Nil
dimensionless = id


-- Runtime testsuite

-- 20200322 NSF: we don't actually test anything other than that this all compiles

main :: IO ()
main = defaultMain tests

defaultMain :: () -> IO ()
defaultMain = pure

type TestTree = ()
testGroup :: String -> [()] -> ()
testGroup _ _ = ()

testCase :: String -> () -> ()
testCase _ _ = ()

infix 1 @?=
(@?=) :: a -> a -> ()
_ @?= _ = ()

tests :: TestTree
tests = testGroup "uom-plugin"
  [ testGroup "Showing constants"
    [ testCase "show 3m"                 $ show (3 *: meter)               @?= "[u| 3 m |]"
    , testCase "show 3m/s"               $ show (3 *: meter /: second)     @?= "[u| 3 m / s |]"
    , testCase "show 3.2 s^2"            $ show (3.2 *: second *: second)  @?= "[u| 3.2 s^2 |]"
    , testCase "show 3.0 kg m^2 / m s^2" $ show (3.0 *: kilo *: gram *: meter *: meter /: meter *: second *: second)
                                                                           @?= "[u| 3.0 kg m / s^2 |]"
    , testCase "show 1"                  $ show (mk 1)                     @?= "[u| 1 |]"
    , testCase "show 1 s^-1"             $ show (1 /: second)              @?= "[u| 1 s^-1 |]"
    , testCase "show 2 1 / kg s"         $ show (2 *: milli *: invGram *: second)
                                                                           @?= "[u| 2 kg^-1 s^-1 |]"
    , testCase "show (1 % 2) kg"         $ show (quRational 0.5 *: kilo *: gram)
                                                                           @?= "[u| 0.5 kg |]"
    ]
  , testGroup "Basic operations"
    [ testCase "2 + 2"                   $ (2 *: second) +: (2 *: second)        @?= (4 *: second)
    , testCase "in m/s"                  $ inMetresPerSecond 5             @?= (5 *: meter *: invSecond)
    , testCase "mean"                    $ mean [ 2 *: newton, 4 *: newton ] @?= (3 *: newton)
    , testCase "tricky generalisation"   $ tricky (2 *: second)               @?= (6 *: meter *: second, 10 *: kilo *: gram *: second)
    , testCase "polymorphic zero"        $ zeroQu @?= (0 *: zeroQu *: meter)
    , testCase "polymorphic frac zero"   $ zeroQu @?= (0.0 *: newton *: invMeter)
    ]
  , testGroup "Literal 1 (*:) Quantity _ u"
    [ testCase "_ = Double"
        $ 1 *: ((1 *: meter) :: (Quantity Double (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Int"
        $ 1 *: ((1 *: meter) :: (Quantity Int (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Integer"
        $ 1 *: ((1 *: meter) :: (Quantity Integer (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Rational, 1 *: (1 *: meter)"
        $ 1 *: ((1 *: meter) :: (Quantity Rational (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Rational, mk (1 % 1) *: (1 *: meter)"
        $ mk (1 % 1) *: ((1 *: meter) :: (Quantity Rational (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Rational, 1 *: [u| 1 % 1 m |]"
        $ 1 *: ((mk (1 % 1) *: meter) :: (Quantity Rational (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Rational, mk (1 % 1) *: [u| 1 % 1 m |]"
        $ mk (1 % 1) *: ((mk (1 % 1) *: meter) :: (Quantity Rational (Nil :+ M))) @?= (1 *: meter)
    ]
  , testGroup "(1 :: Quantity _ Nil) (*:) Quantity _ u"
    [ testCase "_ = Double"
        $ (1 :: Quantity Double Nil) *: ((1 *: meter) :: (Quantity Double (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Int"
        $ (1 :: Quantity Int Nil) *: ((1 *: meter) :: (Quantity Int (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Integer"
        $ (1 :: Quantity Integer Nil) *: ((1 *: meter) :: (Quantity Integer (Nil :+ M))) @?= (1 *: meter)
    , testCase "_ = Int"
        $ (1 :: Quantity Rational Nil) *: ((1 *: meter) :: (Quantity Rational (Nil :+ M))) @?= (1 *: meter)
    ]
  , {- testGroup "errors when a /= b, (1 :: Quantity a Nil) (*:) Quantity b u"
    [ testGroup "b = Double"
      [ testCase "a = Int" $ op_a1 `throws` opErrors "Double" "Int" "Int"
      , testCase "a = Integer" $ op_a2 `throws` opErrors "Double" "Integer" "Integer"
      , testCase "a = Rational" $ op_a3 `throws` opErrors "Double" "GHC.Real.Ratio Integer" "Rational"
      ]
    , testGroup "b = Int"
      [ testCase "a = Double" $ op_b1 `throws` opErrors "Int" "Double" "Double"
      , testCase "a = Integer" $ op_b2 `throws` opErrors "Int" "Integer" "Integer"
      , testCase "a = Rational" $ op_b3 `throws` opErrors "Int" "GHC.Real.Ratio Integer" "Rational"
      ]
    , testGroup "b = Integer"
      [ testCase "a = Double" $ op_c1 `throws` opErrors "Integer" "Double" "Double"
      , testCase "a = Int" $ op_c2 `throws` opErrors "Integer" "Int" "Int"
      , testCase "a = Rational" $ op_c3 `throws` opErrors "Integer" "GHC.Real.Ratio Integer" "Rational"
      ]
    , testGroup "b = Rational"
      [ testCase "a = Double" $ op_d1 `throws` opErrors "GHC.Real.Ratio Integer" "Double" "Double"
      , testCase "a = Int" $ op_d2 `throws` opErrors "GHC.Real.Ratio Integer" "Int" "Int"
      , testCase "a = Integer" $ op_d3 `throws` opErrors "GHC.Real.Ratio Integer" "Integer" "Integer"
      ]
    ]
  , -} testGroup "showQu"
    [ testCase "myMass"         $ showQu myMass         @?= "65.0 kg"
    , testCase "gravityOnEarth" $ showQu gravityOnEarth @?= "9.808 m / s^2"
    , testCase "forceOnGround"  $ showQu forceOnGround  @?= "637.52 kg m / s^2"
    ]
  {- , -} {- testGroup "convert"
    [ testCase "10m in ft"     $ convert [u| 10m |]   @?= [u| 32.8 ft |]
    , testCase "5 km^2 in m^2" $ convert [u| 5km^2 |] @?= [u| 5000000 m m |]
    , testCase "ratio"         $ show (ratio [u| ft |] meter) @?= "[u| 3.28 ft / m |]"
    , testCase "100l in m^3"   $ convert [u| 100l |]   @?= [u| 0.1 m^3 |]
    , testCase "1l/m in m^2"   $ convert [u| 1l/m |]   @?= [u| 0.001 m^2 |]
    , testCase "1l/m in m^2"   $ convert [u| 1l/m |]   @?= [u| 0.001 m^2 |]
    , testCase "5l in ft^3"    $ convert [u| 5l   |]   @?= [u| 0.17643776 ft^3 |]
    , testCase "2000000l^2 in ft^3 m^3" $ convert [u| 2000000l^2 |] @?= [u| 70.575104 ft^3 m^3 |]
    , testCase "42 rad/s in s^-1" $ convert [u| 42 rad/s |] @?= [u| 42 s^-1 |]
    , testCase "2.4 l/h in m" $ convert [u| 2.4 l/ha |] @?= [u| 2.4e-7 m |]
    , testCase "1 m^4 in l m" $ convert [u| 1 m^4 |] @?= [u| 1000 l m |]
    ]
  , -} {- testGroup "errors"
    [ testCase "s/m ~ m/s"            $ mismatch1 `throws` mismatch1_errors
    , testCase "m + s"                $ mismatch2 `throws` mismatch2_errors
    , testCase "a ~ a  =>  a ~ kg"    $ given1 undefined `throws` given1_errors
    , testCase "a ~ b  =>  a ~ kg"    $ given2 undefined `throws` given2_errors
    , testCase "a^2 ~ b^3  =>  a ~ s" $ given3 undefined `throws` given3_errors
    ]
  , -} {- testGroup "read . show"
    [ testCase "3 m"     $ read (show [u| 3 m     |]) @?= [u| 3 m     |]
    , testCase "1.2 m/s" $ read (show [u| 1.2 m/s |]) @?= [u| 1.2 m/s |]
    , testCase "0"       $ read (show [u| 1       |]) @?= [u| 1       |]
    ]
  , -} {- testGroup "read normalisation"
    [ testCase "1 m/m"       $ read "[u| 1 m/m |]"       @?= [u| 1 |]
    , testCase "-0.3 m s^-1" $ read "[u| -0.3 m s^-1 |]" @?= [u| -0.3 m/s |]
    , testCase "42 s m s"    $ read "[u| 42 s m s |]"    @?= [u| 42 m s^2 |]
    ]
   -}
  ]

{-
-- | Assert that evaluation of the first argument (to WHNF) will throw
-- an exception whose string representation contains one of the given
-- lists of substrings.
throws :: a -> [[String]] -> Assertion
throws v xs =
    (evaluate v >> assertFailure "No exception!") `catch` \ (e :: SomeException) ->
        unless (any (all (`isInfixOf` show e)) xs) $ throw e
-}
