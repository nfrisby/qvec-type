{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fplugin=Plugin.QVec #-}
{-# OPTIONS_GHC -Wwarn=partial-type-signatures #-}

module Wanteds (main) where

import           Defns

speed1 :: _
speed1 = quRational 100 `timesQu` meter `overQu` second

speed2 :: _
speed2 = quRational 200 `overQu` second `timesQu` meter

rate3 :: Proxy unit -> Qu (Nil :- S :+ unit) Rational
rate3 _ = UnsafeQu 300

main :: IO ()
main = do
    -- the units add up to Nil
    print $ map (\x -> plusQu speed1 x) [speed2]
    print $ map (\x -> plusQu speed1 x `timesQu` second `overQu` meter) [speed2]

    -- due to the MonomorphismRestriction, the unit is irrelevant
    --
    -- TODO why is this annotation needed?
    print $ let qu = UnsafeQu (1 :: Rational) in (qu `overQu` qu :: Qu (Nil :: QVec SI) Rational)

    -- the unit is inferred via the MonomorphismRestriction and the
    -- occurrences of z
    let z = UnsafeQu 1
    print (speed1 `timesQu` z :: Qu (Nil :: QVec SI) Rational)
    (plusQu speed1 (rate3 Proxy) `timesQu` z) `seq` pure ()

    print $ quInteger $ meter `timesQu` meter `timesQu` newton

    do
      let f s qu = putStrLn $ s <> " " <> show (quDouble $ fromRationalQu qu)
      f "speedOfLight" speedOfLight
      f "gravitationalConstant" gravitationalConstant
      f "planckConstant" planckConstant
      f "electricConstant" electricConstant
      f "boltzmannConstant" boltzmannConstant
      f "planckMass" planckMass
      f "avogadroNumber" avogadroNumber
      f "idealGasConstant" idealGasConstant

    print $ qPowerQu (Proxy :: Proxy 3) (Proxy :: Proxy 2) $ quDouble $
      10 `timesQu` newton `overQu` meter `overQu` meter

    -- test an SI identity
    putStr "R = N_A * k_B? "
    print $
      let nA = fromIntegerQu avogadroNumber `timesQu` nano
      in idealGasConstant `timesQu` micro `overQu` kilo == nA `timesQu` boltzmannConstant

    -- test an SI identity
    putStr "m_P^2 = h c / G? "
    print $   -- TODO why False? the RHS is a bit more than 4 times the LHS
      let lhs = planckMass `timesQu` planckMass
          rhs = planckConstant `timesQu` speedOfLight `overQu` gravitationalConstant
      in lhs == coerceUnit baseJoule rhs
