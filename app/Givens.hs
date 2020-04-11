{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fplugin=Plugin.QVec #-}

module Givens (main) where

import           Defns

main :: IO ()
main = do

    -- Nil :+ a :+ b ~ Nil :+ b :+ a
    pure $
      nuA $ \pA ->
      nuB $ \pB ->
      wanted (pNil .+ pA .+ pB .~. pNil .+ pB .+ pA)

    -- x :+: y ~ y :+: x
    pure $
      nuX $ \pX ->
      nuY $ \pY ->
      wanted (pX .+. pY .~. pY .+. pX)

    -- a ~ b => Nil ~ Nil :+ a :- b
    --
    -- I'm not sure why, but this test revealed the bug where
    -- unflattening an fmv didn't emit any constraint and so GHC
    -- stopped the loop before giving our flattening a chance to
    -- affect things.
    pure $
      nuA $ \pA ->
      nuB $ \pB ->
      given (pA .~. pB) $
      wanted (pNil .~. pNil .+ pA .- pB)

    -- x ~ y => Nil ~ x :-: y
    pure $
      nuX $ \pX ->
      nuY $ \pY ->
      given (pX .~. pY) $
      wanted (pNil .~. pX .-. pY)

    -- Foo (x :+: x) => Foo (ScN 2 x)
    --
    -- Requires canonicalizing fsks
    pure $
      nuX $ \pX ->
      given (pFoo (pX .+. pX)) $
      wanted (pFoo $ pScN p2 pX)

    pure $
      nuX $ \pX ->
      given (pFoo (pX .+. pX)) $
      test1 pX

    -- 2x ~ 3y => x ~ 3y/2
    --
    -- Requires the antiSwapMasquerade.
    pure $
      nuX $ \pX ->
      nuY $ \pY ->
      given (pScN p2 pX .~. pScN p3 pY) $ test2 pX pY

    -- 2x ~ 3y => x ~ 3y/2
    --
    -- Same as above, but the Given equality needs to be simplified
    -- even when all of its skolems are shallower than the current
    -- level. Motivates using the +100000 level trick for the
    -- antiSwapMasquerade.
    pure $ nuX $ \pX ->
      nuY $ \pY ->
      given (pX .+. pX .~. pScN p3 pY) $
      wanted (pX .~. pScQ p3 p2 pY)

    -- Nil :+ [a] :+ b ~ Nil :+ Maybe c :+ d
    --
    -- Requires improving the Given to yield a basis equivalence.
    pure $
      nuA $ \pA ->
      nuB $ \pB ->
      nuC $ \pC ->
      nuC $ \pD ->
      given (pNil .+ pList pA .+ pB .~. pNil .+ pMaybe pC .+ pD) $
      wanted (pD .~. pList pA) <>
      wanted (pB .~. pMaybe pC)

    -- FixCoord 2 Int (Bv1 a :- Char :+ Int)
    pure $
      nuA $ \pa ->
      given (pFixCoord p2 p1 pInt (pBv1 pa .- pChar .+ pInt) .~. pMkProved) $
      ()

    -- FixCoord 1 [Int] (Bv1 [a] :- Maybe b)
    pure $
      nuB $ \pb ->
      nuA $ \pa ->
      given (pFixCoord p1 p1 (pList pInt) (pBv1 (pList pa) .- pMaybe pb) .~. pMkProved) $
      ()

    -- G1 FixCoords 1 1 a x
    -- G2 x ~ Nil :+ b
    -- W1 a ~ b
    --
    -- The FixCoord substitution of G1 crucially reveals the
    -- improvement a ~ b from G2.
    pure $
      nuA $ \pa ->
      nuB $ \pb ->
      nuX $ \px ->
      given (pFixCoord p1 p1 pa px .~. pMkProved) $
      given (px .~. (pNil .+ pb)) $
      wanted (pa .~. pb)

    -- W1 FixCoord 1 1 a (Bv1 a)
    pure $
      nuA $ \pa ->
      wanted (pFixCoord p1 p1 pa (pBv1 pa) .~. pMkProved)

    -- G1 FixCoord 1 1 a x
    -- W1 FixCoord 2 1 a (x :+ a)
    pure $
      nuX $ \px ->
      nuA $ \pa ->
      given (pFixCoord p1 p1 pa px .~. pMkProved) $
      wanted (pFixCoord p2 p1 pa (px .+ pa) .~. pMkProved)

-- Foo (x :+: x) => Foo (ScN 2 x)
--
-- Requires canonicalizing fsks
test1 :: Foo (x :+: x) => Proxy x -> ()
test1 pX =
  wanted (pFoo $ pScN p2 pX)

-- Scn 2 x ~ ScN 3 y => x ~ ScQ 3 2 y
--
-- Requires rearranging a Given equality
test2 :: (ScN 2 x ~ ScN 3 y) => Proxy x -> Proxy y -> ()
test2 pX pY =
    wanted (pX .~. pScQ p3 p2 pY)
