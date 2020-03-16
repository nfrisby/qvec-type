{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -fplugin=Plugin.QVec #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Defns (
  module Defns,
  module Data.QVec,
  module Data.QVec.Qu,
  Proxy (..),
  ) where    

import           Data.Proxy (Proxy (..))

import           Data.QVec
import           Data.QVec.Qu

nuA :: (forall a. Proxy (a :: *) -> ()) -> ()
nuA _ = ()

nuB :: (forall b. Proxy (b :: *) -> ()) -> ()
nuB _ = ()

nuC :: (forall c. Proxy (c :: *) -> ()) -> ()
nuC _ = ()

nuD :: (forall d. Proxy (d :: *) -> ()) -> ()
nuD _ = ()

nuX :: (forall x. Proxy (x :: QVec *) -> ()) -> ()
nuX _ = ()

nuY :: (forall x. Proxy (x :: QVec *) -> ()) -> ()
nuY _ = ()

nuZ :: (forall x. Proxy (x :: QVec *) -> ()) -> ()
nuZ _ = ()

p0 :: Proxy 0
p0 = Proxy

p1 :: Proxy 1
p1 = Proxy

p2 :: Proxy 2
p2 = Proxy

p3 :: Proxy 3
p3 = Proxy

pList :: Proxy a -> Proxy [a]
pList _ = Proxy

pMaybe :: Proxy a -> Proxy (Maybe a)
pMaybe _ = Proxy

pNil :: Proxy Nil
pNil = Proxy

pBv1 :: Proxy e -> Proxy (Bv1 e)
pBv1 _ = Proxy

pBvN :: Proxy n -> Proxy e -> Proxy (BvN n e)
pBvN _ _ = Proxy

pBvQ :: Proxy n -> Proxy d -> Proxy e -> Proxy (BvQ n d e)
pBvQ _ _ _ = Proxy

pInv :: Proxy v -> Proxy (Inv v)
pInv _ = Proxy

pScN :: Proxy n -> Proxy v -> Proxy (ScN n v)
pScN _ _ = Proxy

pScQ :: Proxy n -> Proxy d -> Proxy v -> Proxy (ScQ n d v)
pScQ _ _ _ = Proxy

infixl 0 .~.

(.~.) :: Proxy a -> Proxy b -> Proxy (a ~ b)
_ .~. _ = Proxy

infixl 7 .-., .+., .+, .-

(.-.) :: Proxy v1 -> Proxy v2 -> Proxy (v1 :-: v2)
_ .-. _ = Proxy

(.+.) :: Proxy v1 -> Proxy v2 -> Proxy (v1 :+: v2)
_ .+. _ = Proxy

(.-) :: Proxy v -> Proxy e -> Proxy (v :- e)
_ .- _ = Proxy

(.+) :: Proxy v -> Proxy e -> Proxy (v :+ e)
_ .+ _ = Proxy

given :: prx c -> (c => ()) -> ()
given _ _ = ()

{-# NOINLINE wanted #-}

wanted :: c => prx c -> ()
wanted _ = ()

class Foo (v :: QVec k)

pFoo :: prx v -> Proxy (Foo v)
pFoo _ = Proxy

-----

-- | The SI base units with one exception.
--
--   * We use gram instead of kilogram.

data SIb =
      Sb | Mb | Gb | Ab | Kb | Molb | Cdb

-- | The SI base and derived units with three exceptions.
--
--   * We use gram instead of kilogram.
--
--   * We omit degrees Celsius because it cannot be defined as a
--     linear transformation of base SI units.
--
--   * We also include the SI prefix 'Deca' as a dimensionless
--     \"derived unit\"; this basis vector serves to collect all of
--     the various prefixes.

data SI =
      S | M | G | A | K | Mol | Cd
    |
      Rad | Sr | Hz | N | Pa | J
    |
      W | C | V | F | Ohm | Si
    |
      Wb | T | H | {- DegreesC | -} Lm | Lx
    |
      Bq | Gy | Sv | Kat
    |
      Deca

second :: Num a => Qu (Nil :+ S) a
second = UnsafeQu 1

meter :: Num a => Qu (Nil :+ M) a
meter = UnsafeQu 1

gram :: Num a => Qu (Nil :+ G) a
gram = UnsafeQu 1

ampere :: Num a => Qu (Nil :+ A) a
ampere = UnsafeQu 1

kelvin :: Num a => Qu (Nil :+ K) a
kelvin = UnsafeQu 1

mole :: Num a => Qu (Nil :+ Mol) a
mole = UnsafeQu 1

candela :: Num a => Qu (Nil :+ Cd) a
candela = UnsafeQu 1

radian :: Num a => Qu (Nil :+ Rad) a
radian = UnsafeQu 1

baseRadian :: UnitCoercion (Nil :+ Rad) Nil
baseRadian = UnsafeUnitCoercion

steradian :: Num a => Qu (Nil :+ Sr) a
steradian = UnsafeQu 1

baseSteradian :: UnitCoercion (Nil :+ Sr) Nil
baseSteradian = UnsafeUnitCoercion

hertz :: Num a => Qu (Nil :+ Hz) a
hertz = UnsafeQu 1

baseHertz :: UnitCoercion (Nil :+ Hz) (Nil :+ S)
baseHertz = UnsafeUnitCoercion

newton :: Num a => Qu (Nil :+ N) a
newton = UnsafeQu 1

baseNewton :: UnitCoercion (Nil :+ N) (BvN 3 Deca :+ G :+ M :- S :- S)
baseNewton = UnsafeUnitCoercion

pascal :: Num a => Qu (Nil :+ Pa) a
pascal = UnsafeQu 1

basePascal :: UnitCoercion (Nil :+ Pa) (BvN 3 Deca :+ G :- M :- S :- S)
basePascal = UnsafeUnitCoercion

joule :: Num a => Qu (Nil :+ J) a
joule = UnsafeQu 1

baseJoule :: UnitCoercion (Nil :+ J) (BvN 3 Deca :+ G :+ M :+ M :- S :- S)
baseJoule = UnsafeUnitCoercion

watt :: Num a => Qu (Nil :+ W) a
watt = UnsafeQu 1

baseWatt :: UnitCoercion (Nil :+ W) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S)
baseWatt = UnsafeUnitCoercion

coulomb :: Num a => Qu (Nil :+ C) a
coulomb = UnsafeQu 1

baseCoulomb :: UnitCoercion (Nil :+ C) (Nil :+ S :+ A)
baseCoulomb = UnsafeUnitCoercion

volt :: Num a => Qu (Nil :+ V) a
volt = UnsafeQu 1

baseVolt :: UnitCoercion (Nil :+ V) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S :- A)
baseVolt = UnsafeUnitCoercion

farad :: Num a => Qu (Nil :+ F) a
farad = UnsafeQu 1

baseFarad :: UnitCoercion (Nil :+ F) (Nil :-: BvN 3 Deca :- G :- M :- M :+: BvN 4 S :+ A :+ A)
baseFarad = UnsafeUnitCoercion

ohm :: Num a => Qu (Nil :+ Ohm) a
ohm = UnsafeQu 1

baseOhm :: UnitCoercion (Nil :+ Ohm) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S :- A :- A)
baseOhm = UnsafeUnitCoercion

siemens :: Num a => Qu (Nil :+ Si) a
siemens = UnsafeQu 1

baseSiemens :: UnitCoercion (Nil :+ Si) (Nil :-: BvN 3 Deca :- G :- M :- M :+: BvN 3 S :+ A :+ A)
baseSiemens = UnsafeUnitCoercion

weber :: Num a => Qu (Nil :+ Wb) a
weber = UnsafeQu 1

baseWeber :: UnitCoercion (Nil :+ Wb) (BvN 3 Deca :+ G :+ M :+ M :- S :- S :- A)
baseWeber = UnsafeUnitCoercion

telsa :: Num a => Qu (Nil :+ T) a
telsa = UnsafeQu 1

baseTelsa :: UnitCoercion (Nil :+ T) (BvN 3 Deca :+ G :- S :- S :- A)
baseTelsa = UnsafeUnitCoercion

henry :: Num a => Qu (Nil :+ H) a
henry = UnsafeQu 1

baseHenry :: UnitCoercion (Nil :+ H) (BvN 3 Deca :+ G :+ M :+ M :- S :- S :- A :- A)
baseHenry = UnsafeUnitCoercion

lumen :: Num a => Qu (Nil :+ Lm) a
lumen = UnsafeQu 1

baseLumen :: UnitCoercion (Nil :+ Lm) (Nil :+ Cd :+ Sr)
baseLumen = UnsafeUnitCoercion

lux :: Num a => Qu (Nil :+ Lx) a
lux = UnsafeQu 1

baseLux :: UnitCoercion (Nil :+ Lx) (Nil :- M :- M :+ Cd)
baseLux = UnsafeUnitCoercion

becquerel :: Num a => Qu (Nil :+ Bq) a
becquerel = UnsafeQu 1

baseBecquerel :: UnitCoercion (Nil :+ Bq) (Nil :- S)
baseBecquerel = UnsafeUnitCoercion

gray :: Num a => Qu (Nil :+ Gy) a
gray = UnsafeQu 1

baseGray :: UnitCoercion (Nil :+ Gy) (Nil :+ M :+ M :- S :- S)
baseGray = UnsafeUnitCoercion

sievert :: Num a => Qu (Nil :+ Sv) a
sievert = UnsafeQu 1

baseSievert :: UnitCoercion (Nil :+ Sv) (Nil :+ M :+ M :- S :- S)
baseSievert = UnsafeUnitCoercion

katal :: Num a => Qu (Nil :+ Kat) a
katal = UnsafeQu 1

baseKatal :: UnitCoercion (Nil :+ Kat) (Nil :+ Mol :- S)
baseKatal = UnsafeUnitCoercion

yotta    :: Num a => Qu (BvN 24 Deca) a
yotta    = UnsafeQu 1
perYotta :: Num a => Qu (Nil :-: BvN 24 Deca) a
perYotta = UnsafeQu $ 10^(24 :: Int)

zetta    :: Num a => Qu (BvN 21 Deca) a
zetta    = UnsafeQu 1
perZetta :: Num a => Qu (Nil :-: BvN 21 Deca) a
perZetta = UnsafeQu $ 10^(21 :: Int)

exa    :: Num a => Qu (BvN 18 Deca) a
exa    = UnsafeQu 1
perExa :: Num a => Qu (Nil :-: BvN 18 Deca) a
perExa = UnsafeQu $ 10^(18 :: Int)

peta    :: Num a => Qu (BvN 15 Deca) a
peta    = UnsafeQu 1
perPeta :: Num a => Qu (Nil :-: BvN 15 Deca) a
perPeta = UnsafeQu $ 10^(15 :: Int)

tera    :: Num a => Qu (BvN 12 Deca) a
tera    = UnsafeQu 1
perTera :: Num a => Qu (Nil :-: BvN 12 Deca) a
perTera = UnsafeQu $ 10^(12 :: Int)

giga    :: Num a => Qu (BvN 9 Deca) a
giga    = UnsafeQu 1
perGiga :: Num a => Qu (Nil :-: BvN 9 Deca) a
perGiga = UnsafeQu $ 10^(9 :: Int)

mega    :: Num a => Qu (BvN 6 Deca) a
mega    = UnsafeQu 1
perMega :: Num a => Qu (Nil :-: BvN 6 Deca) a
perMega = UnsafeQu $ 10^(6 :: Int)

kilo    :: Num a => Qu (Nil :+: BvN 3 Deca) a
kilo    = UnsafeQu 1
perKilo :: Num a => Qu (Nil :-: BvN 3 Deca) a
perKilo = UnsafeQu $ 10^(3 :: Int)

hecto    :: Num a => Qu (Nil :+ Deca :+ Deca) a
hecto    = UnsafeQu 1
perHecto :: Num a => Qu (Nil :- Deca :- Deca) a
perHecto = UnsafeQu $ 10^(2 :: Int)

deca    :: Num a => Qu (Nil :+ Deca) a
deca    = UnsafeQu 1
perDeca :: Num a => Qu (Nil :- Deca) a
perDeca = UnsafeQu (10^(1 :: Int))

deci    :: Num a => Qu (Nil :- Deca) a
deci    = UnsafeQu 1
deciPer :: Num a => Qu (Nil :+ Deca) a
deciPer = UnsafeQu (10^(1 :: Int))

centi    :: Num a => Qu (Nil :- Deca :- Deca) a
centi    = UnsafeQu 1
centiPer :: Num a => Qu (Nil :+ Deca :+ Deca) a
centiPer = UnsafeQu (10^(2 :: Int))

milli    :: Num a => Qu (Nil :-: BvN 3 Deca) a
milli    = UnsafeQu 1
milliPer :: Num a => Qu (Nil :-: BvN 3 Deca) a
milliPer = perKilo

micro    :: Num a => Qu (Nil :-: BvN 6 Deca) a
micro    = UnsafeQu 1
microPer :: Num a => Qu (Nil :-: BvN 6 Deca) a
microPer = perMega

nano    :: Num a => Qu (Nil :-: BvN 9 Deca) a
nano    = UnsafeQu 1
nanoPer :: Num a => Qu (Nil :-: BvN 9 Deca) a
nanoPer = perGiga

pico    :: Num a => Qu (Nil :-: BvN 12 Deca) a
pico    = UnsafeQu 1
picoPer :: Num a => Qu (Nil :-: BvN 12 Deca) a
picoPer = perTera

femto    :: Num a => Qu (Nil :-: BvN 15 Deca) a
femto    = UnsafeQu 1
femtoPer :: Num a => Qu (Nil :-: BvN 15 Deca) a
femtoPer = perPeta

atto    :: Num a => Qu (Nil :-: BvN 18 Deca) a
atto    = UnsafeQu 1
attoPer :: Num a => Qu (Nil :-: BvN 18 Deca) a
attoPer = perExa

zepto    :: Num a => Qu (Nil :-: BvN 21 Deca) a
zepto    = UnsafeQu 1
zeptoPer :: Num a => Qu (Nil :-: BvN 21 Deca) a
zeptoPer = perZetta

yocto    :: Num a => Qu (Nil :-: BvN 24 Deca) a
yocto    = UnsafeQu 1
yoctoPer :: Num a => Qu (Nil :-: BvN 24 Deca) a
yoctoPer = perYotta

-----

speedOfLight :: Num a => Qu (Nil :+ M :- S) a
speedOfLight = UnsafeQu 299792458

gravitationalConstant ::
    Fractional a =>
    Qu (Nil :+: BvN 3 M :-: BvN 3 Deca :- G :- S :- S) a
gravitationalConstant = UnsafeQu 6.6743015e-11

planckConstant :: _
planckConstant = quRational 6.62607015e-34 `timesQu` joule `timesQu` second

electricConstant :: Fractional a => Qu (Nil :+ F :- M) a
electricConstant = UnsafeQu 8.854187812813e-12

boltzmannConstant :: _
boltzmannConstant = quRational 1.380649e-23 `timesQu` joule `overQu` kelvin

-----

planckMass :: Fractional a => Qu (BvN 3 Deca :+ G) a
planckMass = UnsafeQu 2.17643524e-8

-----

avogadroNumber :: Num a => Qu (Nil :- Mol) a
avogadroNumber = UnsafeQu $ 602214076 * 10^(15 :: Int)

idealGasConstant :: _
idealGasConstant = quRational 8.31446261815324 `timesQu` joule `overQu` kelvin `overQu` mole
