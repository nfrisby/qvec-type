{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

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

concreteCoords :: ConcreteCoords a => Proxy a -> ()
concreteCoords _ = ()

class ConcreteCoords (a :: Coords *)

instance ConcreteCoords NilCoords
instance ConcreteCoords coords => ConcreteCoords (ConsCoords sign n d k coords)

-----

-- | The SI base units with one exception.
--
--   * We use gram instead of kilogram.

data SIb =
      Sb | Mb | Gb | Ab | Kb | Molb | Cdb

-- | The SI base and derived units, with three exceptions
--
--   * We use gram instead of kilogram.
--
--   * We omit degrees Celsius because it cannot be defined as a
--     linear transformation of base SI units.
--
--   * We also include the SI prefix 'Deca' as a dimensionless
--     \"derived unit\"; this basis vector serves to collect all of
--     the various prefixes.
--
-- TODO add minute and hour?
--
-- TODO add hectare and liter and metric ton?
--
-- TODO add arc degree, arc minute, and arc second?
--
-- TODO add neper, bel, and decibel?
--
-- TODO add important irrationals, like pi?

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

-- This poor link is the only discussion I could find :(
-- <https://www.quora.com/Is-there-a-conventional-unit-ordering-in-the-International-System-of-Units-for-compound-units>

type instance ShowsUnitPriority SI = DefaultShowsUnitPriority

namedPriority :: Rational
namedPriority = -4

instance ShowUnit S where
  showsUnitPriority = mkShowsUnitPriority (-1)
  showsUnit = mkShowsUnit $ \_p -> showString "s"
second :: Num a => Qu (Nil :+ S) a
second = UnsafeQu 1
invSecond :: Num a => Qu (Nil :- S) a
invSecond = UnsafeQu 1

instance ShowUnit M where
  showsUnitPriority = mkShowsUnitPriority (-2)
  showsUnit = mkShowsUnit $ \_p -> showString "m"
meter :: Num a => Qu (Nil :+ M) a
meter = UnsafeQu 1
invMeter :: Num a => Qu (Nil :- M) a
invMeter = UnsafeQu 1

instance ShowUnit G where
  showsUnitPriority = mkShowsUnitPriority (-3)
  showsUnit = mkShowsUnit $ \_p -> showString "g"
gram :: Num a => Qu (Nil :+ G) a
gram = UnsafeQu 1
invGram :: Num a => Qu (Nil :- G) a
invGram = UnsafeQu 1

instance ShowUnit A where showsUnit = mkShowsUnit $ \_p -> showString "A"
ampere :: Num a => Qu (Nil :+ A) a
ampere = UnsafeQu 1
invAmpere :: Num a => Qu (Nil :- A) a
invAmpere = UnsafeQu 1

instance ShowUnit K where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "K"
kelvin :: Num a => Qu (Nil :+ K) a
kelvin = UnsafeQu 1
invKelvin :: Num a => Qu (Nil :- K) a
invKelvin = UnsafeQu 1

instance ShowUnit Mol where showsUnit = mkShowsUnit $ \_p -> showString "mol"
mole :: Num a => Qu (Nil :+ Mol) a
mole = UnsafeQu 1
invMole :: Num a => Qu (Nil :- Mol) a
invMole = UnsafeQu 1

instance ShowUnit Cd where showsUnit = mkShowsUnit $ \_p -> showString "cd"
candela :: Num a => Qu (Nil :+ Cd) a
candela = UnsafeQu 1
invCandela :: Num a => Qu (Nil :- Cd) a
invCandela = UnsafeQu 1

instance ShowUnit Rad where showsUnit = mkShowsUnit $ \_p -> showString "rad"
radian :: Num a => Qu (Nil :+ Rad) a
radian = UnsafeQu 1
invRadian :: Num a => Qu (Nil :- Rad) a
invRadian = UnsafeQu 1
baseRadian :: UnitCoercion (Nil :+ Rad) Nil
baseRadian = UnsafeUnitCoercion

instance ShowUnit Sr where showsUnit = mkShowsUnit $ \_p -> showString "sr"
steradian :: Num a => Qu (Nil :+ Sr) a
steradian = UnsafeQu 1
invSteradian :: Num a => Qu (Nil :- Sr) a
invSteradian = UnsafeQu 1
baseSteradian :: UnitCoercion (Nil :+ Sr) Nil
baseSteradian = UnsafeUnitCoercion

instance ShowUnit Hz where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Hz"
hertz :: Num a => Qu (Nil :+ Hz) a
hertz = UnsafeQu 1
invHertz :: Num a => Qu (Nil :- Hz) a
invHertz = UnsafeQu 1
baseHertz :: UnitCoercion (Nil :+ Hz) (Nil :+ S)
baseHertz = UnsafeUnitCoercion

instance ShowUnit N where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "N"
newton :: Num a => Qu (Nil :+ N) a
newton = UnsafeQu 1
invNewton :: Num a => Qu (Nil :- N) a
invNewton = UnsafeQu 1
baseNewton :: UnitCoercion (Nil :+ N) (BvN 3 Deca :+ G :+ M :- S :- S)
baseNewton = UnsafeUnitCoercion

instance ShowUnit Pa where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Pa"
pascal :: Num a => Qu (Nil :+ Pa) a
pascal = UnsafeQu 1
invPascal :: Num a => Qu (Nil :- Pa) a
invPascal = UnsafeQu 1
basePascal :: UnitCoercion (Nil :+ Pa) (BvN 3 Deca :+ G :- M :- S :- S)
basePascal = UnsafeUnitCoercion

instance ShowUnit J where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "J"
joule :: Num a => Qu (Nil :+ J) a
joule = UnsafeQu 1
invJoule :: Num a => Qu (Nil :- J) a
invJoule = UnsafeQu 1
baseJoule :: UnitCoercion (Nil :+ J) (BvN 3 Deca :+ G :+ M :+ M :- S :- S)
baseJoule = UnsafeUnitCoercion

instance ShowUnit W where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "W"
watt :: Num a => Qu (Nil :+ W) a
watt = UnsafeQu 1
invWatt :: Num a => Qu (Nil :- W) a
invWatt = UnsafeQu 1
baseWatt :: UnitCoercion (Nil :+ W) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S)
baseWatt = UnsafeUnitCoercion

instance ShowUnit C where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "C"
coulomb :: Num a => Qu (Nil :+ C) a
coulomb = UnsafeQu 1
invCoulomb :: Num a => Qu (Nil :- C) a
invCoulomb = UnsafeQu 1
baseCoulomb :: UnitCoercion (Nil :+ C) (Nil :+ S :+ A)
baseCoulomb = UnsafeUnitCoercion

instance ShowUnit V where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "V"
volt :: Num a => Qu (Nil :+ V) a
volt = UnsafeQu 1
invVolt :: Num a => Qu (Nil :- V) a
invVolt = UnsafeQu 1
baseVolt :: UnitCoercion (Nil :+ V) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S :- A)
baseVolt = UnsafeUnitCoercion

instance ShowUnit F where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "F"
farad :: Num a => Qu (Nil :+ F) a
farad = UnsafeQu 1
invFarad :: Num a => Qu (Nil :- F) a
invFarad = UnsafeQu 1
baseFarad :: UnitCoercion (Nil :+ F) (Nil :-: BvN 3 Deca :- G :- M :- M :+: BvN 4 S :+ A :+ A)
baseFarad = UnsafeUnitCoercion

instance ShowUnit Ohm where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Ω"
ohm :: Num a => Qu (Nil :+ Ohm) a
ohm = UnsafeQu 1
invOhm :: Num a => Qu (Nil :- Ohm) a
invOhm = UnsafeQu 1
baseOhm :: UnitCoercion (Nil :+ Ohm) (BvN 3 Deca :+ G :+ M :+ M :-: BvN 3 S :- A :- A)
baseOhm = UnsafeUnitCoercion

instance ShowUnit Si where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "S"
siemens :: Num a => Qu (Nil :+ Si) a
siemens = UnsafeQu 1
invSiemens :: Num a => Qu (Nil :- Si) a
invSiemens = UnsafeQu 1
baseSiemens :: UnitCoercion (Nil :+ Si) (Nil :-: BvN 3 Deca :- G :- M :- M :+: BvN 3 S :+ A :+ A)
baseSiemens = UnsafeUnitCoercion

instance ShowUnit Wb where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Wb"
weber :: Num a => Qu (Nil :+ Wb) a
weber = UnsafeQu 1
invWeber :: Num a => Qu (Nil :- Wb) a
invWeber = UnsafeQu 1
baseWeber :: UnitCoercion (Nil :+ Wb) (BvN 3 Deca :+ G :+ M :+ M :- S :- S :- A)
baseWeber = UnsafeUnitCoercion

instance ShowUnit T where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "T"
telsa :: Num a => Qu (Nil :+ T) a
telsa = UnsafeQu 1
invTelsa :: Num a => Qu (Nil :- T) a
invTelsa = UnsafeQu 1
baseTelsa :: UnitCoercion (Nil :+ T) (BvN 3 Deca :+ G :- S :- S :- A)
baseTelsa = UnsafeUnitCoercion

instance ShowUnit H where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "H"
henry :: Num a => Qu (Nil :+ H) a
henry = UnsafeQu 1
invHenry :: Num a => Qu (Nil :- H) a
invHenry = UnsafeQu 1
baseHenry :: UnitCoercion (Nil :+ H) (BvN 3 Deca :+ G :+ M :+ M :- S :- S :- A :- A)
baseHenry = UnsafeUnitCoercion

instance ShowUnit Lm where showsUnit = mkShowsUnit $ \_p -> showString "lm"
lumen :: Num a => Qu (Nil :+ Lm) a
lumen = UnsafeQu 1
invLumen :: Num a => Qu (Nil :- Lm) a
invLumen = UnsafeQu 1
baseLumen :: UnitCoercion (Nil :+ Lm) (Nil :+ Cd :+ Sr)
baseLumen = UnsafeUnitCoercion

instance ShowUnit Lx where showsUnit = mkShowsUnit $ \_p -> showString "lx"
lux :: Num a => Qu (Nil :+ Lx) a
lux = UnsafeQu 1
invLux :: Num a => Qu (Nil :- Lx) a
invLux = UnsafeQu 1
baseLux :: UnitCoercion (Nil :+ Lx) (Nil :- M :- M :+ Cd)
baseLux = UnsafeUnitCoercion

instance ShowUnit Bq where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Bq"
becquerel :: Num a => Qu (Nil :+ Bq) a
becquerel = UnsafeQu 1
invBecquerel :: Num a => Qu (Nil :- Bq) a
invBecquerel = UnsafeQu 1
baseBecquerel :: UnitCoercion (Nil :+ Bq) (Nil :- S)
baseBecquerel = UnsafeUnitCoercion

instance ShowUnit Gy where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Gy"
gray :: Num a => Qu (Nil :+ Gy) a
gray = UnsafeQu 1
invGray :: Num a => Qu (Nil :- Gy) a
invGray = UnsafeQu 1
baseGray :: UnitCoercion (Nil :+ Gy) (Nil :+ M :+ M :- S :- S)
baseGray = UnsafeUnitCoercion

instance ShowUnit Sv where
  showsUnitPriority = mkShowsUnitPriority namedPriority
  showsUnit = mkShowsUnit $ \_p -> showString "Sv"
sievert :: Num a => Qu (Nil :+ Sv) a
sievert = UnsafeQu 1
invSievert :: Num a => Qu (Nil :- Sv) a
invSievert = UnsafeQu 1
baseSievert :: UnitCoercion (Nil :+ Sv) (Nil :+ M :+ M :- S :- S)
baseSievert = UnsafeUnitCoercion

instance ShowUnit Kat where showsUnit = mkShowsUnit $ \_p -> showString "kat"
katal :: Num a => Qu (Nil :+ Kat) a
katal = UnsafeQu 1
invKatal :: Num a => Qu (Nil :- Kat) a
invKatal = UnsafeQu 1
baseKatal :: UnitCoercion (Nil :+ Kat) (Nil :+ Mol :- S)
baseKatal = UnsafeUnitCoercion

instance ShowUnit Deca where
  showsUnit = mkShowsUnit $ \_p -> showString "10"
  showsUnitPriority = mkShowsUnitPriority (-1000000)

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
speedOfLight = 299792458 `timesQu` meter `timesQu` invSecond

gravitationalConstant ::
    Fractional a =>
    Qu (Nil :+: BvN 3 M :-: BvN 3 Deca :- G :- S :- S) a
gravitationalConstant =
    6.6743015e-11
      `timesQu` (meter `timesQu` meter `timesQu` meter)
      `overQu` (kilo `timesQu` gram)
      `overQu` (second `timesQu` second)

planckConstant :: _
planckConstant = quRational 6.62607015e-34 `timesQu` joule `timesQu` second

electricConstant :: Fractional a => Qu (Nil :+ F :- M) a
electricConstant = 8.854187812813e-12 `timesQu` farad `overQu` meter

boltzmannConstant :: _
boltzmannConstant = quRational 1.380649e-23 `timesQu` joule `overQu` kelvin

-----

planckMass :: Fractional a => Qu (BvN 3 Deca :+ G) a
planckMass = 2.17643524e-8 `timesQu` kilo `timesQu` gram

-----

avogadroNumber :: Num a => Qu (Nil :- Mol) a
avogadroNumber = (602214076 * 10^(15 :: Int)) `timesQu` invMole

idealGasConstant :: _
idealGasConstant = quRational 8.31446261815324 `timesQu` joule `overQu` kelvin `overQu` mole
