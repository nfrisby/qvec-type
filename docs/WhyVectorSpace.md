This document explains why we chose to work with vector spaces.

# Background

First, some context. Our initial objective is to use strong types to
ensure that our calculations respect units of measure. This
necessitates some basics. To keep this discussion simple, I'll assume
we're only interested in SI base units and `Rational` magnitudes.

```
data U = ...  -- to be determined

-- | A quantity is a magnitude tagged with the units @u@
newtype Qu (u :: U) = UnsafeQu Rational

zeroQu :: Qu u
zeroQu = UnsafeQu 0

scalarQu :: Rational -> Qu One
scalarQu = UnsafeQu

plusQu :: Qu u -> Qu u -> Qu u
plusQu (UnsafeQu x) (UnsafeQu y) = UnsafeQu (x + y)

timesQu :: Num => Qu u1 -> Qu u2 -> Qu (u1 :*: u2)
timesQu (UnsafeQu x) (UnsafeQu y) = UnsafeQu (x * y)

recipQu :: Qu u -> Qu (Inv u)
recipQu (UnsafeQu x) = UnsafeQu (recip x)

sqrt :: Qu (u :*: u) -> Qu u
sqrt (UnsafeQu x) = UnsafeQu (realToFrac (sqrt $ fromRational x :: Double))
```

We'll also need some way to introduce units themselves.

```
data SI = S | M | Kg | A | K | Mol | Cd

second :: Qu (Iota S)
second = UnsafeQu 1

meter :: Qu (Iota M)
meter = UnsafeQu 1

-- and so on
```

So we already see that we need at least the following signature for
@U@.

```
One :: U               -- The unit element

(:*:) :: U -> U -> U   -- Multiplication

Inv :: U -> U -> U     -- Multiplicative Inverse

Iota :: SI -> U        -- Embed a base unit
```

Because `Rational` is an [Abelian
group](https://en.wikipedia.org/wiki/Abelian_group), our kind `U` must
also be. For example, if `timesQu` is associative, then so must be
`:*:`; how could `timesQu x y` and `timesQu y x` be equivalent unless
their types `Qu (a :+: b)` and `Qu (b :+: a)` were too? Lastly,
because our signature includes one constant per value of `SI` and each
such constant is only ever equal to itself, the desired semantics of
`Iota` makes `U` a [free Abelian
group](https://en.wikipedia.org/wiki/Free_abelian_group).

# Motivating Example

Now that we've identified the signature and its expected equational
theory, we can consider a particular example equation.

```
(x :*: x) ~ (y :*: y :*: y)
```

By associativity, we can rewrite the above using exponents. Such
exponents will always be integers, since all we're doing is collating
multiple occurrences of a unit variable (some positive and some
negative). (Additionally, those occurrences don't even need to be
adjacent, because of commutativity.)

```
x^2 ~ y^3   (1)
```

It is immediately tempting to conclude that `x = y^(3/2)` and `y =
x^(2/3)`. But those righthand-sides are not valid types inhabiting the
kind `U`, since `U`s signature has no way to multiply together
three-and-a-half copies of `x`! Recall that our exponents are limited
to integers.

That doesn't mean this equation is invalid. If we introduce a fresh
variable, we can simplify the equation somewhat by rewriting it in
[parametric form](https://en.wikipedia.org/wiki/Parametric_equation).

```
   x^2 ~ y^3

       <=>

   exists z. (x ~ z^3, y ~ z^2)   (2)
```

We will not ultimately use this approach, but we discuss it briefly
and later refer to it because it can be an illuminating alternative
perspective on the semantics of the original equation.

By back substituting the definitions from Equation (2) into Equation
(1), we see `z^6` on both sides, so it's a valid solution. Since `z ::
U` can only have integer exponents, the statement `exists z. x ~ z^3`
by itself merely requires that every exponent in `x` is divisible by
3. Similarly every exponent in `y` must be divisible by 2. This
observation relates to [Diophantine
equations](https://en.wikipedia.org/wiki/Diophantine_equation) and
[quantifier
elimination](https://en.wikipedia.org/wiki/Quantifier_elimination).

It may be helpful to elaborate what is meant by "the exponents in
`x`", ie exactly which exponents must be divisible by 3. Suppose that
a program involving this equation ends up passing the type checker
(and the type `x` was actually relevant). If so, then `x` will at some
point have been identified as seven specific exponents, one per base
unit in `SI` (some may be 0) -- say, `x ~ (Iota Kg :*: Inv (Iota M ^
3))` for a density, ie `(0,-3,1,0,0,0,0)`. In other words, `U` is
ultimately isomorphic to a sequence of length seven, in which each
element is a exponent of one of the seven base SI units. It is these
exponents that must all be divisible by 3 in order for `y ~ x^(2/3)`
to be a valid definition of `y :: U`.

Thus we see that Equation (1) implicitly requires that `x`'s exponents
are divisible by 3 and `y`'s are divisible by 2, while Equation (1)
obviously also explicitly requires a corresondence between each
exponent `x` and the corresponding exponent in `y`. And while the
divisiblity constraints have become (more) explicit in Equation (2),
the `x` and `y` correspondence has become (more) implicit: it is now
only realized because the same _shared_ variable `z` occurs in both
nested equations.

Requiring a fresh variable `z` is burdensome -- it'd be nicer if we
could make do with just the variables we already have. Moreover, in
our specific case of a GHC typechecker plugin, some invocation of the
plugin -- when simplifying Givens -- do not allow it to introduce
fresh variables. I'm not sure, but I suspect this is ultimately an
artificial restriction that only serves to simplify the design of the
GHC constraint solver, as opposed to a more fundamental restriction.
Even if the plugin could introduce a fresh skolem type variable, it
might be confusing for the user to see it in error messages, for
example. And I'd personally rather not disturb the innards of GHC's
constraint solver proper if we don't need to.

# Generalize to Simplify

Since the typechecker plugin cannot always introduce fresh variables,
we need an alternative to the Diophantine/parameteric form
approach. Let's reconsider our goal.

We're attempting to solve the following equation, where `x` and `y`
both inhabit `U`.

```
x^2 ~ y^3   (1)
```

Since the signature of `U` only permits integer exponents, we cannot
use either of the "obvious" equations `x = y^(3/2)` or `y = x^(2/3)`.
If we could always introduce a fresh variable, then we could use
Equation (2) to get similar equations `x = z^3` and `y = z^2`. But we
(currently) cannot and might prefer not to even if we could.

We'd like to replace Equation (1) with either of the "obvious"
solutions or the pair of equations in terms of `z` because they can be
utilized as substitution mappings for `x` and/or `y`. The primary
concrete consequence of equality constraints in the GHC constraint
solver is variable elimination through substitution. If Equation (1)
is a Derived or Wanted constraint and we're able to rearrange it to
isolate a unification variable on the lefthand-side, then -- various
checks permitting -- we can assign that variable to be the
righthand-side. This discharges the equality and also (eventually)
removes that unification variable from the rest of the constraints. If
the equation is instead a Given constraint, then -- various checks
permitting -- it is used to rewrite each other constraint, replacing
any occurences of the variable isolated on the lefthand-side by the
type on righthand-side. The variable will eventually only occur on the
lefthand-side of the Given constraint that "defines" it. The
bottom-line is that any useful equality constraint will eliminate one
variable by substituting some type for it. This propagates all
information known about what type the variable represents so that that
information is now manifest within each constraint in which the
variable had occurred. This enables local reasoning to potentially
further simplify those constraints.

The above is quite similar to the un-optimization version of
[https://en.wikipedia.org/wiki/Gaussian_elimination](Gaussian
elimination) algorithm: [the elimination (of variables)
method](https://en.wikipedia.org/wiki/System_of_linear_equations#Elimination_of_variables).
To solve a system of linear equations: pick one, rearrange it to be a
definition of one of the unknowns in terms of the others, and then
back substitute that definition into all the other equations. Repeat
until you have a definition for every unknown or else run out of
equations because some were revealed as redundant during this process.
The crucial step is rearranging the equation into a definition. In
Gaussian elimination, this is always possible because we're working in
a vector space. This means the coefficients are fields, which means
they always have a multiplicative inverse. IE `2/3` and `3/2` are
valid coefficients, or in our case would be valid exponents: `x =
y^(3/2)` or `y = x^(2/3)`. The back substitution step is indeed what
the GHC constraint solver already does for equations where an
acceptable variable is isolated on the lefthand-side.

The comparison between GHC's solver and the classic Gaussian
elimination algorithm suggests what appears to be the simplest
alternative: merely add scalar multiplication by a rational to our
signature in order to make `U` a vector space. This enables us to
rearrange any equation into a definition of any `U` variable that
occurs in it.

```
-- Scalar Multiplication
ScQ :: Rational -> U
```

We can therefore simplify Equation (1) to either `x = y^(3/2)` or `y =
x^(2/3)`. We choose whichever GHC would prefer (cf
`TcUnify.swapOverTyVars`) or else arbitrarily (but still
deterministically).

The process applies just as well to equations with more than two
variables. Each (successful) equality constraint ultimately defines
one variable in terms of those remaining, and so -- just like Gaussian
elimination -- if there are enough equations then all variables will
eventually be solved. Notably, the order in which the equations are
treated does not matter, which is helpful because a plugin may not be
able to control the order.

# Recovering Diophantine Solutions

It is possible some use-cases/users will ultimately prefer for the
constants' exponents to be integers after all. As was made most
explicit in the Diophantine/parameteric form approach, the key
ingredient is a divisibility constraint on the constant's exponents.
We can add that along-side our vector space signature for users to
opt-in to.

```
DividesExponents :: Natural -> U -> Constraint
```

Based on previous experience, I anticipate that, because this
constraint is not a compositional property (ie `DividesExponents n (u1
:*: u2)` does not imply `(DividesExponents n u1, DividesExponents n
u2)`), it will be awkward to implement a complete decision procedure
for it. I'll write that up once it's finished.
