# Introduction

This is the beginning of my _n_-th attempt at a GHC typechecker plugin
providing something comparable to row polymorphism. This time I've
focused on a more expressive but less featureful foundation: the
equational theory of vector spaces.

This plugin extends GHC's constraint solver with E-unification
capabilities for the equational theory of a vector space with rational
coefficients. Considered as a data type, each such _Q-vector_ is a
multiset in which each multiplicity is a rational number (positive or
negative).

See `app/*.hs` for uncommented but suggestive examples.

# Major Caveat

The implementation currently only works with a GHC that has been
patched for Issue https://gitlab.haskell.org/ghc/ghc/issues/15147. In
particular, I've developed it against this exploratory commit
https://github.com/nfrisby/ghc/commit/b6c914a8a20df10eae65482cc5bea215c9f70393.

The plugin currently only simplifies equivalence constraints. This is
quite spartan, but proves out the core concept. In particular, it is
sufficient for a standard example: ergonomic static checking for a
data type for magnitudes that is indexed by the units
measure. (However the units are cannot yet be inspected at run-time.)

# Future Work

  * Add a type family that extracts the non-zero coefficients and
    their corresponding basis vector as an inspectable sequence type
    in a canonical order. This will allow run-time inspection of
    inferred units of measure, for example.

  * Add type classes that restrict the coefficients to interesting
    subsets of the rationals: integers (signed multisets), naturals
    (traditional multisets), binary digits (sets). This will allow for
    extensible anonymous type-indexed enumerations, product types, and
    sum types, for example; See
    https://github.com/nfrisby/frags/blob/develop/docs/README.md for
    what I intend to re-implement on this front.
