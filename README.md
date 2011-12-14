inch
====

**Inch** is a type-checker for a subset of Haskell (plus some GHC extensions) with the addition of integer constraints. After successfully type-checking a source file, it outputs an operationally equivalent version with the type-level integers erased, so it can be used as a preprocessor in order to compile programs.

This is a very rough and ready prototype. Many Haskell features are missing or poorly implemented.


Installation
------------

    cabal install inch


Features
--------

* A new kind `Integer` for type-level integers, together with a synonym `Nat` for integers constrained to be nonnegative

* Type-level addition, subtraction, multiplication and exponentiation operations (plus a few more)

* Contexts contain numeric equality and inequality constraints

* Π-types (dependent functions from integers) inspired by the SHE preprocessor, which erase to the corresponding non-dependent functions

* Guards can test numeric constraints and make this information available for type-checking (as in `plan` below)

* Powerful type inference using a novel approach to equational unification (though type signatures are needed for GADT pattern matches and polymorphic recursion)


Example
-------

The following program defines a type of vectors (lists indexed by their length) and some functions using them. 

    {-# OPTIONS_GHC -F -pgmF inch #-}
    {-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

    data Vec :: * -> Nat -> * where
        VNil  :: Vec a 0
        VCons :: forall a (n :: Nat) . a -> Vec a n -> Vec a (n+1)
      deriving Show

    vreverse :: forall (n :: Nat) a . Vec a n -> Vec a n
    vreverse xs = vrevapp xs VNil
      where
        vrevapp :: forall (m n :: Nat) a . Vec a m -> Vec a n -> Vec a (m+n)
        vrevapp VNil         ys = ys
        vrevapp (VCons x xs) ys = vrevapp xs (VCons x ys)

    vec :: pi (n :: Nat) . a -> Vec a n
    vec {0}   a = VNil
    vec {n+1} a = VCons a (vec {n} a)

    vlookup :: forall (n :: Nat) a . pi (m :: Nat) . m < n => Vec a n -> a
    vlookup {0}   (VCons x _)  = x
    vlookup {k+1} (VCons _ xs) = vlookup {k} xs

    plan :: pi (n :: Nat) . Vec Integer n
    plan {0}           = VNil
    plan {m} | {m > 0} = VCons m (plan {m-1})

After type-checking and preprocecessing with `inch`, the resulting file is as follows.

    {-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

    data Vec :: * -> * where
        VNil  :: Vec a
        VCons :: a -> Vec a -> Vec a
      deriving Show

    vreverse :: Vec a -> Vec a
    vreverse xs = vrevapp xs VNil
      where
        vrevapp :: Vec a -> Vec a -> Vec a
        vrevapp VNil         ys = ys
        vrevapp (VCons x xs) ys = vrevapp xs (VCons x ys)

    vec :: Integer -> a -> Vec a n
    vec 0     a = VNil
    vec (n+1) a = VCons a (vec n a)

    vlookup :: Integer -> Vec a n -> a
    vlookup 0     (VCons x _)  = x
    vlookup (k+1) (VCons _ xs) = vlookup k xs

    plan :: Integer -> Vec Integer
    plan 0         = VNil
    plan m | m > 0 = VCons m (plan (m-1))

For more examples, look in the [examples directory](https://github.com/adamgundry/inch/tree/master/examples) of the source distribution. These include:

* More fun with vectors

* Merge sort that maintains length and ordering invariants

* Red-black tree insertion and deletion with ordering, colour and black height invariants guaranteed by types

* Time complexity annotations showing that red-black tree insert/delete are linear in the black height, plus a few other examples

* Units of measure with good type inference properties and (morally) no runtime overhead


Known limitations
-----------------

* Lots of Haskell features are unsupported, notably list comprehensions, `do` notation, `if` expressions, newtypes, field labels, ...

* The parser is somewhat idiosyncratic; look at the examples to figure out what syntax it accepts. Data types must be defined in GADT syntax, using a kind signature rather than a list of variables. Parsing of infix operators is almost but not entirely nonexistent, so they must usually be written prefix.

* Modules are poorly supported. A `.inch` file is generated when preprocessing a module, listing the identifiers it defines, and this file is looked up when the module is imported. Because preprocessing happens in reverse dependency order, manual intervention may be required to generate `.inch` files before they are needed (by loading dependencies in GHCi). Qualified names are not supported, so there will be problems if multiple modules bring the same name into scope.

* Type classes are not completely implemented: ambiguity checking and defaulting are lacking, superclasses are not taken into consideration when solving constraints, and the constraint solver is untested.

* No kind inference is performed, so type variables must be annotated with their kind if it is not `*`. This means explicit `forall`-bindings must be used in some type signatures. Type variables in instance declarations cannot be annotated, so they may only have kind `*` (at the moment).

* Only GADTs involving type-level numeric equalities are supported, not more general equations between types.

* Support for higher-rank types is limited.



Outstanding design issues
-------------------------

* Metavariables are solved using equational unification in the abelian group of integers with addition, which works well, but a better story about ambiguity is needed.

* Constraint solving is based on normalisation and a solver for Presburger arithmetic, so only linear constraints are guaranteed to be solved. Hard constraints can be dealt with by the user invoking higher-rank functions that add facts to the context. A better characterisation of solvable constraints would be nice.

* Exponentiation by a negative integer is possible but makes no sense.

* At the moment, `Nat` is just `Integer` (with a positivity constraint added when it is used in a type signature). Kind polymorphism and subkinding might allow more precise kinds to be given to arithmetic operations, including a correct kind for exponentiation. 

* `n+k`-patterns provide quite a nice syntax for defining dependent numeric functions, but they have been deprecated and removed from Haskell 2010, so perhaps an alternative should be found.

* Erasure for type classes involving numeric kinds is not yet properly specified.


Related work
------------

Iavor Diatchki is working on [TypeNats](http://hackage.haskell.org/trac/ghc/wiki/TypeNats), an extension to GHC that aims to support type-level natural numbers. He also implemented the [presburger](http://github.com/yav/presburger) package, which `inch` uses for constraint solving.

Conor McBride's [Strathclyde Haskell Enhancement](http://personal.cis.strath.ac.uk/~conor/pub/she/) is a preprocessor that supports Π-types and allows lifting algebraic data types (but not numeric types) to kinds. SHE inspired the braces syntax used in `inch`. These ideas (and more, including kind polymorphism) are being implemented in GHC: see [Giving Haskell a Promotion](http://research.microsoft.com/en-us/people/dimitris/fc-kind-poly.pdf) by Brent Yorgey, Stephanie Weirich, Julien Cretin, Simon Peyton Jones and Dimitrios Vytiniotis. 

Max Bolingbroke has implemented the new [Constraint kind](http://blog.omega-prime.co.uk/?p=127) in GHC. This kind is supported by `inch` but not erased, so it will only work if GHC support is present.

This work is inspired by Hongwei Xi's [Dependent ML](http://www.cs.bu.edu/~hwxi/DML/DML.html) and its successor [ATS](http://www.ats-lang.org/), which support type-level Presburger arithmetic.


Contact
-------

Adam Gundry, adam.gundry@strath.ac.uk