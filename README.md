Abstract
======

This is a short introduction into the technique of "compile-time testing", also known as program correctness proving.

I show why and how "compile-time testing" will be the solution for outstanding problems of programming. 

(The slides were presented at Prezi in 45 minutes on 11. Oct. 2013: http://www.ustream.tv/recorded/39746752)


Runtime vs. compile-time
========================

These activities can be done either in runtime (multiple times) or in compile-time (once):

-   Lexical and syntactic analysis, scope checking
     (done at runtime for some interpreted languages)
-   Type checking: dynamic vs. static type checking
-   Termination check
     cycle-in-spine and deadlock check in Haskell runtime
-   Testing: unit tests vs. correctness proof
    -   Exceptions
         array boundary check, null-pointer check, divide-by-zero exception, …
    -   Sanity check
         Is the input already sorted?

-   Garbage collection, stack overflow check, memory and time limit checks, …

Better to do them once in compile-time!

In Agda, it is possible to do all but the last ones in compile-time.

Outline
=======

-   Testing – live coding in Haskell
-   Informal proofs
-   Formal proofs – live coding in Agda

Testing
=======

Test the associativity of addition:

-   Unit test
-   Property test

*Live coding in Haskell*

Full Haskell code
=================

Pragmas

``` haskell
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
```

Imports

``` haskell
import Test.QuickCheck
import Test.SmallCheck
import Test.SmallCheck.Series

import Prelude hiding ((+))
```

Peano numbers

~~~~ {.sourceCode .literate .haskell}
data Nat :: * where
    Zero :: Nat
    Suc  :: Nat -> Nat
        deriving Show

instance Eq Nat where
  Zero  == Zero  = True
  Suc a == Suc b = a == b
  _     == _     = False

one, two, three, four :: Nat
one   = Suc Zero
two   = Suc one
three = Suc two
four  = Suc three

(+) :: Nat -> Nat -> Nat
Zero  + b = b
Suc a + b = Suc (a + b)
~~~~

Unit test

~~~~ {.sourceCode .literate .haskell}
assoc_unit :: Bool
assoc_unit =  (one + one) + two == one + (one + two)

assoc_unit' :: Bool
assoc_unit' =  assoc_prop one one two

assoc_prop :: Nat -> Nat -> Nat -> Bool
assoc_prop a b c =  (a + b) + c == a + (b + c)
~~~~

Property test (random)

~~~~ {.sourceCode .literate .haskell}
assoc_qc :: IO ()
assoc_qc = quickCheck assoc_prop

instance Arbitrary Nat where
    arbitrary = oneof [return Zero, fmap Suc arbitrary]
~~~~

Property test (systematic)

~~~~ {.sourceCode .literate .haskell}
assoc_sc :: IO ()
assoc_sc = smallCheck 5 assoc_prop

instance Monad m => Serial m Nat where
    series = cons0 Zero \/ cons1 Suc
~~~~

Informal proofs
===============

Statement (1)
=============

`assoc_unit` is `True`.

Proof by evaluation
===================

~~~~ {.sourceCode .literate .haskell}
      assoc_unit
  ~>  (one + one) + two == one + (one + two)          -- one
  ~>  (Suc Zero + one) + two == one + (one + two)     -- (+) Suc
  ~>  Suc (Zero + one) + two == one + (one + two)     -- (+) Suc
  ~>  Suc ((Zero + one) + two) == one + (one + two)
  ~>  ...
  ~>  Suc ((Zero + one) + two) == Suc (Zero + (one + two))  -- (==) Suc
  ~>  (Zero + one) + two == Zero + (one + two)   -- (+) Zero
  ~>  one + two == Zero + (one + two)            -- one
  ~>  Suc Zero + two == Zero + (one + two)       -- (+) Suc
  ~>  Suc (Zero + two) == Zero + (one + two)
  ~>  ...
  ~>  Suc (Zero + two) == Suc (Zero + two)    -- (==) Suc
  ~>  Zero + two == Zero + two
  ~>  ...
  ~>  True
~~~~

Statement (2)
=============

∀ `n :: Nat`, `m :: Nat`

~~~~ {.sourceCode .literate .haskell}
assoc_prop Zero n m  ~>  True
~~~~

Proof by evaluation of open expressions
=======================================

~~~~ {.sourceCode .literate .haskell}
      assoc_prop Zero n m
  ~>  (Zero + n) + m == Zero + (n + m)    -- (+) Zero
  ~>  n + m == Zero + (n + m)             -- (+) Zero
  ~>  n + m == n + m
~~~~

We stuck here, use the following lemma.

Remarks:

-   Evaluation of open expressions would not work if `(+)` was a black box
-   Works only for a specific definition of `(+)`

Statement (3)
=============

∀ `n :: Nat`

~~~~ {.sourceCode .literate .haskell}
refl n  ~>  True
~~~~

where

~~~~ {.sourceCode .literate .haskell}
refl :: Nat -> Bool
refl n = n == n
~~~~

Proof by case distinction
=========================

1st case:

~~~~ {.sourceCode .literate .haskell}
      refl Zero
  ~>  Zero == Zero
  ~>  True
~~~~

2nd case:

~~~~ {.sourceCode .literate .haskell}
      refl (Suc n')
  ~>  Suc n' == Suc n'
  ~>  n' == n'
  =   refl n'
~~~~

`refl` is constant `True` by induction.

Statement (4)
=============

∀ `n :: Nat`, `m :: Nat`, `k :: Nat`

~~~~ {.sourceCode .literate .haskell}
assoc_prop n m k  ~>  True
~~~~

Proof by case distinction
=========================

1st case:

~~~~ {.sourceCode .literate .haskell}
      assoc_prop Zero m k    -- statement (3)
  =   True
~~~~

2nd case:

~~~~ {.sourceCode .literate .haskell}
      assoc_prop (Suc n') m k
  ~>  (Suc n' + m) + k == Suc n' + (m + k)
  ~>  ...
  ~>  Suc ((n' + m) + k) == Suc (n' + (m + k))    -- (==) Suc
  ~>  (n' + m) + k == n' + (m + k)
  =   assoc_prop n' m k
~~~~

`assoc_prop` is constant `True` by induction.

Question
========

How could we formalize these statements and proofs?

-   Use as few language constructs as possible
-   Proof checking should be automatic

Solution
========

Use *types* for statement formalization and
*type checking* for prof checking!

~~~~ {.sourceCode .literate .haskell}
proof :: theorem
~~~~

The type system checks whether a proof matches a theorem.

Formal proofs
=============

*Live coding in Agda*

Agda code (prelude)
===================

``` agda
module Nat where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

one two three four : ℕ
one   = suc zero
two   = suc one
three = suc two
four  = suc three

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

data Bool : Set where
  true  : Bool
  false : Bool

_≟_ : ℕ → ℕ → Bool
zero  ≟ zero  = true
suc a ≟ suc b = a ≟ b
_     ≟ _     = false

infix 4 _≟_

assocProp : ℕ → ℕ → ℕ → Bool
assocProp a b c =  (a + b) + c ≟ a + (b + c)

reflProp : ℕ → Bool
reflProp n =  n ≟ n
```

Agda code (direct `isTrue`)
===========================

~~~~ {.sourceCode .literate .haskell}
  data isTrue : Bool → Set where
    ok : isTrue true

  unitTest : isTrue (assocProp one one two)
  unitTest = ok

  refl-True : (n : ℕ) → isTrue (reflProp n)
  refl-True zero = ok
  refl-True (suc n) = refl-True n

  assocProp-zero-True : (n m : ℕ) → isTrue (assocProp zero n m)
  assocProp-zero-True n m = refl-True (n + m)

  assocProp-True : (n m k : ℕ) → isTrue (assocProp n m k)
  assocProp-True zero    m k = assocProp-zero-True m k
  assocProp-True (suc n) m k = assocProp-True n m k
~~~~

Agda code (switch to `_≡_`)
===========================

~~~~ {.sourceCode .literate .haskell}
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

refl′ : {A : Set} {a : A} → a ≡ a
refl′ = refl

isTrue : Bool → Set
isTrue x = x ≡ true

refl-True : (n : ℕ) → isTrue (reflProp n)
refl-True zero = refl
refl-True (suc n) = refl-True n

unitTest : isTrue (assocProp one one two)
unitTest = refl

assocProp-zero-True : (n m : ℕ) → isTrue (assocProp zero n m)
assocProp-zero-True n m = refl-True (n + m)

assocProp-True : (n m k : ℕ) → isTrue (assocProp n m k)
assocProp-True zero    m k = assocProp-zero-True m k
assocProp-True (suc n) m k = assocProp-True n m k
~~~~

Agda code (connection between `_≡_` and `_≟_`)
==============================================

~~~~ {.sourceCode .literate .haskell}
cong : {A B : Set} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

cong-suc : {a b : ℕ} → a ≡ b → suc a ≡ suc b
cong-suc = cong suc

≡-to-≟ : {a b : ℕ} → a ≡ b → isTrue (a ≟ b)
≡-to-≟ {a} refl = refl-True a

≟-to-≡ : (a b : ℕ) → isTrue (a ≟ b) → a ≡ b
≟-to-≡ zero zero i = refl
≟-to-≡ zero (suc b) ()
≟-to-≡ (suc a) zero ()
≟-to-≡ (suc a) (suc b) i = cong-suc (≟-to-≡ a b i)
~~~~

Agda code (direct use of `_≡_`)
===============================

~~~~ {.sourceCode .literate .haskell}
+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong-suc (+-assoc a b c)

+-left-id : (a : ℕ) → zero + a ≡ a
+-left-id a = refl

+-right-id : (a : ℕ) → a + zero ≡ a
+-right-id zero = refl
+-right-id (suc a) = cong suc (+-right-id a)

com-suc : (a b : ℕ) → a + suc b ≡ suc a + b
com-suc zero b = refl
com-suc (suc a) b = cong suc (com-suc a b)

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

+-com : (a b : ℕ) → a + b ≡ b + a
+-com zero b = sym (+-right-id b)
+-com (suc a) b = trans (cong suc (+-com a b)) (sym (com-suc b a))
~~~~

Agda code (final)
=================

~~~~ {.sourceCode .literate .haskell}
module Nat where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

cong : {A B : Set} {a b : A} (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-left-id : (a : ℕ) → zero + a ≡ a
+-left-id a = refl

+-right-id : (a : ℕ) → a + zero ≡ a
+-right-id zero = refl
+-right-id (suc a) = cong suc (+-right-id a)

com-suc : (a b : ℕ) → a + suc b ≡ suc a + b
com-suc zero b = refl
com-suc (suc a) b = cong suc (com-suc a b)

sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

+-com : (a b : ℕ) → a + b ≡ b + a
+-com zero b = sym (+-right-id b)
+-com (suc a) b = trans (cong suc (+-com a b)) (sym (com-suc b a))
~~~~

How does it scale
=================

An example:

It is feasible to prove the correctness of the [Haskell pipes library](http://hackage.haskell.org/package/pipes) core in Agda.
([Work in progress](http://www.haskellforall.com/2013/10/manual-proofs-for-pipes-laws.html) by Gabriel Gonzalez.)

Thanks!
=======

Questions?

