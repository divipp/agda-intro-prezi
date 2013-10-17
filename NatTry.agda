-- Long version, the final version is Nat.agda
module NatTry where

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

module isTrue-direct where

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

-------- switch to _≡_

module ≡-Bool where

  -- propositional equalitiy on Bool
  data _≡_ : Bool → Bool → Set where
    refl : {a : Bool} → a ≡ a  -- the Bool paramter is hidden

  infix 4 _≡_

  isTrue : Bool → Set
  isTrue x = x ≡ true

-- generic propositional equality
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 4 _≡_

-- This is the type of the refl constructor
-- The parameters are hidden
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


---- switch from _≟_

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


-- the rest is in Nat.agda
