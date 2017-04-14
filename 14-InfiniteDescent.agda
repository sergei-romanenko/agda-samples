module 14-InfiniteDescent where

{--
  Based on

    James Brotherston. Sequent Calculus Proof Systems for Inductive Definitions.
    PhD thesis, University of Edinburgh, 2006.
    http://hdl.handle.net/1842/1458
--}

open import Data.Nat
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Empty

open import Function

open import Relation.Nullary

mutual

  data Even : ℕ → Set where
    even0  : Even zero
    even1 : ∀ {n} → Odd n → Even (suc n)

  data Odd : ℕ → Set where
    odd1 : ∀ {n} → Even n → Odd (suc n)

odd-1 : Odd 1
odd-1 = odd1 even0

even-2 : Even 2
even-2 = even1 (odd1 even0)

module Even⊎Odd-1 where

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd zero =
    inj₁ even0
  even⊎odd (suc zero) =
    inj₂ (odd1 even0)
  even⊎odd (suc (suc n)) with even⊎odd n
  ... | inj₁ even-n =
    inj₁ (even1 (odd1 even-n))
  ... | inj₂ odd-n =
    inj₂ (odd1 (even1 odd-n))

module Even⊎Odd-2 where

  mutual

    even⊎odd : ∀ n → Even n ⊎ Odd n
    even⊎odd zero =
      inj₁ even0
    even⊎odd (suc n) =
      Sum.map even1 odd1 (odd⊎even n)

    odd⊎even : ∀ n → Odd n ⊎ Even n
    odd⊎even zero =
      inj₂ even0
    odd⊎even (suc n) =
      Sum.map odd1 even1 (even⊎odd n)

module Even⊎Odd-3 where

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd zero =
    inj₁ even0
  even⊎odd (suc n) =
    ([ inj₂ , inj₁ ]′ ∘ Sum.map odd1 even1) (even⊎odd n)

module Even⊎Odd-4 where

  indℕ : ∀ {P : ℕ → Set} (base : P zero) (step : ∀ n → P n → P (suc n)) →
    ∀ n → P n 
  indℕ base step zero = base
  indℕ base step (suc n) =
    step n (indℕ base step n)

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd n =
    indℕ {λ n → Even n ⊎ Odd n}
      (inj₁ even0) (λ m → [ inj₂ ∘ odd1 , inj₁ ∘ even1 ]′) n

-- The R example

data R : (x y : ℕ) → Set where
  zy : ∀ {y} → R zero y
  xz : ∀ {x} → R x zero
  ss : ∀ {x y} → R (suc (suc x)) y → R (suc x) (suc y)

all-r : ∀ x y → R x y
all-r x zero = xz
all-r zero (suc y) = zy
all-r (suc x) (suc y) =
  ss (all-r (suc (suc x)) y)

-- The P & Q example

mutual

  data P : (x : ℕ) → Set where
    pz : P zero
    ps : ∀ {x} → P x → Q x (suc x) → P (suc x)

  data Q : (x y : ℕ) → Set where
    qz : ∀ {x} → Q x zero
    qs : ∀ {x y} → P x → Q x y → Q x (suc y)

mutual

  all-q : ∀ x y → Q x y
  all-q x zero = qz
  all-q x (suc y) =
    qs (all-p x) (all-q x y)

  all-p : ∀ x → P x
  all-p zero = pz
  all-p (suc x) =
    ps (all-p x) (all-q x (suc x))

-- The N′ example

  data N′ : (x y : ℕ) → Set where
    nz : ∀ {y} → N′ zero y
    ns : ∀ {x y} → N′ y x → N′ (suc x) y

mutual

  all-n : ∀ x y → N′ x y
  all-n zero y = nz
  all-n (suc x) y = ns (all-n y x)

-- The "problem" with Agda is that it is a statically-typed language,
-- while Brotherston deals with an untyped language.
-- Thus some examples are too easy to reproduce in Agda.
-- Hence, let us define natural numbers in "unnatural" way,
-- in order that they be a subset of an Agda type.

open import Data.Bool
open import Data.List

data BN : (bs : List Bool) → Set where
  zero : BN []
  suc  : ∀ {bs} → BN bs → BN (true ∷ bs)

bn3 : BN (true ∷ true ∷ true ∷ [])
bn3 = suc (suc (suc zero))

mutual

  data BE : (bs : List Bool) → Set where
    be0 : BE []
    be1 : ∀ {bs} → BO bs → BE (true ∷ bs)

  data BO : (bs : List Bool) → Set where
    bo1 : ∀ {bs} → BE bs → BO (true ∷ bs)

be2 : BE (true ∷ true ∷ [])
be2 = be1 (bo1 be0)

bo3 : BO (true ∷ true ∷ true ∷ [])
bo3 = bo1 (be1 (bo1 be0))

module BE⊎BO-1 where

  be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
  be⊎bo zero = inj₁ be0
  be⊎bo (suc zero) = inj₂ (bo1 be0)
  be⊎bo (suc (suc bn)) with be⊎bo bn
  ... | inj₁ be-bs =
    inj₁ (be1 (bo1 be-bs))
  ... | inj₂ bo-bs =
    inj₂ (bo1 (be1 bo-bs))

module BE⊎BO-2 where

  mutual

    be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
    be⊎bo zero = inj₁ be0
    be⊎bo (suc bn) =
      Sum.map be1 bo1 (bo⊎be bn)

    bo⊎be : ∀ {n} (bn : BN n) → BO n ⊎ BE n
    bo⊎be zero = inj₂ be0
    bo⊎be (suc bn) =
      Sum.map bo1 be1 (be⊎bo bn)

module BE⊎BO-3 where

  be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
  be⊎bo zero = inj₁ be0
  be⊎bo (suc bn) =
    [ inj₂ , inj₁ ]′ (Sum.map bo1 be1 (be⊎bo bn))

module BE⊎BO-BN-1 where

  be-bn : ∀ {n} (be : BE n) → BN n
  be-bn be0 = zero
  be-bn (be1 (bo1 be)) = suc (suc (be-bn be))

  be⊎bo-bn : ∀ {n} (beo : BE n ⊎ BO n) → BN n
  be⊎bo-bn (inj₁ be) = be-bn be
  be⊎bo-bn (inj₂ (bo1 be)) = suc (be-bn be)

module BE⊎BO-BN-2 where

  mutual

    be-bn : ∀ {n} (be : BE n) → BN n
    be-bn be0 = zero
    be-bn (be1 bo) = suc (bo-bn bo)

    bo-bn : ∀ {n} (bo : BO n) → BN n
    bo-bn (bo1 be) = suc (be-bn be)

  be⊎bo-bn : ∀ {n} (beo : BE n ⊎ BO n) → BN n
  be⊎bo-bn (inj₁ be) = be-bn be
  be⊎bo-bn (inj₂ bo) = bo-bn bo
