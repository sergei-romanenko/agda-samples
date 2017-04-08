module 14-InfiniteDescent where

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
      Sum.map even1 odd1 (even⊎odd-suc n)

    even⊎odd-suc : ∀ n → Odd n ⊎ Even n
    even⊎odd-suc zero =
      inj₂ even0
    even⊎odd-suc (suc n) =
      Sum.map odd1 even1 (even⊎odd n)

module Even⊎Odd-3 where

  mutual

    even⊎odd : ∀ n → Even n ⊎ Odd n
    even⊎odd zero =
      inj₁ even0
    even⊎odd (suc n) =
      ([ inj₂ , inj₁ ]′ ∘ Sum.map odd1 even1) (even⊎odd n)

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
