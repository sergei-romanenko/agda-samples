module 14-InfiniteDescent where

open import Data.Nat
open import Data.Sum as Sum

open import Function

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
      ([ inj₂ , inj₁ ]′ ∘ map odd1 even1) (even⊎odd n)

data Silly : (x y : ℕ) → Set where
  zy : ∀ {y} → Silly zero y
  xz : ∀ {x} → Silly x zero
  ss : ∀ {x y} → Silly (suc (suc x)) y → Silly (suc x) (suc y)

all-silly : ∀ x y → Silly x y
all-silly x zero = xz
all-silly zero (suc y) = zy
all-silly (suc x) (suc y) =
  ss (all-silly (suc (suc x)) y)
