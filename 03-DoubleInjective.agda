module 03-DoubleInjective where

open import Data.Nat
open import Function using (_∘_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding([_])

open ≡-Reasoning

module Gen where

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

≡-pred : ∀{n m : ℕ} → suc n ≡ suc m → n ≡ m
≡-pred refl = refl

double-injective₁ : (n m : ℕ) → double n ≡ double m → n ≡ m
-- P n ⟺ ∀ m → double n ≡ double m → n ≡ m
-- Consider P 0 ⟺ ∀ m → double 0 ≡ double m → 0 ≡ m
-- Suppose m ≡ 0
-- Then P 0 ⟺ 0 ≡ 0 → 0 ≡ 0
double-injective₁ zero zero _ = refl
-- Suppose m ≡ suc m'
-- Then P 0 ⟺ 0 ≡ suc (suc (double m')) → 0 ≡ suc m'
double-injective₁ zero (suc m) ()
-- Consider P (suc n') ⟺ ∀ m → double (suc n') ≡ double m → suc n' ≡ m
-- Suppose m ≡ 0
-- Then P (suc n') ⟺ suc (suc (double n')) ≡ 0 → suc n' ≡ 0
double-injective₁ (suc n') zero ()
-- Suppose m ≡ suc m'
-- Then P (suc n') ⟺ suc (suc (double n')) ≡ suc (suc (double m')) →
--                   suc n' ≡ suc m'
-- Let ssd : suc (suc (double n')) ≡ suc (suc (double m'))
-- Then ≡-pred ssdn : suc (double n') ≡ suc (double m')
-- Then ≡-pred (≡-pred ssdn) : double n' ≡ double m'
-- Let d : double n' ≡ double m'
-- Then double-injective₁ n' m' d : n' ≡ m'
-- Hence suc n' ≡ suc m'
double-injective₁ (suc n') (suc m') ssd with ≡-pred (≡-pred ssd)
... | d = cong suc (double-injective₁ n' m' d)

double-injective₂ : (n m : ℕ) → double n ≡ double m → n ≡ m
double-injective₂ zero zero _ = refl
double-injective₂ zero (suc m') ()
double-injective₂ (suc n') zero ()
double-injective₂ (suc n') (suc m') ssd≡ssd = sn≡sm
  where
  ssd : suc (suc (double n')) ≡ suc (suc (double m'))
  ssd = ssd≡ssd
  sd : suc (double n') ≡ suc (double m')
  sd = ≡-pred ssd
  d : double n' ≡ double m'
  d = ≡-pred sd
  n≡m : n' ≡ m'
  n≡m = double-injective₂ n' m' d
  sn≡sm : suc n' ≡ suc m'
  sn≡sm = cong suc n≡m

double-injective₃ : (n m : ℕ) → double n ≡ double m → n ≡ m
double-injective₃ zero zero _ = refl
double-injective₃ zero (suc m') ()
double-injective₃ (suc n') zero ()
double-injective₃ (suc n') (suc m') ssd≡ssd =
  cong suc (double-injective₃ n' m' (cong (pred ∘ pred) ssd≡ssd))

  
