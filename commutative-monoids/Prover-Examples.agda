module Prover-Examples where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Algebra
  using (module CommutativeSemiring)

open import Data.Nat
open import Data.Fin
  using (zero; suc)
open import Data.Vec
  using([]; _∷_)

open import Data.Nat.Properties
  using (commutativeSemiring)

open CommutativeSemiring commutativeSemiring
  using (+-commutativeMonoid)

import Prover
open Prover +-commutativeMonoid

0+0≡0-prove : 0 + 0 ≡ 0
0+0≡0-prove = prove eq ρ refl
  where
    eq = ◇ ⊕ ◇ ⊜ ◇
    ρ = []

0+a≡a-prove : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-prove a = prove eq ρ refl
  where
    eq = close 1 λ a → ◇ ⊕ a ⊜ a
    ρ = a ∷ []

ab-prove : ∀ (a b : ℕ) → (a + b) + a ≡ b + (a + a)
ab-prove a b = prove eq ρ refl
  where
    eq = close 2 λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ (a ⊕ a)
    ρ = a ∷ b ∷ []

abcd-prove : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
abcd-prove a b c d = prove eq ρ refl
  where
    eq = close 4 λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d)
    ρ = a ∷ b ∷ c ∷ d ∷ []

--
