module Solver-Examples where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Algebra
  using (module CommutativeSemiring)

open import Data.Nat

open import Data.Nat.Properties using (commutativeSemiring)
open CommutativeSemiring commutativeSemiring
  using (+-commutativeMonoid)

import Solver
open Solver +-commutativeMonoid


0+0≡0-solve0 : 0 + 0 ≡ 0
0+0≡0-solve0 = solve0 (◇ ⊕ ◇ ⊜ ◇) refl

0+0≡0-solve : 0 + 0 ≡ 0
0+0≡0-solve = solve 0 (◇ ⊕ ◇ ⊜ ◇) refl

0+a≡a-solve1 : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-solve1 = solve1 (λ a → ◇ ⊕ a ⊜ a) refl

0+a≡a-solve : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-solve = solve 1 (λ a → ◇ ⊕ a ⊜ a) refl

ab-solve2 : ∀ (a b : ℕ) → (a + b) + a ≡ b + (a + a)
ab-solve2 = solve2 (λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ a ⊕ a) refl

ab-solve : ∀ a b → (a + b) + a ≡ b + (a + a)
ab-solve = solve 2 (λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ (a ⊕ a)) refl

abcd-solve : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
abcd-solve = solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d)) refl

--
