module Example where

open import Relation.Binary.PropositionalEquality

open import Algebra
open import Data.Nat
open import Data.Vec using([]; _∷_)
open import Data.Nat.Properties using (commutativeSemiring)
open CommutativeSemiring commutativeSemiring
     using (+-commutativeMonoid)

open import Data.Product

open import Expr
import Semantics
open Semantics +-commutativeMonoid


0+0≡0-prove : 0 + 0 ≡ 0
0+0≡0-prove = prove ρ e₁ e₂ refl
  where
    ρ = []
    e₁ = close 0 (◇ ⊕ ◇)
    e₂ = close 0 ◇

0+0≡0-solve0 : 0 + 0 ≡ 0
0+0≡0-solve0 = solve0 (◇ ⊕ ◇ ⊜ ◇) refl

0+0≡0-solve : 0 + 0 ≡ 0
0+0≡0-solve = solve 0 (◇ ⊕ ◇ ⊜ ◇) refl


0+a≡a-prove : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-prove a = prove ρ e₁ e₂ refl
  where
    ρ = a ∷ []
    e₁ = close 1 λ a → ◇ ⊕ a
    e₂ = close 1 λ a → a

0+a≡a-solve1 : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-solve1 = solve1 (λ a → ◇ ⊕ a ⊜ a) refl

0+a≡a-solve : ∀ (a : ℕ) → 0 + a ≡ a
0+a≡a-solve = solve 1 (λ a → ◇ ⊕ a ⊜ a) refl


ab-prove : ∀ (a b : ℕ) → (a + b) + a ≡ b + (a + a)
ab-prove a b = prove ρ e₁ e₂ refl
  where
    ρ = a ∷ b ∷ []
    e₁₂ = close 2 λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ (a ⊕ a)
    e₁ = proj₁ e₁₂
    e₂ = proj₂ e₁₂

ab-solve2 : ∀ (a b : ℕ) → (a + b) + a ≡ b + (a + a)
ab-solve2 = solve2 (λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ a ⊕ a) refl

ab-solve : ∀ a b → (a + b) + a ≡ b + (a + a)
ab-solve = solve 2 (λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ (a ⊕ a)) refl


abcd-prove : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
abcd-prove a b c d = prove ρ e₁ e₂ refl
  where
    ρ = a ∷ b ∷ c ∷ d ∷ []
    e₁ = close 4 λ a b c d → (a ⊕ b) ⊕ (c ⊕ d)
    e₂ = close 4 λ a b c d → (a ⊕ c) ⊕ (b ⊕ d)

abcd-solve : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
abcd-solve = solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d)) refl

--
