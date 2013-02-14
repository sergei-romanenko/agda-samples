module Example where

open import Relation.Binary.PropositionalEquality

open import Algebra
open import Data.Nat
open import Data.Vec using([]; _∷_)
open import Data.Nat.Properties using (commutativeSemiring)
open CommutativeSemiring commutativeSemiring
     using (+-commutativeMonoid)

open import Expr
import Semantics
open Semantics +-commutativeMonoid

prove₁ : ∀ a b → (a + b) + a ≡ b + (a + a)
prove₁ a b = prove ρ e₁ e₂ refl
  where
    ρ = a ∷ b ∷ []
    e₁ = close 2 λ a b → (a ⊕ b) ⊕ a
    e₂ = close 2 λ a b → b ⊕ (a ⊕ a)

prove₂ : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
prove₂ a b c d = prove ρ e₁ e₂ refl
  where
    ρ = a ∷ b ∷ c ∷ d ∷ []
    e₁ = close 4 λ a b c d → (a ⊕ b) ⊕ (c ⊕ d)
    e₂ = close 4 λ a b c d → (a ⊕ c) ⊕ (b ⊕ d)

solve₁ : ∀ a b → (a + b) + a ≡ b + (a + a)
solve₁ = solve 2 (λ a b → (a ⊕ b) ⊕ a ⊜ b ⊕ (a ⊕ a)) refl

solve₂ : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
solve₂ = solve 4 (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d)) refl

--
