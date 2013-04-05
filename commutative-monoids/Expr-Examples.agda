module Expr-Examples where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec

open import Relation.Binary.PropositionalEquality

open import Expr

expr₁ : Expr 3
expr₁ = close 3 λ a b c → a ⊕ (b ⊕ a)

what-is-expr₁? : expr₁ ≡ var zero ⊕ (var (suc zero) ⊕ var zero)
what-is-expr₁? = refl

nr₁ : nr expr₁ ≡
  suc (suc zero) ∷ suc zero ∷ zero ∷ []
nr₁ = refl

norm₁ : norm expr₁ ≡
  (var zero ⊕ var zero ⊕ ◇) ⊕ (var (suc zero) ⊕ ◇) ⊕ ◇ ⊕ ◇
norm₁ = refl

--
