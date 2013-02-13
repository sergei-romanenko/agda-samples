module Example where

open import Expr
import Semantics as Sem
open import Relation.Binary.PropositionalEquality

open import Algebra
open import Data.Nat
open import Data.Vec using([]; _∷_)
open import Data.Nat.Properties using (commutativeSemiring)
open CommutativeSemiring commutativeSemiring
     using (+-commutativeMonoid)

open Sem +-commutativeMonoid

eqn₁ : Eqn 2
eqn₁ = build 2 λ a b → (a ⊕ b) ⊕ a == b ⊕ (a ⊕ a)

prf₁ : ∀ n m → (n + m) + n ≡ m + (n + n)
prf₁ n m = prove eqn₁ (n ∷ m ∷ []) refl

prf₂ : ∀ a b c d → _
prf₂ a b c d =
  prove
    (build 4 λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) == (a ⊕ c) ⊕ (b ⊕ d))
    (a ∷ b ∷ c ∷ d ∷ [])
    refl

--
