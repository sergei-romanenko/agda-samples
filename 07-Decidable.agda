module 07-Decidable where

--open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Sum
--open import Data.Fin
--open import Data.Vec

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

--
-- Evenness
--

data Even : ℕ → Set where
  ev-base : Even zero
  ev-step : ∀ {n} → (e : Even n) → Even (suc (suc n))

even10 : Even 10
even10 = ev-step (ev-step (ev-step (ev-step (ev-step ev-base))))

ev-step⁻¹ : ∀ {n} → (ess : Even (suc (suc n))) → Even n
ev-step⁻¹ (ev-step e) = e

even? : (n : ℕ) → Dec (Even n)
even? zero = yes ev-base
even? (suc zero) = no (λ ())
even? (suc (suc n)) with even? n
... | yes p = yes (ev-step p)
... | no ¬p = no (λ z → ¬p (ev-step⁻¹ z))

soundnessEven⊤ : ∀ n p → even? n ≡ yes p → Even n
soundnessEven⊤ n p eq = p

soundnessEven⊥ : ∀ n ¬p → even? n ≡ no ¬p → ¬ Even n
soundnessEven⊥ n ¬p eq = ¬p

even?4 : even? 4 ≡ yes (ev-step (ev-step ev-base))
even?4 = refl

even?3 : even? 3 ≡ no _
even?3 = refl

×-dec : ∀ {ℓ} {P Q : Set ℓ} → Dec P → Dec Q → Dec (P × Q)
×-dec (yes p) (yes q) = yes (p , q)
×-dec _       (no ¬q) = no (λ {(p , q) → ¬q q})
×-dec (no ¬p) _       = no (λ {(p , q) → ¬p p})

⊎-dec : ∀ {ℓ} {P Q : Set ℓ} → Dec P → Dec Q → Dec (P ⊎ Q)
⊎-dec (yes p) _       = yes (inj₁ p)
⊎-dec _       (yes q) = yes (inj₂ q)
⊎-dec (no ¬p) (no ¬q) = no [ ¬p , ¬q ]′

¬-dec : ∀ {ℓ} {P : Set ℓ} → Dec P → Dec (¬ P)
¬-dec (yes p) = no (λ ¬p → ¬p p)
¬-dec (no ¬p) = yes ¬p

