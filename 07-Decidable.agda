module 07-Decidable where

--open import Data.Bool
open import Data.Nat
  hiding (_≤?_)
open import Data.Unit
  hiding (_≤_; _≤?_; _≟_)
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
  ev0 : Even zero
  ev2 : ∀ {n} → (e : Even n) → Even (suc (suc n))

even10 : Even 10
even10 = ev2 (ev2 (ev2 (ev2 (ev2 ev0))))

ev2⁻¹ : ∀ {n} → (ess : Even (suc (suc n))) → Even n
ev2⁻¹ (ev2 e) = e

even? : (n : ℕ) → Dec (Even n)
even? zero = yes ev0
even? (suc zero) = no (λ ())
even? (suc (suc n)) with even? n
... | yes p = yes (ev2 p)
... | no ¬p = no (λ z → ¬p (ev2⁻¹ z))

soundnessEven⊤ : ∀ n p → even? n ≡ yes p → Even n
soundnessEven⊤ n p eq = p

soundnessEven⊥ : ∀ n ¬p → even? n ≡ no ¬p → ¬ Even n
soundnessEven⊥ n ¬p eq = ¬p

even?4 : even? 4 ≡ yes (ev2 (ev2 ev0))
even?4 = refl

even?1 : even? 1 ≡ no (¬ Even 1 ∋ λ ())
even?1 = refl

even?3 : even? 3 ≡ no (λ (z : Even 3) → (¬ Even 1 ∋ λ ()) (ev2⁻¹ z))
even?3 = refl

even?5 : even? 5 ≡ no (λ (z : Even 5) → (¬ Even 1 ∋ λ ()) (ev2⁻¹ (ev2⁻¹ z)))
even?5 = refl

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

_≤?_ : (m n : ℕ) → Dec (m ≤ n)
-- m ≤? n = ?
zero ≤? n = yes z≤n
suc m ≤? zero = no (λ ())
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no (λ sm≤sn → ¬m≤n (≤-pred sm≤sn))

_≤⊎_ : (m n : ℕ) →  m ≤ n ⊎ n < m
--m ≤⊎ n = {!!}
zero ≤⊎ n = inj₁ z≤n
suc m ≤⊎ zero = inj₂ (s≤s z≤n)
suc m ≤⊎ suc n with m ≤⊎ n
... | inj₁ m≤n = inj₁ (s≤s m≤n)
... | inj₂ n<m = inj₂ (s≤s n<m)

--
-- Views
--

-- Parity

data Parity : ℕ → Set where
  p0 : (k : ℕ) → Parity (k * 2)
  p1 : (k : ℕ) → Parity (suc (k * 2))

parity : (n : ℕ) → Parity n
--parity n = {!!}
parity zero = p0 zero
parity (suc n)
  with parity n
parity (suc .(k * 2))
  | p0 k = p1 k
parity (suc .(suc (k * 2)))
  | p1 k = p0 (suc k)

half : (n : ℕ) → ℕ
half n              with parity n
half .(k * 2)       | p0 k = k
half .(suc (k * 2)) | p1 k = k

--
-- Information propagation
--

open import Data.Vec
open import Data.Maybe

module AddVec₁ where

  addVec : ∀ {n} (xs : Vec ℕ n) (ys : Vec ℕ n) → Vec ℕ n
  addVec = zipWith _+_

module AddVec₂ where

  addVec : ∀ {n} (xs : Vec ℕ n) {m} (ys : Vec ℕ m) → Maybe (Vec ℕ n)
  {-
  -- This doesn't work! No information propagation about m≡n . :-(
  addVec {n} xs {m} ys with m ≟ n
    if m != n then nothing
              else just (zipWith _+_ xs ys)
  -}

  addVec {n} xs {m} ys with m ≟ n
  ... | no  m≢n = nothing
  ... | yes m≡n rewrite m≡n =
    just (zipWith _+_ xs ys)

module AddVec₃ where

  addVec : ∀ {n} (xs : Vec ℕ n) {m} (ys : Vec ℕ m) → Maybe (Vec ℕ n)

  addVec {n} xs {m} ys with m ≟ n
  ... | no  m≢n = nothing
  ... | yes m≡n = just (zipWith _+_ xs ys′)
    where ys′ : Vec ℕ n
          ys′ = subst (Vec ℕ) m≡n (Vec ℕ m ∋ ys)

--
