module 11-EquationalReasoning where

open import Data.Nat

open import Data.Sum
  renaming (map to map⊎)
open import Data.Product
  renaming (map to map×)

open import Data.Nat.Properties

open import Algebra
  using (module CommutativeSemiring)

private
  module +* =
    CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open import Relation.Binary.PropositionalEquality

open import Function
import Function.Related as Related

module ~-Reasoning = Related.EquationalReasoning
  renaming (sym to ↔-sym)

2* : ℕ → ℕ
2* zero = zero
2* (suc n) = suc (suc (2* n))

-- "Correctness"

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n m n = begin
  m + suc n
    ≡⟨ refl ⟩
  m + (1 + n)
    ≡⟨ sym (+*.+-assoc m (suc zero) n) ⟩
  (m + 1) + n
    ≡⟨ cong (flip _+_ n) (+*.+-comm m (suc zero)) ⟩
  (1 + m) + n
    ≡⟨ refl ⟩
  suc (m + n)
  ∎
  where open ≡-Reasoning

2*-correct : ∀ n → 2* n ≡ n + n
2*-correct zero = refl
2*-correct (suc n) = begin
  2* (suc n)
    ≡⟨ refl ⟩
  suc (suc (2* n))
    ≡⟨ cong (suc ∘ suc) (2*-correct n) ⟩
  suc (suc (n + n))
    ≡⟨ sym (m+1+n≡1+m+n (suc n) n) ⟩
  suc (n + suc n)
    ≡⟨ refl ⟩
  suc n + suc n
  ∎
  where open ≡-Reasoning

-- Now let us prove this:

2*-injective : (n m : ℕ) → 2* n ≡ 2* m → n ≡ m
2*-injective zero zero _ = refl
2*-injective zero (suc n) ()
2*-injective (suc n) zero ()
2*-injective (suc n) (suc m) h =
  -- This is shot, but looks like a mystery.
  cong suc (2*-injective n m (cong (pred ∘ pred) h))

-- Let us try to rewrite the above proof in a more "human-friendly" form
-- by using "equational reasoning.
-- The point is that, unlike "≡-Reasoning", in this proof
-- we have to deal with a sequence of equations, rather than expressions.

2*-injective′ : (n m : ℕ) → 2* n ≡ 2* m → n ≡ m
2*-injective′ zero zero = λ _ → refl
2*-injective′ zero (suc n) = λ ()
2*-injective′ (suc n) zero = λ ()
2*-injective′ (suc n) (suc m) =
  -- Here ∼ corresponds to implication.
  2* (suc n) ≡ 2* (suc m)
    ≡⟨ refl ⟩
  suc (suc (2* n)) ≡ suc (suc (2* m))
    ∼⟨ cong (pred ∘ pred) ⟩
  2* n ≡ 2* m
    ∼⟨ 2*-injective′ n m ⟩
  n ≡ m
    ∼⟨ cong suc ⟩
  suc n ≡ suc m ∎
  where open ~-Reasoning


open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)


⊎-comm : ∀ {ℓ} (A B : Set ℓ) → A ⊎ B → B ⊎ A
⊎-comm A B =
  (A ⊎ B)
    ↔⟨ ×⊎.+-comm A B ⟩
  (B ⊎ A) ∎
  where open ~-Reasoning

×-comm : ∀ {ℓ} (A B : Set ℓ) → A × B → B × A
×-comm A B =
  (A × B)
    ↔⟨ ×⊎.*-comm A B ⟩
  (B × A) ∎
  where open ~-Reasoning

⊎-assoc : ∀ {ℓ} (A B C : Set ℓ) → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc A B C =
  ((A ⊎ B) ⊎ C)
    ↔⟨ ×⊎.+-assoc A B C ⟩
  (A ⊎ (B ⊎ C)) ∎
  where open ~-Reasoning

×⊎-distribˡ : ∀ {ℓ} (C A B : Set ℓ) → C × (A ⊎ B) → C × A ⊎ C × B
×⊎-distribˡ C A B =
  (C × (A ⊎ B))
    ↔⟨ proj₁ ×⊎.distrib C A B ⟩
  (C × A ⊎ C × B) ∎
  where open ~-Reasoning

×⊎-distribʳ : ∀ {ℓ} (C A B : Set ℓ) → (A ⊎ B) × C → A × C ⊎ B × C
×⊎-distribʳ C A B =
  ((A ⊎ B) × C)
    ↔⟨ proj₂ ×⊎.distrib C A B ⟩
  (A × C ⊎ B × C) ∎
  where open ~-Reasoning

--
-- This is hardly an optimal way of proving this thing.
-- Just to show the use of ×⊎.distrib and ×⊎.+-assoc.
--

-- Here ∼ is just implication. Note that ∼ is "Chinese" and is entered as \~ .

cacb⇒cab : ∀ {ℓ} {C A B : Set ℓ} → (C ⊎ A) × (C ⊎ B) → C ⊎ A × B
cacb⇒cab {_} {C} {A} {B} =
  ((C ⊎ A) × (C ⊎ B))
    ↔⟨ proj₂ ×⊎.distrib (C ⊎ B) C A ⟩
  (C × (C ⊎ B) ⊎ A × (C ⊎ B))
    ∼⟨ proj₁ ⊎-cong id ⟩
  (C ⊎ (A × (C ⊎ B)))
    ↔⟨ (C ∎) ⊎-cong proj₁ ×⊎.distrib A C B ⟩
  (C ⊎ (A × C ⊎ A × B))
    ↔⟨ ↔-sym $ ×⊎.+-assoc C (A × C) (A × B) ⟩
  ((C ⊎ A × C) ⊎ A × B)
    ∼⟨ [ id , proj₂ ]′ ⊎-cong id ⟩
  (C ⊎ A × B) ∎
  where open ~-Reasoning


--