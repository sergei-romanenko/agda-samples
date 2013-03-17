module 11-EquationalReasoning where

open import Data.Nat
open import Data.Bool
  using (true; false)
open import Data.Empty

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
  -- Note that ∼ is "Chinese" and is entered as \~ .
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

open import Function.Equivalence
  using (_⇔_; equivalence)
open import Function.Inverse
  using (_↔_)

⊎-comm : ∀ {ℓ} (A B : Set ℓ) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm A B =
  (A ⊎ B)
    ↔⟨ ×⊎.+-comm A B ⟩
  (B ⊎ A) ∎
  where open ~-Reasoning

-- What is ×⊎.+-comm ?

×⊎-+-comm : ∀ {ℓ} (A B : Set ℓ) → (A ⊎ B) ↔ (B ⊎ A)
×⊎-+-comm A B = record
  { to   = →-to-⟶ to&from
  ; from = →-to-⟶ to&from
  ; inverse-of = record
    { left-inverse-of = li&ri
    ; right-inverse-of = li&ri
    }
  }
  where
    to&from : ∀ {ℓ} {A B : Set ℓ} → A ⊎ B → B ⊎ A
    to&from = [ inj₂ , inj₁ ]′

    li&ri : ∀ {ℓ} {A B : Set ℓ} → (p : A ⊎ B) → to&from (to&from p) ≡ p
    li&ri (inj₁ a) = refl
    li&ri (inj₂ b) = refl

--
-- In ×⊎-+-comm the functions "to" and "from" coincide (by chance).
-- Let us consider an example, where "to" and "from" are different.
--

ℕ∃-suc↔ : ∀ {x} → 0 < x ↔ (∃ λ y → x ≡ suc y)
ℕ∃-suc↔ {x} = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = li
    ; right-inverse-of = ri
    }
  }
  where
    to : ∀ {x} → 0 < x → (∃ λ y → x ≡ suc y)
    to {zero} ()
    to {suc y} (s≤s z≤n) = y , refl

    from : ∀ {x} → (∃ λ y → x ≡ suc y) → 0 < x
    from (y , refl) = s≤s z≤n

    li : ∀ {x} (p : 1 ≤ x) → from (to p) ≡ p
    li (s≤s z≤n) = refl

    ri : ∀ {x} → (p : ∃ λ y → x ≡ suc y) → to (from p) ≡ p
    ri (y , refl) = refl

×-comm : ∀ {ℓ} (A B : Set ℓ) → (A × B) ↔ (B × A)
×-comm A B =
  (A × B)
    ↔⟨ ×⊎.*-comm A B ⟩
  (B × A) ∎
  where open ~-Reasoning

⊎-assoc : ∀ {ℓ} (A B C : Set ℓ) → ((A ⊎ B) ⊎ C) ↔ (A ⊎ (B ⊎ C))
⊎-assoc A B C =
  ((A ⊎ B) ⊎ C)
    ↔⟨ ×⊎.+-assoc A B C ⟩
  (A ⊎ (B ⊎ C)) ∎
  where open ~-Reasoning

×⊎-distribˡ : ∀ {ℓ} (C A B : Set ℓ) → (C × (A ⊎ B)) ↔ (C × A ⊎ C × B)
×⊎-distribˡ C A B =
  (C × (A ⊎ B))
    ↔⟨ proj₁ ×⊎.distrib C A B ⟩
  (C × A ⊎ C × B) ∎
  where open ~-Reasoning

×⊎-distribʳ : ∀ {ℓ} (C A B : Set ℓ) → ((A ⊎ B) × C) ↔ (A × C ⊎ B × C)
×⊎-distribʳ C A B =
  ((A ⊎ B) × C)
    ↔⟨ proj₂ ×⊎.distrib C A B ⟩
  (A × C ⊎ B × C) ∎
  where open ~-Reasoning

-- Here ∼ is just implication. Note that ∼ is "Chinese" and is entered as \~ .

⊎-intro : ∀ {ℓ} (A B : Set ℓ) → A → A ⊎ B
⊎-intro A B =
  A ∼⟨ inj₁ ⟩ (A ⊎ B) ∎
  where open ~-Reasoning

×-elim : ∀ {ℓ} (A B : Set ℓ) → A × B → A
×-elim A B =
  (A × B) ∼⟨ proj₁ ⟩ A ∎
  where open ~-Reasoning

--
-- This is hardly an optimal way of proving this thing.
-- Just to show the use of ×⊎.distrib , ×⊎.+-assoc ,
-- and ∼ as ⇔ .
--

⊎-distribˡ : ∀ {ℓ} {C A B : Set ℓ} → (C ⊎ A × B) ⇔ ((C ⊎ A) × (C ⊎ B))
⊎-distribˡ {_} {C} {A} {B} =
  -- Here ∼ is ⇔ .
  (C ⊎ A × B)
    ∼⟨ equivalence inj₁ [ id , proj₂ ]′ ⟨ ×⊎.+-cong ⟩ (_ ∎) ⟩
  ((C ⊎ A × C) ⊎ A × B)
    ↔⟨ ×⊎.+-assoc C (A × C) (A × B) ⟩
  (C ⊎ (A × C ⊎ A × B))
    ↔⟨ (C ∎) ⟨ ×⊎.+-cong ⟩ (↔-sym $ proj₁ ×⊎.distrib A C B) ⟩
  (C ⊎ (A × (C ⊎ B)))
    ∼⟨ equivalence < id , inj₁ >  proj₁ ⟨ ×⊎.+-cong ⟩ (_ ∎) ⟩
  (C × (C ⊎ B) ⊎ A × (C ⊎ B))
    ↔⟨ ↔-sym $ proj₂ ×⊎.distrib (C ⊎ B) C A ⟩
  ((C ⊎ A) × (C ⊎ B)) ∎
  where open ~-Reasoning

--
-- What is the difference between ↔ and ⇔ ?
-- ⇔ does not guarantee that either to (from p) p ≡ p or from (to p) ≡ p .

a→aa : ∀ {ℓ} {A : Set ℓ} → A → A × A
a→aa a = a , a

a←aa₁ : ∀ {ℓ} {A : Set ℓ} → A × A → A
a←aa₁ (a₁ , a₂) = a₁

a←aa₂ : ∀ {ℓ} {A : Set ℓ} → A × A → A
a←aa₂ (a₁ , a₂) = a₂

a⇔aa : ∀ {ℓ} {A : Set ℓ} → (A ⇔ (A × A))
a⇔aa =
  -- equivalence a→aa a←aa₁
  record
  { to = →-to-⟶ a→aa
  ; from = →-to-⟶ a←aa₁ -- or a←aa₂
  }

a-aa-li : ∀ {ℓ} {A : Set ℓ} → (p : A) → a←aa₁ (a→aa p) ≡ p
a-aa-li p = refl

∃¬a-aa-ri : a→aa (a←aa₁ (true , false)) ≡ (true , true)
∃¬a-aa-ri = refl

-- Therefore, this is not provable:
--     ∀ {ℓ} {A : Set ℓ} → (p : A × A) → a→aa (a←aa₁ p) ≡ p

--