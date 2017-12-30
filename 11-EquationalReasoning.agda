module 11-EquationalReasoning where

open import Data.Nat
open import Data.Bool
  using (true; false)
open import Data.Empty

open import Data.Sum
  renaming (map to map⊎)
open import Data.Product
  renaming (map to map×)

open import Algebra
  using (module CommutativeSemiring)

open import Data.Nat.Properties.Simple

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; cong₂; →-to-⟶; module ≡-Reasoning)

open import Function
import Function.Related as Related

2* : ℕ → ℕ
2* zero = zero
2* (suc n) = suc (suc (2* n))

-- "Correctness"

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n m n = begin
  m + suc n
    ≡⟨⟩
  m + (1 + n)
    ≡⟨ P.sym (+-assoc m (suc zero) n) ⟩
  (m + 1) + n
    ≡⟨ +-comm m (suc zero) ⟨ cong₂ _+_ ⟩ refl ⟩
  (1 + m) + n
    ≡⟨⟩
  suc (m + n)
  ∎
  where open ≡-Reasoning

2*-correct : ∀ n → 2* n ≡ n + n
2*-correct zero = refl
2*-correct (suc n) = begin
  2* (suc n)
    ≡⟨⟩
  suc (suc (2* n))
    ≡⟨ cong (suc ∘ suc) (2*-correct n) ⟩
  suc (suc (n + n))
    ≡⟨ P.sym (m+1+n≡1+m+n (suc n) n) ⟩
  suc (n + suc n)
    ≡⟨⟩
  suc n + suc n
  ∎
  where open ≡-Reasoning

-- Now let us prove this:

2*-injective : (n m : ℕ) → 2* n ≡ 2* m → n ≡ m
2*-injective zero zero refl = refl
2*-injective zero (suc n) ()
2*-injective (suc n) zero ()
2*-injective (suc n) (suc m) 2+2n≡2+2m =
  -- This is short, but looks like a mystery.
  cong suc (2*-injective n m (cong (pred ∘ pred) 2+2n≡2+2m))

-- Let us try to rewrite the above proof in a more "human-friendly" form
-- by using "equational reasoning.
-- The point is that, unlike "≡-Reasoning", in this proof
-- we have to deal with a sequence of equations, rather than expressions.

2*-injective′ : (n m : ℕ) → 2* n ≡ 2* m → n ≡ m
2*-injective′ zero zero refl = refl
2*-injective′ zero (suc n) ()
2*-injective′ (suc n) zero ()
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
  where open Related.EquationalReasoning


open import Function.Equivalence
  using (_⇔_; equivalence)
open import Function.Inverse
  using (_↔_)

open import Data.List
open import Data.Unit
  using (⊤; tt)

-- What is "isomorphism"?
-- suc (suc zero) ↔ ⊤ ∷ ⊤ ∷ []

ℕ↔List⊤ : ℕ ↔ List ⊤

ℕ↔List⊤ = record
  {to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
    to : ℕ → List ⊤
    to zero = []
    to (suc n) = tt ∷ to n

    from : List ⊤ → ℕ
    from [] = zero
    from (tt ∷ xs) = suc (from xs)

    from∘to : (n : ℕ) → from (to n) ≡ n
    from∘to zero = refl
    from∘to (suc n) = cong suc (from∘to n)

    to∘from : (xs : List ⊤) → to (from xs) ≡ xs
    to∘from [] = refl
    to∘from (tt ∷ xs) = cong (_∷_ tt) (to∘from xs)

-- In Agda, "data" and "proofs" are the same thing.
-- Here is an example of an isomorphism between proofs!

ℕ∃-suc↔ : ∀ {x} → 0 < x ↔ (∃ λ y → x ≡ suc y)
ℕ∃-suc↔ {x} = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
    to : ∀ {x} → 0 < x → (∃ λ y → x ≡ suc y)
    to {zero} ()
    to {suc y} (s≤s z≤n) = y , refl

    from : ∀ {x} → (∃ λ y → x ≡ suc y) → 0 < x
    from (y , refl) = s≤s z≤n

    from∘to : ∀ {x} (p : 1 ≤ x) → from (to p) ≡ p
    from∘to (s≤s z≤n) = refl

    to∘from : ∀ {x} → (p : ∃ λ y → x ≡ suc y) → to (from p) ≡ p
    to∘from (y , refl) = refl

-- × and ⊎ form a commutative semiring.

open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

-- Let us use a theorem provided by ×⊎ .

⊎-comm : ∀ {ℓ} (A B : Set ℓ) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm A B =
  (A ⊎ B)
    ↔⟨ ×⊎.+-comm A B ⟩
  (B ⊎ A) ∎
  where open Related.EquationalReasoning

-- What is ×⊎.+-comm ?

×⊎-+-comm : ∀ {ℓ} (A B : Set ℓ) → (A ⊎ B) ↔ (B ⊎ A)
×⊎-+-comm A B = record
  { to   = →-to-⟶ to
  ; from = →-to-⟶ to  -- By chance, "to" and "from" coincide...
  ; inverse-of = record
    { left-inverse-of = to∘to
    ; right-inverse-of = to∘to
    }
  }
  where
    to : ∀ {ℓ} {A B : Set ℓ} → A ⊎ B → B ⊎ A
    to = [ inj₂ , inj₁ ]′

    to∘to : ∀ {ℓ} {A B : Set ℓ} → (p : A ⊎ B) → to (to p) ≡ p
    to∘to (inj₁ a) = refl
    to∘to (inj₂ b) = refl

-- More theorems provided by ×⊎-+-comm...

×-comm : ∀ {ℓ} (A B : Set ℓ) → (A × B) ↔ (B × A)
×-comm A B =
  (A × B)
    ↔⟨ ×⊎.*-comm A B ⟩
  (B × A) ∎
  where open Related.EquationalReasoning

⊎-assoc : ∀ {ℓ} (A B C : Set ℓ) → ((A ⊎ B) ⊎ C) ↔ (A ⊎ (B ⊎ C))
⊎-assoc A B C =
  ((A ⊎ B) ⊎ C)
    ↔⟨ ×⊎.+-assoc A B C ⟩
  (A ⊎ (B ⊎ C)) ∎
  where open Related.EquationalReasoning

×⊎-distribˡ : ∀ {ℓ} (C A B : Set ℓ) → (C × (A ⊎ B)) ↔ (C × A ⊎ C × B)
×⊎-distribˡ C A B =
  (C × (A ⊎ B))
    ↔⟨ proj₁ ×⊎.distrib C A B ⟩
  (C × A ⊎ C × B) ∎
  where open Related.EquationalReasoning

×⊎-distribʳ : ∀ {ℓ} (C A B : Set ℓ) → ((A ⊎ B) × C) ↔ (A × C ⊎ B × C)
×⊎-distribʳ C A B =
  ((A ⊎ B) × C)
    ↔⟨ proj₂ ×⊎.distrib C A B ⟩
  (A × C ⊎ B × C) ∎
  where open Related.EquationalReasoning


-- Reasoning about implications.
-- In this context ∼ denotes implication.
-- Note that ∼ is "Chinese" and is entered as \~ .

⊎-intro : ∀ {ℓ} (A B : Set ℓ) → A → A ⊎ B
⊎-intro A B =
  A ∼⟨ inj₁ ⟩ (A ⊎ B) ∎
  where open Related.EquationalReasoning

×-elim : ∀ {ℓ} (A B : Set ℓ) → A × B → A
×-elim A B =
  (A × B) ∼⟨ proj₁ ⟩ A ∎
  where open Related.EquationalReasoning

--
-- A ⇔ B means (A → B) × (B → A)
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
-- An example of using ×⊎.distrib , ×⊎.+-assoc , ×⊎.+-cong
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
    ↔⟨ (C ∎) ⟨ ×⊎.+-cong ⟩ (sym $ proj₁ ×⊎.distrib A C B) ⟩
  (C ⊎ (A × (C ⊎ B)))
    ∼⟨ equivalence < id , inj₁ >  proj₁ ⟨ ×⊎.+-cong ⟩ (_ ∎) ⟩
  (C × (C ⊎ B) ⊎ A × (C ⊎ B))
    ↔⟨ sym $ proj₂ ×⊎.distrib (C ⊎ B) C A ⟩
  ((C ⊎ A) × (C ⊎ B)) ∎
  where open Related.EquationalReasoning
