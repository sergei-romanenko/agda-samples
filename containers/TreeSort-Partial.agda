module TreeSort-Partial where

open import Level
  using (Level; _⊔_; Lift; lift; lower)

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Algebra
  using (module CommutativeSemiring)

open import Function
open import Function.Inverse
  using (_↔_; module Inverse)

open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)

private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

open import Algebra
  using (module CommutativeSemiring)

open import Relation.Binary.PropositionalEquality

import Function.Related as Related

private
  module ~-Reasoning = Related.EquationalReasoning
    renaming (sym to ↔-sym)

open import Tree

------------------------------------------------------------------------
-- Insertion into trees


-- Inserts an element into the tree.
-- Insertion of n into xs at the right place
-- (assuming that xs is sorted)

insert : ∀ {A : Set} (_≤_ : A → A → Bool)
           (x : A) (t : Tree A) → Tree A
insert _≤_ x leaf = node leaf x leaf
insert _≤_ x (node l y r) with x ≤ y
... | true  = node (insert _≤_ x l) y r
... | false = node l y (insert _≤_ x r)

-- The insert function inserts.

AnyT-insert : ∀ {A : Set}
               (P : A → Set) (_≤_ : A → A → Bool) (x : A) (t : Tree A) →
               AnyT P (insert _≤_ x t) ↔ (P x ⊎ AnyT P t)

AnyT-insert P _≤_ x leaf =
  AnyT P (insert _≤_ x leaf)
    ↔⟨ _ ∎ ⟩
  AnyT P (node leaf x leaf)
    ↔⟨ AnyT-node ⟩
  (AnyT P leaf ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ AnyT-leaf ⟨ ×⊎.+-cong ⟩ _ ∎  ⟩
  (⊥ ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ (↔-sym $ Lift⊥↔⊥) ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
  (Lift ⊥ ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ proj₁ ×⊎.+-identity (P x ⊎ AnyT P leaf) ⟩
  (P x ⊎ AnyT P leaf) ∎
  where open ~-Reasoning

AnyT-insert P _≤_ x (node l y r) with x ≤ y
... | true =
  AnyT P (node (insert _≤_ x l) y r)
    ↔⟨ AnyT-node ⟩
  (AnyT P (insert _≤_ x l) ⊎ P y ⊎ AnyT P r)
    ↔⟨ AnyT-insert P _≤_ x l ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
  ((P x ⊎ AnyT P l) ⊎ P y ⊎ AnyT P r)
    ↔⟨ ×⊎.+-assoc (P x) (AnyT P l) (P y ⊎ AnyT P r) ⟩
  (P x ⊎ (AnyT P l ⊎ P y ⊎ AnyT P r))
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (↔-sym $ AnyT-node) ⟩
  (P x ⊎ AnyT P (node l y r)) ∎
  where open ~-Reasoning
... | false =
  AnyT P (node l y (insert _≤_ x r))
    ↔⟨ AnyT-node ⟩
  (AnyT P l ⊎ P y ⊎ AnyT P (insert _≤_ x r))
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (_ ∎ ⟨ ×⊎.+-cong ⟩ AnyT-insert P _≤_ x r) ⟩
  (AnyT P l ⊎ P y ⊎ P x ⊎ AnyT P r)
    ↔⟨ shuffle ⟩
  (P x ⊎ AnyT P l ⊎ P y ⊎ AnyT P r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (↔-sym $ AnyT-node) ⟩
  (P x ⊎ AnyT P (node l y r)) ∎
  where
    open ~-Reasoning
    shuffle : ∀ {A B C D : Set} → ((B ⊎ C ⊎ A ⊎ D) ↔ (A ⊎ B ⊎ C ⊎ D))
    shuffle {A} {B} {C} {D} =
      (B ⊎ (C ⊎ A ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (↔-sym $ ×⊎.+-assoc C A D) ⟩
      (B ⊎ ((C ⊎ A) ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (×⊎.+-comm C A ⟨ ×⊎.+-cong ⟩ _ ∎) ⟩
      (B ⊎ ((A ⊎ C) ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ×⊎.+-assoc A C D ⟩
      (B ⊎ (A ⊎ (C ⊎ D)))
        ↔⟨ ↔-sym $ ×⊎.+-assoc B A (C ⊎ D) ⟩
      ((B ⊎ A) ⊎ (C ⊎ D))
        ↔⟨ ×⊎.+-comm B A ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      ((A ⊎ B) ⊎ (C ⊎ D))
        ↔⟨ ×⊎.+-assoc A B (C ⊎ D) ⟩
      (A ⊎ B ⊎ C ⊎ D) ∎

--