open import Data.Bool

module TreeSort-Partial
  {A : Set}
  (_≤_ : A → A → Bool) -- A comparison function.
  where

open import Level
  using (Level; _⊔_; Lift; lift; lower)

open import Data.List
open import Data.List.Any as Any
  using (Any; here; there)
open Any.Membership-≡

open import Data.List.Any.Properties
  using (⊥↔Any[]; ++↔; ∷↔)

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

open import Relation.Binary.PropositionalEquality as P
  using (_≡_)

import Function.Related as Related

open import Tree

------------------------------------------------------------------------
-- Insertion into trees


-- Inserts an element into the tree.
-- Insertion of n into xs at the right place
-- (assuming that xs is sorted)

insert : ∀ (x : A) (t : Tree A) → Tree A
insert x leaf = node leaf x leaf
insert x (node l y r) with x ≤ y
... | true  = node (insert x l) y r
... | false = node l y (insert x r)

-- The insert function inserts.

AnyT-insert : ∀ (P : A → Set) (x : A) (t : Tree A) →
               AnyT P (insert x t) ↔ (P x ⊎ AnyT P t)

AnyT-insert P x leaf =
  AnyT P (insert x leaf)
    ↔⟨ _ ∎ ⟩
  AnyT P (node leaf x leaf)
    ↔⟨ AnyT-node ⟩
  (AnyT P leaf ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ AnyT-leaf ⟨ ×⊎.+-cong ⟩ _ ∎  ⟩
  (Lift ⊥ ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ proj₁ ×⊎.+-identity (P x ⊎ AnyT P leaf) ⟩
  (P x ⊎ AnyT P leaf) ∎
  where open Related.EquationalReasoning

AnyT-insert P x (node l y r) with x ≤ y
... | true =
  AnyT P (node (insert x l) y r)
    ↔⟨ AnyT-node ⟩
  (AnyT P (insert x l) ⊎ P y ⊎ AnyT P r)
    ↔⟨ AnyT-insert P x l ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
  ((P x ⊎ AnyT P l) ⊎ P y ⊎ AnyT P r)
    ↔⟨ ×⊎.+-assoc (P x) (AnyT P l) (P y ⊎ AnyT P r) ⟩
  (P x ⊎ (AnyT P l ⊎ P y ⊎ AnyT P r))
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (sym $ AnyT-node) ⟩
  (P x ⊎ AnyT P (node l y r)) ∎
  where open Related.EquationalReasoning
... | false =
  AnyT P (node l y (insert x r))
    ↔⟨ AnyT-node ⟩
  (AnyT P l ⊎ P y ⊎ AnyT P (insert x r))
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (_ ∎ ⟨ ×⊎.+-cong ⟩ AnyT-insert P x r) ⟩
  (AnyT P l ⊎ P y ⊎ P x ⊎ AnyT P r)
    ↔⟨ shuffle ⟩
  (P x ⊎ AnyT P l ⊎ P y ⊎ AnyT P r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (sym $ AnyT-node) ⟩
  (P x ⊎ AnyT P (node l y r)) ∎
  where
    open Related.EquationalReasoning
    shuffle : ∀ {A B C D : Set} → ((B ⊎ C ⊎ A ⊎ D) ↔ (A ⊎ B ⊎ C ⊎ D))
    shuffle {A} {B} {C} {D} =
      (B ⊎ (C ⊎ A ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (sym $ ×⊎.+-assoc C A D) ⟩
      (B ⊎ ((C ⊎ A) ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (×⊎.+-comm C A ⟨ ×⊎.+-cong ⟩ _ ∎) ⟩
      (B ⊎ ((A ⊎ C) ⊎ D))
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ×⊎.+-assoc A C D ⟩
      (B ⊎ (A ⊎ (C ⊎ D)))
        ↔⟨ sym $ ×⊎.+-assoc B A (C ⊎ D) ⟩
      ((B ⊎ A) ⊎ (C ⊎ D))
        ↔⟨ ×⊎.+-comm B A ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      ((A ⊎ B) ⊎ (C ⊎ D))
        ↔⟨ ×⊎.+-assoc A B (C ⊎ D) ⟩
      (A ⊎ B ⊎ C ⊎ D) ∎

------------------------------------------------------------------------
-- Turning a list into a search tree

-- Converts the list to a search tree.

to-search-tree : List A → Tree A
to-search-tree = foldr insert leaf

-- No elements are added or removed.

to-search-tree↔ : ∀ x xs → x ∈T to-search-tree xs ↔ x ∈ xs
to-search-tree↔ x [] =
  x ∈T to-search-tree []
    ↔⟨ AnyT-leaf ⟩
  Lift ⊥
    ↔⟨ Lift⊥↔Any[] ⟩
  x ∈ [] ∎
  where open Related.EquationalReasoning
to-search-tree↔ x (y ∷ xs) =
  x ∈T to-search-tree (y ∷ xs)
    ↔⟨ _ ∎ ⟩
  x ∈T insert y (to-search-tree xs)
    ↔⟨ AnyT-insert (_≡_ x) y (to-search-tree xs) ⟩
  (x ≡ y ⊎ x ∈T to-search-tree xs)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ to-search-tree↔ x xs ⟩
  (x ≡ y ⊎ x ∈ xs)
    ↔⟨ ∷↔ (_≡_ x) ⟩
  x ∈ y ∷ xs ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

tree-sort : List A → List A
tree-sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

tree-sort-permutes : ∀ {x xs} → x ∈ tree-sort xs ↔ x ∈ xs
tree-sort-permutes {x} {xs} =
  x ∈ tree-sort xs
    ↔⟨ _ ∎ ⟩
  x ∈  flatten (to-search-tree xs)
    ↔⟨ flatten↔ (to-search-tree xs) x ⟩
  x ∈T to-search-tree xs
    ↔⟨ to-search-tree↔ x xs ⟩
  x ∈ xs ∎
  where open Related.EquationalReasoning

--
