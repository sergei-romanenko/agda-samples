module Tree where

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
  --using(_×_; _,_; proj₁; proj₂)
open import Data.Sum

open import Algebra
  using (module CommutativeSemiring)

open import Function
open import Function.Inverse
  using (_↔_; module Inverse)

open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)

private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

open import Relation.Binary.Sum
  using (_⊎-cong_)
open import Relation.Binary.Product.Pointwise
  using (_×-cong_)

open import Algebra
  using (module CommutativeSemiring)

open import Relation.Binary.PropositionalEquality

import Function.Related as Related
module ~-Reasoning = Related.EquationalReasoning
  renaming (sym to ↔-sym)

------------------------------------------------------------------------
-- Binary trees

data Tree {a} (A : Set a) : Set a where
  leaf : Tree A
  node : (l : Tree A) (x : A) (r : Tree A) → Tree A

-- Any.

AnyT : ∀ {a p} {A : Set a} → (A → Set p) → Tree A → Set (a ⊔ p)
AnyT P leaf         = Lift ⊥
AnyT P (node l x r) = AnyT P l ⊎ P x ⊎ AnyT P r

-- Membership.

_∈T_ : ∀ {a} {A : Set a} → A → Tree A → Set a
x ∈T t = AnyT (_≡_ x) t

-- Bag equivalence.

_≈-bagT_ : ∀ {a} {A : Set a} → Tree A → Tree A → Set a
t₁ ≈-bagT t₂ = ∀ x → x ∈T t₁ ↔ x ∈T t₂

------------------------------------------------------------------------
-- Singleton

-- Singleton trees.

singleton : ∀ {a} {A : Set a} → A → Tree A
singleton x = node leaf x leaf

-- Any lemma for singleton.

AnyT-singleton : ∀ {A : Set} (P : A → Set) {x} →
                AnyT P (singleton x) ↔ P x
AnyT-singleton P {x} =
  AnyT P (singleton x)
    ≡⟨ refl ⟩
  (Lift ⊥ ⊎ (P x ⊎ Lift ⊥))
    ↔⟨ proj₁ ×⊎.+-identity (P x ⊎ Lift ⊥) ⟩
  (P x ⊎ Lift ⊥)
    ↔⟨ proj₂ ×⊎.+-identity (P x) ⟩
  P x ∎
  where open ~-Reasoning

{-
AnyT↔ : ∀ {a p} {A : Set a} {P : A → Set p} {t} →
       (∃ λ x → x ∈T t × P x) ↔ AnyT P t
AnyT↔ = {!!}
-}

------------------------------------------------------------------------
-- Flatten

-- Inorder flattening of a tree.

flatten : {A : Set} → Tree A → List A
flatten leaf         = []
flatten (node l x r) = flatten l ++ x ∷ flatten r

-- Flatten does not add or remove any elements.

Lift⊥↔ : ∀ {ℓ} → Lift {Level.zero} {ℓ} ⊥ ↔ ⊥
Lift⊥↔ = record
  { to = →-to-⟶ lower
  ; from = →-to-⟶ lift
  ; inverse-of = record
    { left-inverse-of = λ _ → refl
    ; right-inverse-of = λ ()
    }
  }

flatten↔ : {A : Set} (t : Tree A) → ∀ z → z ∈ flatten t ↔ z ∈T t
flatten↔ leaf z =
  z ∈ flatten leaf
    ↔⟨ _ ∎ ⟩
  Any (_≡_ z) []
    ↔⟨ ↔-sym $ ⊥↔Any[] ⟩
  ⊥
    ↔⟨ ↔-sym $ Lift⊥↔ ⟩
  Lift ⊥ ∎
  where open ~-Reasoning

flatten↔ (node l x r) z =
  z ∈ flatten (node l x r)
    ↔⟨ _ ∎ ⟩
  z ∈ flatten l ++ x ∷ flatten r
    ↔⟨ ↔-sym $ ++↔ ⟩
  (z ∈ flatten l ⊎ z ∈ x ∷ flatten r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ↔-sym (∷↔ (_≡_ z)) ⟩
  (z ∈ flatten l ⊎ z ≡ x ⊎ z ∈ flatten r)
    ↔⟨ flatten↔ l z ⟨ ×⊎.+-cong ⟩ (_ ∎ ⟨ ×⊎.+-cong ⟩ flatten↔ r z) ⟩
  (z ∈T l ⊎ z ≡ x ⊎ z ∈T r)
    ↔⟨ _ ∎ ⟩
  z ∈T (node l x r) ∎
  where open ~-Reasoning

--
