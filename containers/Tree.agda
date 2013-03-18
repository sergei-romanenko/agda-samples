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

------------------------------------------------------------------------
-- Binary trees

data Tree {a} (A : Set a) : Set a where
  leaf : Tree A
  node : (l : Tree A) (x : A) (r : Tree A) → Tree A

-- AnyT.

data AnyT {a p} {A : Set a} (P : A → Set p) : Tree A → Set (a ⊔ p) where
  here  : ∀ {x t₁ t₂} (px : P x) → AnyT P (node t₁ x t₂)
  thereˡ : ∀ {x t₁ t₂} (pt₁ : AnyT P t₁) → AnyT P (node t₁ x t₂)
  thereʳ : ∀ {x t₁ t₂} (pt₂ : AnyT P t₂) → AnyT P (node t₁ x t₂)

-- Positions

data TreeP : Set where
  zero : TreeP
  sucˡ : TreeP → TreeP
  sucʳ : TreeP → TreeP

indexT : ∀ {a p} {A : Set a} {P : A → Set p} {t} → (h : AnyT P t) → TreeP
indexT (here px) = zero
indexT (thereˡ pt₁) = sucˡ (indexT pt₁)
indexT (thereʳ pt₂) = sucʳ (indexT pt₂)

-- Tree Membership.

infix 4 _∈T_ _∉T_

_∈T_ : ∀ {a} {A : Set a} → A → Tree A → Set a
x ∈T t = AnyT (_≡_ x) t

_∉T_ : ∀ {a} {A : Set a} → A → Tree A → Set a
x ∉T t = ¬ x ∈T t

-- Bag equivalence.

_≈-bagT_ : ∀ {a} {A : Set a} → Tree A → Tree A → Set a
t₁ ≈-bagT t₂ = ∀ x → x ∈T t₁ ↔ x ∈T t₂

-- Lift⊥↔⊥

Lift⊥↔⊥ : ∀ {ℓ} → Lift {Level.zero} {ℓ} ⊥ ↔ ⊥
Lift⊥↔⊥ {ℓ} = record
  { to = →-to-⟶ lower
  ; from = →-to-⟶ lift
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = λ ()
    }
  }
  where
    from∘to : (h : Lift ⊥) → lift (lower h) ≡ h
    from∘to (lift ())

-- ⊎⊥

⊎⊥ : ∀ {A : Set} → (A ⊎ ⊥) ↔ A
⊎⊥ {A} =
  (A ⊎ ⊥)
    ↔⟨ ×⊎.+-cong (_ ∎) (↔-sym $ Lift⊥↔⊥) ⟩
  (A ⊎ Lift ⊥)
    ↔⟨ proj₂ ×⊎.+-identity A ⟩
  A ∎
  where open ~-Reasoning

-- AnyT-leaf

AnyT-leaf : ∀ {a} {A : Set a} {P : A → Set} →
  AnyT P leaf ↔ ⊥
AnyT-leaf {P = P} = record
  { to = →-to-⟶ (λ ())
  ; from = →-to-⟶ (λ ())
  ; inverse-of = record
    { left-inverse-of = λ ()
    ; right-inverse-of = λ ()
    }
  }

-- AnyT-node

AnyT-node : ∀ {a p} {A : Set a} {P : A → Set p} {x l r} →
  AnyT P (node l x r) ↔ (P x ⊎ AnyT P l ⊎ AnyT P r)
AnyT-node {P = P} {x} {l} {r} = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
    to : AnyT P (node l x r) → P x ⊎ AnyT P l ⊎ AnyT P r

    to (here px) = inj₁ px
    to (thereˡ pt₁) = inj₂ (inj₁ pt₁)
    to (thereʳ pt₂) = inj₂ (inj₂ pt₂)

    from : P x ⊎ AnyT P l ⊎ AnyT P r → AnyT P (node l x r)
    from = [ here , [ thereˡ , thereʳ ]′ ]′

    from∘to : (h : AnyT P (node l x r)) → from (to h) ≡ h
    from∘to (here px) = refl
    from∘to (thereˡ pt₁) = refl
    from∘to (thereʳ pt₂) = refl

    to∘from : (h : P x ⊎ AnyT P l ⊎ AnyT P r) → to (from h) ≡ h
    to∘from (inj₁ px) = refl
    to∘from (inj₂ (inj₁ pt₁)) = refl
    to∘from (inj₂ (inj₂ pt₂)) = refl

-- AnyT↔

AnyT↔ : ∀ {a p} {A : Set a} {P : A → Set p} {t : Tree A} →
       (∃ λ x → x ∈T t × P x) ↔ AnyT P t
AnyT↔ {P = P} {t} = record
  { to = →-to-⟶ (to t)
  ; from = →-to-⟶ (from t)
  ; inverse-of = record
    { left-inverse-of = from∘to t
    ; right-inverse-of = to∘from t
    }
  }
  where
    to : ∀ t → ∃ (λ x → x ∈T t × P x) → AnyT P t

    to leaf (x , () , px)
    to (node l y r) (x , here x≡y , px) rewrite sym x≡y = here px
    to (node l _ r) (x , thereˡ pt₁ , px) = thereˡ (to l (x , pt₁ , px))
    to (node l _ r) (x , thereʳ pt₂ , px) = thereʳ (to r (x , pt₂ , px))

    from : ∀ t → AnyT P t → ∃ (λ x → x ∈T t × P x)

    from leaf ()
    from (node l x′ r) (here px) = x′ , here refl , px
    from (node l x′ r) (thereˡ pt₁) with from l pt₁
    ... | x , x∈Tt₁ , px = x , thereˡ x∈Tt₁ , px
    from (node l x′ r) (thereʳ pt₂) with from r pt₂
    ... | x , x∈Tt₂ , px = x , thereʳ x∈Tt₂ , px

    from∘to : ∀ t → (h : ∃ λ x → x ∈T t × P x) → from t (to t h) ≡ h

    from∘to leaf (x , () , px)
    from∘to (node l y r) (x , here x≡y , px) rewrite x≡y = refl
    from∘to (node l y r) (x , thereˡ pt₁ , px) with from∘to l (x , pt₁ , px)
    ... | eq rewrite eq = refl
    from∘to (node l y r) (x , thereʳ pt₂ , px) with from∘to r (x , pt₂ , px)
    ... | eq rewrite eq = refl

    to∘from : ∀ t → (h : AnyT P t) → to t (from t h) ≡ h

    to∘from leaf ()
    to∘from (node l y r) (here px) = refl
    to∘from (node l y r) (thereˡ pt₁) with to∘from l pt₁
    ... | eq rewrite eq = refl
    to∘from (node l y r) (thereʳ pt₂) with to∘from r pt₂
    ... | eq rewrite eq = refl

-- Singleton

-- Singleton trees.

singleton : ∀ {a} {A : Set a} → A → Tree A
singleton x = node leaf x leaf

-- Any lemma for singleton.

AnyT-singleton : ∀ {A : Set} (P : A → Set) {x} →
                AnyT P (singleton x) ↔ P x
AnyT-singleton P {x} =
  AnyT P (singleton x)
    ↔⟨ _ ∎ ⟩
  AnyT P (node leaf x leaf)
    ↔⟨ AnyT-node ⟩
  (P x ⊎ AnyT P leaf ⊎ AnyT P leaf)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (AnyT-leaf ⟨ ×⊎.+-cong ⟩ AnyT-leaf) ⟩
  (P x ⊎ ⊥ ⊎ ⊥)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ⊎⊥ ⟩
  (P x ⊎ ⊥)
    ↔⟨ ⊎⊥ ⟩
  P x ∎
  where open ~-Reasoning

------------------------------------------------------------------------
-- Flatten

-- Inorder flattening of a tree.

flatten : ∀ {a} {A : Set a} → Tree A → List A
flatten leaf         = []
flatten (node l x r) = flatten l ++ x ∷ flatten r

-- Flatten does not add or remove any elements.

flatten↔ : ∀ {A : Set} (t : Tree A) → ∀ (x : A) →
  x ∈ flatten t ↔ x ∈T t

flatten↔ leaf x =
  x ∈ flatten leaf
    ↔⟨ _ ∎ ⟩
  Any (_≡_ x) []
    ↔⟨ ↔-sym $ ⊥↔Any[] ⟩
  ⊥
    ↔⟨ ↔-sym $ AnyT-leaf ⟩
  AnyT (_≡_ x) leaf
    ↔⟨ _ ∎ ⟩
  x ∈T leaf ∎
  where open ~-Reasoning

flatten↔ (node l y r) x =
  x ∈ flatten (node l y r)
    ↔⟨ _ ∎ ⟩
  x ∈ flatten l ++ y ∷ flatten r
    ↔⟨ ↔-sym $ ++↔ ⟩
  (x ∈ flatten l ⊎ x ∈ y ∷ flatten r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ↔-sym (∷↔ (_≡_ x)) ⟩
  (x ∈ flatten l ⊎ x ≡ y ⊎ x ∈ flatten r)
    ↔⟨ helper ⟩
  (x ≡ y ⊎ x ∈ flatten l ⊎ x ∈ flatten r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (flatten↔ l x ⟨ ×⊎.+-cong ⟩ flatten↔ r x) ⟩
  (x ≡ y ⊎ x ∈T l ⊎ x ∈T r)
    ↔⟨ ↔-sym AnyT-node ⟩
  x ∈T node l y r ∎
  where
    open ~-Reasoning
    helper : ∀ {ℓ} {A B C : Set ℓ} → (A ⊎ B ⊎ C) ↔ (B ⊎ (A ⊎ C))
    helper {ℓ} {A} {B} {C} =
      (A ⊎ B ⊎ C)    ↔⟨ ↔-sym $ ×⊎.+-assoc A B C ⟩
      ((A ⊎ B) ⊎ C)  ↔⟨ ×⊎.+-comm A B ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      ((B ⊎ A) ⊎ C)  ↔⟨ ×⊎.+-assoc B A C ⟩
      (B ⊎ (A ⊎ C))  ∎

--
