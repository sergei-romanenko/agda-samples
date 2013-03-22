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
  using (_≡_; refl; →-to-⟶)

import Function.Related as Related

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
  AnyT P (node l x r) ↔ (AnyT P l ⊎ P x ⊎ AnyT P r)
AnyT-node {P = P} {x} {l} {r} = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
    to : AnyT P (node l x r) → AnyT P l ⊎ P x ⊎ AnyT P r
    to (here px) = inj₂ (inj₁ px)
    to (thereˡ pt₁) = inj₁ pt₁
    to (thereʳ pt₂) = inj₂ (inj₂ pt₂)

    from : AnyT P l ⊎ P x ⊎ AnyT P r → AnyT P (node l x r)
    from = [ thereˡ , [ here , thereʳ ]′ ]′

    from∘to : (h : AnyT P (node l x r)) → from (to h) ≡ h
    from∘to (here px) = refl
    from∘to (thereˡ pt₁) = refl
    from∘to (thereʳ pt₂) = refl

    to∘from : (h : AnyT P l ⊎ P x ⊎ AnyT P r) → to (from h) ≡ h
    to∘from (inj₁ px) = refl
    to∘from (inj₂ (inj₁ pt₁)) = refl
    to∘from (inj₂ (inj₂ pt₂)) = refl

-- AnyT↔

AnyT↔ : ∀ {a p} {A : Set a} {P : A → Set p} {t : Tree A} →
       (∃ λ x → x ∈T t × P x) ↔ AnyT P t
AnyT↔ {P = P} {t} = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
    to : ∀ {t} → ∃ (λ x → x ∈T t × P x) → AnyT P t

    to (x , here x≡y , px) rewrite P.sym x≡y = here px
    to (x , thereˡ pt₁ , px) = thereˡ (to (x , pt₁ , px))
    to (x , thereʳ pt₂ , px) = thereʳ (to (x , pt₂ , px))

    from : ∀ {t} → AnyT P t → ∃ (λ x → x ∈T t × P x)

    from {node _ x _} (here px) =
      x , here refl , px
    from (thereˡ pt₁) with from pt₁
    ... | x , x∈Tt₁ , px = x , thereˡ x∈Tt₁ , px
    from (thereʳ pt₂) with from pt₂
    ... | x , x∈Tt₂ , px = x , thereʳ x∈Tt₂ , px

    from∘to : ∀ {t} → (h : ∃ λ x → x ∈T t × P x) → from (to h) ≡ h

    from∘to (x , here x≡y , px)
      rewrite x≡y = refl
    from∘to (x , thereˡ pt₁ , px)
      rewrite from∘to (x , pt₁ , px) = refl
    from∘to (x , thereʳ pt₂ , px)
      rewrite from∘to (x , pt₂ , px) = refl

    to∘from : ∀ {t} → (h : AnyT P t) → to (from h) ≡ h

    to∘from (here px) = refl
    to∘from (thereˡ pt₁) rewrite to∘from pt₁ = refl
    to∘from (thereʳ pt₂) rewrite to∘from pt₂ = refl

-- Singleton trees.

AnyT-singleton : ∀ {A : Set} (P : A → Set) {x} →
                AnyT P (node leaf x leaf) ↔ P x
AnyT-singleton P {x} =
  AnyT P (node leaf x leaf)
    ↔⟨ AnyT-node ⟩
  (AnyT P leaf ⊎ P x ⊎ AnyT P leaf)
    ↔⟨ AnyT-leaf ⟨ ×⊎.+-cong ⟩ ((_ ∎) ⟨ ×⊎.+-cong ⟩ AnyT-leaf) ⟩
  (⊥ ⊎ P x ⊎ ⊥)
    ↔⟨ sym Lift⊥↔⊥ ⟨ ×⊎.+-cong ⟩ (_ ∎ ⟨ ×⊎.+-cong ⟩ sym Lift⊥↔⊥) ⟩
  (Lift ⊥ ⊎ P x ⊎ Lift ⊥)
    ↔⟨ proj₁ ×⊎.+-identity (P x ⊎ Lift ⊥) ⟩
  (P x ⊎ Lift ⊥)
    ↔⟨ proj₂ ×⊎.+-identity (P x) ⟩
  P x ∎
  where open Related.EquationalReasoning

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
    ↔⟨ sym $ ⊥↔Any[] ⟩
  ⊥
    ↔⟨ sym $ AnyT-leaf ⟩
  AnyT (_≡_ x) leaf
    ↔⟨ _ ∎ ⟩
  x ∈T leaf ∎
  where open Related.EquationalReasoning

flatten↔ (node l y r) x =
  x ∈ flatten (node l y r)
    ↔⟨ _ ∎ ⟩
  x ∈ flatten l ++ y ∷ flatten r
    ↔⟨ sym $ ++↔ ⟩
  (x ∈ flatten l ⊎ x ∈ y ∷ flatten r)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ sym (∷↔ (_≡_ x)) ⟩
  (x ∈ flatten l ⊎ x ≡ y ⊎ x ∈ flatten r)
    ↔⟨ flatten↔ l x ⟨ ×⊎.+-cong ⟩ (_ ∎ ⟨ ×⊎.+-cong ⟩ flatten↔ r x) ⟩
  (x ∈T l ⊎ x ≡ y ⊎ x ∈T r)
    ↔⟨ sym AnyT-node ⟩
  x ∈T node l y r ∎
  where open Related.EquationalReasoning

--
