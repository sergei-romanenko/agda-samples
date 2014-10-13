module Tree-Container where

open import Data.Container

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product
open import Data.Sum

open import Function

open import Function.Inverse
  using (_↔_)

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong; →-to-⟶; module ≡-Reasoning)

{-

infix 5 _▷_

record Container (ℓ : Level) : Set (suc ℓ) where
  constructor _▷_
  field
    Shape    : Set ℓ
    Position : Shape → Set ℓ

⟦_⟧ : ∀ {ℓ} → Container ℓ → Set ℓ → Set ℓ
⟦ C ⟧ X = Σ[ s ∈ Shape C ] (Position C s → X)

-}

data Tree {ℓ} (A : Set ℓ) : Set ℓ where
  leaf : Tree A
  node : (x : A) → (l : Tree A) → (r : Tree A) → Tree A

-- By removing data from a tree we get its "shape".
-- TreeShape is isomorphic to Tree ⊤. ???

data TreeShape : Set where
  leaf : TreeShape
  node : (l r : TreeShape) → TreeShape

-- Positions are paths to data.

data TreePos : TreeShape → Set where
  here  : ∀ {l r} → TreePos (node l r)
  left  : ∀ {l r} → TreePos l → TreePos (node l r)
  right : ∀ {l r} → TreePos r → TreePos (node l r)

-- Now we produce a tree container

TreeContainer : Container _
TreeContainer = TreeShape ▷ TreePos

posToLabel : ∀ {ℓ} {A : Set ℓ} {s₁ s₂}
  (x : A) (f₁ : TreePos s₁ → A) (f₂ : TreePos s₂ → A)
  (p : TreePos (node s₁ s₂)) → A
posToLabel x f₁ f₂ here = x
posToLabel x f₁ f₂ (left p) = f₁ p
posToLabel x f₁ f₂ (right p) = f₂ p


-- `⟦ TreeContainer ⟧ A` and `Tree A` are isomorphic
-- (assuming the extensionality).

Tree↔TreeContainer : (ext : ∀ {ℓ} → P.Extensionality ℓ ℓ) →
  ∀ (A : Set) → ⟦ TreeContainer ⟧ A  ↔ Tree A

Tree↔TreeContainer ext A = record
  { to = →-to-⟶ to
  ; from = →-to-⟶ from
  ; inverse-of = record
    { left-inverse-of = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where

  to′ : (s : TreeShape) (f : TreePos s → A) → Tree A
  to′ leaf f = leaf
  to′ (node s₁ s₂) f = 
    node (f here) (to′ s₁ (f ∘ left)) (to′ s₂ (f ∘ right))

  to : Σ[ s ∈ TreeShape ] (TreePos s → A) → Tree A
  to = uncurry to′

  from : Tree A → Σ[ s ∈ TreeShape ] (TreePos s → A)
  from leaf = leaf , (λ ())
  from (node x t₁ t₂) with from t₁ | from t₂
  ... | s₁ , f₁ | s₂ , f₂ = node s₁ s₂ , posToLabel x f₁ f₂

  from∘to′ : (s : TreeShape) (f : TreePos s → A) → from (to′ s f) ≡ (s , f)
  from∘to′ leaf f = cong (_,_ leaf) (ext (λ ()))
  from∘to′ (node s₁ s₂) f
    with from∘to′ s₁ (f ∘ left) | from∘to′ s₂ (f ∘ right)
  ... | ≡₁ | ≡₂ rewrite ≡₁ | ≡₂ = cong (_,_ (node s₁ s₂))(ext eq)
    where
    eq : (p : TreePos (node s₁ s₂)) →
      posToLabel (f here) (λ x → f (left x)) (λ x → f (right x)) p ≡ f p
    eq here = refl
    eq (left p) = refl
    eq (right p) = refl

  from∘to : (c : Σ[ s ∈ TreeShape ]  (TreePos s → A)) → from (to c) ≡ c
  from∘to = uncurry from∘to′

  to∘from : (t : Tree A) → to (from t) ≡ t
  to∘from leaf = refl
  to∘from (node x t₁ t₂) with to∘from t₁ | to∘from t₂
  ... | ≡t₁ | ≡t₂ rewrite ≡t₁ | ≡t₂ = refl
