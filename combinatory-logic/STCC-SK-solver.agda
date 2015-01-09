{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  Based on

    Thierry Coquand and Peter Dybjer. 1997.
    Intuitionistic model constructions and normalization proofs.
    Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
    DOI=10.1017/S0960129596002150 http://dx.doi.org/10.1017/S0960129596002150 

  and

    Peter Dybjer and Andrzej Filinski. 2000.
    Normalization and Partial Evaluation.
    In Applied Semantics, International Summer School, APPSEM 2000, Caminha,
    Portugal, September 9-15, 2000, Advanced Lectures,
    Gilles Barthe, Peter Dybjer, Luis Pinto, and João Saraiva (Eds.).
    Springer-Verlag, London, UK, UK, 137-192. 

-}

module STCC-SK-solver where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

open import Relation.Binary.HeterogeneousEquality as H
  using (_≅_; _≇_; ≡-to-≅; ≅-to-≡; module ≅-Reasoning)

open import STCC-SK

--
-- Now the goal is to prove the decidability of ≈
-- The proof is very simple, but is based on the decidability
-- of the equality of Tm-values, which is conceptually simple
-- but is rather tedious...

--
-- The equality of Ty-values is decidable.
--

-- ⇒-injective

⇒-injective : ∀ {α₁ α₂ β₁ β₂} →
  α₁ ⇒ β₁ ≡ α₂ ⇒ β₂ →  α₁ ≡ α₂ × β₁ ≡ β₂
⇒-injective refl = refl , refl

-- _≟ty_

_≟ty_ : (α₁ α₂ : Ty) → Dec (α₁ ≡ α₂)
⋆ ≟ty ⋆ = yes refl
⋆ ≟ty (α₂ ⇒ α₃) = no (λ ())
(α₁ ⇒ β₁) ≟ty ⋆ = no (λ ())
(α₁ ⇒ β₁) ≟ty (α₂ ⇒ β₂) with α₁ ≟ty α₂
... | no  α₁≢α₂ = no (α₁≢α₂ ∘ proj₁ ∘ ⇒-injective)
... | yes α₁≡α₂ with β₁ ≟ty β₂
... | no  β₁≢β₂ = no (β₁≢β₂ ∘ proj₂ ∘ ⇒-injective)
... | yes β₁≡β₂ = yes (cong₂ _⇒_ α₁≡α₂ β₁≡β₂)

--
-- The equality of Tm-values is decidable.
--

-- x ∙ x′ ≅ y ∙ y′ →  x ≅ y × x′ ≅ y′

∙-≅injective :
  ∀ {α α′ β β′} {x : Tm (α ⇒ α′)} {x′ : Tm α} {y : Tm (β ⇒ β′)} {y′ : Tm β} →
  x ∙ x′ ≅ y ∙ y′ →  x ≅ y × x′ ≅ y′
∙-≅injective H.refl = H.refl , H.refl

-- α₁ ≢ α₂ → x₁ ≇ x₂

≢ty→≇tm : ∀ {α₁} (x₁ : Tm α₁) {α₂} (x₂ : Tm α₂) → α₁ ≢ α₂ → x₁ ≇ x₂
≢ty→≇tm K K α₁≢α₂ H.refl = α₁≢α₂ refl
≢ty→≇tm K S α₁≢α₂ ()
≢ty→≇tm K (x₂ ∙ y₂) α₁≢α₂ ()
≢ty→≇tm S K α₁≢α₂ ()
≢ty→≇tm S S α₁≢α₂ H.refl = α₁≢α₂ refl
≢ty→≇tm S (x₂ ∙ x₃) α₁≢α₂ ()
≢ty→≇tm (x₁ ∙ y₁) K α₁≢α₂ ()
≢ty→≇tm (x₁ ∙ y₁) S α₁≢α₂ ()
≢ty→≇tm (x₂ ∙ y₂) (.x₂ ∙ .y₂) α₁≢α₂ H.refl = α₁≢α₂ refl

-- x ≅ y → α ≡ β

≅tm→≡ty : ∀ {α} (x : Tm α) {β} (y : Tm β) → x ≅ y → α ≡ β
≅tm→≡ty K K H.refl = refl
≅tm→≡ty K S ()
≅tm→≡ty K (y ∙ y′) ()
≅tm→≡ty S K ()
≅tm→≡ty S S H.refl = refl
≅tm→≡ty S (y ∙ y′) ()
≅tm→≡ty (x ∙ x′) K ()
≅tm→≡ty (x ∙ x′) S ()
≅tm→≡ty (y ∙ y′) (.y ∙ .y′) H.refl = refl

--
-- Dec (x ≅ y)
--

mutual

  _≅tm?_ : ∀ {α} (x : Tm α) {β} (y : Tm β) → Dec (x ≅ y)
  _≅tm?_ {α} x {β} y with α ≟ty β
  ... | yes α≡β rewrite α≡β = x ≅tm?′ y
  ... | no  α≢β = no (≢ty→≇tm x y α≢β)

  _≅tm?′_ : ∀ {α} (x : Tm α) (y : Tm α) → Dec (x ≅ y)
  K ≅tm?′ K = yes H.refl
  K ≅tm?′ (y ∙ y′) = no (λ ())
  S ≅tm?′ S = yes H.refl
  S ≅tm?′ (y ∙ y′) = no (λ ())
  (x ∙ x′) ≅tm?′ K = no (λ ())
  (x ∙ x′) ≅tm?′ S = no (λ ())
  (x ∙ x′) ≅tm?′ (y ∙ y′) with x ≅tm? y
  ... | no  x≇y = no (x≇y ∘ proj₁ ∘ ∙-≅injective)
  ... | yes x≅y  with x′ ≅tm? y′
  ... | no  x′≇y′ = no (x′≇y′ ∘ proj₂ ∘ ∙-≅injective)
  ... | yes x′≅y′ = yes (∙≅tm∙ (≅tm→≡ty x′ y′ x′≅y′) x≅y x′≅y′)

  ∙≅tm∙ : ∀ {α β γ} {x : Tm (α ⇒ γ)} {x′ : Tm α} {y : Tm (β ⇒ γ)} {y′ : Tm β} →
    α ≡ β → x ≅ y → x′ ≅ y′ → x ∙ x′ ≅ y ∙ y′
  ∙≅tm∙ α≡β x≅y x′≅y′ rewrite α≡β = H.cong₂ _∙_ x≅y x′≅y′

--
-- Dec (x ≡ y)
--

_≟tm_ : ∀ {α} (x y : Tm α) → Dec (x ≡ y)
x ≟tm y with x ≅tm? y
... | yes x≅y = yes (≅-to-≡ x≅y)
... | no  x≇y = no (λ z → x≇y (≡-to-≅ z))

--
-- Finally: Dec (x ≈ y)
--

_≈?_ : ∀ {α} (x y : Tm α) → Dec (x ≈ y)
x ≈? y with ⟪ ⟦ x ⟧ ⟫ ≟tm ⟪ ⟦ y ⟧ ⟫
... | yes u≡v = yes x≈y
  where
  open ≈-Reasoning
  x≈y = begin
    x
      ≈⟨ norm-sound x ⟩
    norm x
      ≡⟨ u≡v ⟩
    norm y
      ≈⟨ ≈sym $ norm-sound y ⟩
    y
    ∎
... | no  u≢v =
  no (λ x≈y → u≢v (norm-complete x≈y))
