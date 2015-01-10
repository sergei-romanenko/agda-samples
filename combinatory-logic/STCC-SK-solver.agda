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

open import STCC-SK-norm

--
-- Now the goal is to prove the decidability of ≈ :
--     Dec (x ≈ y)
-- The proof is very simple, but it is based on
--     Dec (x ≡ y)
-- whose proof is rather tedious...

--
-- The equality of Ty-values is decidable.
--

-- ⇒-injective

⇒-injective : ∀ {α α′ β β′} →
  α ⇒ α′ ≡ β ⇒ β′ →  α ≡ β × α′ ≡ β′

⇒-injective refl = refl , refl

-- Dec (α ≡ β)

_≟ty_ : (α β : Ty) → Dec (α ≡ β)

⋆ ≟ty ⋆ = yes refl
⋆ ≟ty (β ⇒ β′) = no (λ ())
(α ⇒ α′) ≟ty ⋆ = no (λ ())
(α ⇒ α′) ≟ty (β ⇒ β′) with α ≟ty β
... | no  α≢β = no (α≢β ∘ proj₁ ∘ ⇒-injective)
... | yes α≡β with α′ ≟ty β′
... | no  α′≢β′ = no (α′≢β′ ∘ proj₂ ∘ ⇒-injective)
... | yes α′≡β′ = yes (cong₂ _⇒_ α≡β α′≡β′)

--
-- The equality of Tm-values is decidable.
--

-- x ∙ x′ ≅ y ∙ y′ →  x ≅ y × x′ ≅ y′

∙-≅injective :
  ∀ {α α′ β β′} {x : Tm (α ⇒ α′)} {x′ : Tm α} {y : Tm (β ⇒ β′)} {y′ : Tm β} →
  x ∙ x′ ≅ y ∙ y′ →  x ≅ y × x′ ≅ y′

∙-≅injective H.refl = H.refl , H.refl

-- α ≢ β → x ≇ y

≢ty→≇tm : ∀ {α} (x : Tm α) {β} (y : Tm β) → α ≢ β → x ≇ y

≢ty→≇tm K K α≢β H.refl = α≢β refl
≢ty→≇tm K S α≢β ()
≢ty→≇tm K (y ∙ y′) α≢β ()
≢ty→≇tm S K α≢β ()
≢ty→≇tm S S α≢β H.refl = α≢β refl
≢ty→≇tm S (y ∙ y′) α≢β ()
≢ty→≇tm (x ∙ x′) K α≢β ()
≢ty→≇tm (x ∙ x′) S α≢β ()
≢ty→≇tm (x ∙ x′) (.x ∙ .x′) α≢β H.refl = α≢β refl

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

x ≈? y with norm x ≟tm norm  y
... | yes nx≡ny = yes x≈y
  where
  open ≈-Reasoning
  x≈y = begin
    x
      ≈⟨ norm-sound x ⟩
    norm x
      ≡⟨ nx≡ny ⟩
    norm y
      ≈⟨ ≈sym $ norm-sound y ⟩
    y
    ∎
... | no  nx≢ny =
  no (λ x≈y → nx≢ny (norm-complete x≈y))
