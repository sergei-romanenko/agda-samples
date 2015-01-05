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

module STCC-SK where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Reduction.
--

infix 4 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K :  ∀ {α β} {x : Tm α} {y : Tm β} →
             K ∙ x ∙ y ⟶ x
  ⟶S :  ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
             S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶AL : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y   : Tm α} →
             x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y
  ⟶AR : ∀ {α β} {x : Tm (α ⇒ β)} {y y′ : Tm α} →
             y ⟶ y′  →  x ∙ y ⟶ x ∙ y′

-- Reflexive and transitive closure of _⟶_ .

infix 4 _⟶*_

data _⟶*_ : ∀ {α} → Tm α → Tm α → Set where
  here  : ∀ {α} {t : Tm α} →
            t ⟶* t
  there : ∀ {α} {t1 t2 t3 : Tm α} →
            t1 ⟶  t2  →  t2 ⟶* t3  →  t1 ⟶* t3

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Tm α) → (I {α}) ∙ x ⟶* x
reduction-example x = there ⟶S (there ⟶K here)

--
-- Normal forms.
-- 

data Nf : Ty → Set where
  K0 : ∀ {α β} →
         Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} (u : Nf α) →
         Nf (β ⇒ α)
  S0 : ∀ {α β γ} →
         Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) →
         Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β))→
         Nf (α ⇒ γ)

reify : ∀ {α} (n : Nf α) → Tm α
reify K0 = K
reify (K1 u) = K ∙ reify u
reify S0 = S
reify (S1 u) = S ∙ reify u
reify (S2 u v) = S ∙ reify u ∙ reify v

--
-- `reify u` does return a term that cannot be reduced).
--

Normal-form : ∀ {α} (x : Tm α) → Set
Normal-form x = ∄ (λ y → x ⟶ y)

reify→nf : ∀ {α} (u : Nf α) → Normal-form (reify u)
reify→nf K0 (y , ())
reify→nf (K1 u) (._ , ⟶AL ())
reify→nf (K1 u) (._ , ⟶AR ⟶y) =
  reify→nf u (, ⟶y)
reify→nf S0 (y , ())
reify→nf (S1 u) (._ , ⟶AL ())
reify→nf (S1 u) (._ , ⟶AR ⟶y) =
  reify→nf u (, ⟶y)
reify→nf (S2 u v) (._ , ⟶AL (⟶AL ()))
reify→nf (S2 u v) (._ , ⟶AL (⟶AR ⟶y)) =
  reify→nf u (, ⟶y)
reify→nf (S2 u v) (._ , ⟶AR ⟶y) =
  reify→nf v (, ⟶y)

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  {-# TERMINATING #-}

  _⟨∙⟩_ : ∀ {α β} (x : Nf (α ⇒ β)) (u : Nf α) → Nf β
  K0 ⟨∙⟩ w       = K1 w
  K1 u ⟨∙⟩  w   = u
  S0 ⟨∙⟩ w       = S1 w
  S1 u ⟨∙⟩ w    = S2 u w
  S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧

  norm : ∀ {α} → Tm α → Tm α
  norm = reify ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- A "denotational" semantics for `Term α`.
--

module DenotationalNorm where

  D : (α : Ty) → Set
  D ⋆ = ⊥
  D (α ⇒ β) = D α → D β

  ⟦_⟧ : ∀ {α} (x : Tm α) → D α
  ⟦ K ⟧ = λ x y → x
  ⟦ S ⟧ = λ x y z → (x z) (y z)
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟦ y ⟧

  -- The problem is how to "reify" D-values?
  -- (= How to go back to first-order terms?)
  -- (How compare functions for equality?)

--
-- Glueing
--

G : (α : Ty) → Set
G ⋆ = ⊥
G (α ⇒ β) = Nf (α ⇒ β) × (G α → G β)

-- ⌈_⌉

⌈_⌉ : ∀ {α} (g : G α) → Nf α
⌈_⌉ {⋆} ()
⌈_⌉ {α ⇒ β} (n , f) = n

-- ⟪_⟫

⟪_⟫ : ∀ {α} (p : G α) → Tm α
⟪_⟫ = reify ∘ ⌈_⌉

-- Application for glued values

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} (p : G (α ⇒ β)) (q : G α) → G β
p ⟨∙⟩ q = proj₂ p q

--
-- Now `reflect` terminates!
--

⟦_⟧ : ∀ {α} (x : Tm α) → G α
⟦ K ⟧ =
  K0 , λ p →
    K1 ⌈ p ⌉ , λ q →
      p
⟦ S ⟧ =
  S0 , λ p →
    S1 ⌈ p ⌉ , λ q →
      S2 ⌈ p ⌉ ⌈ q ⌉ , λ r →
        (p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r)
⟦ x ∙ y ⟧ =
  ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧

--
-- Normalization.
--

norm : ∀ {α} → Tm α → Tm α
norm = ⟪_⟫ ∘ ⟦_⟧

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl

--
-- Convertibility
--

infix 4 _≈_

data _≈_  : {α : Ty} (x y : Tm α) → Set where
  ≈refl  : ∀ {α} {x : Tm α} →
             x ≈ x
  ≈sym   : ∀ {α} {x y : Tm α} →
             x ≈ y → y ≈ x
  ≈trans : ∀ {α} {x y z : Tm α} →
             x ≈ y → y ≈ z → x ≈ z
  ≈K     : ∀ {α β} {x : Tm α} {y : Tm β} →
             K ∙ x ∙ y ≈ x
  ≈S     : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
             S ∙ x ∙ y ∙ z ≈ (x ∙ z) ∙ (y ∙ z)
  ∙-cong : ∀ {α β} {x₁ x₂ : Tm (α ⇒ β)} {y₁ y₂ : Tm α} →
             x₁ ≈ x₂ → y₁ ≈ y₂ → x₁ ∙ y₁ ≈ x₂ ∙ y₂

≈setoid : {α : Ty} → Setoid _ _

≈setoid {α} = record
  { Carrier = Tm α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {α : Ty} = EqReasoning (≈setoid {α})

--
-- Soundness: the normal forms of two convertible terms are equal
--     x₁ ≈ x₂ → norm x₁ ≡ norm x₂
--

≈→≡gl : ∀ {α} {x₁ x₂ : Tm α} → x₁ ≈ x₂ → ⟦ x₁ ⟧ ≡ ⟦ x₂ ⟧
≈→≡gl ≈refl = refl
≈→≡gl (≈sym x₂≈x₁) =
  sym (≈→≡gl x₂≈x₁)
≈→≡gl (≈trans x≈y y≈z) =
  trans (≈→≡gl x≈y) (≈→≡gl y≈z)
≈→≡gl ≈K = refl
≈→≡gl ≈S = refl
≈→≡gl (∙-cong {α} {β} x₁≈x₂ y₁≈y₂) =
  cong₂ _⟨∙⟩_ (≈→≡gl x₁≈x₂) (≈→≡gl y₁≈y₂)

norm-sound : ∀ {α} {x₁ x₂ : Tm α} →
  x₁ ≈ x₂ → norm x₁ ≡ norm x₂
norm-sound x₁≈x₂ =
  cong ⟪_⟫ (≈→≡gl x₁≈x₂)

--
-- Completeness: terms are convertible to their normal forms
--     x ≈ norm x
-- 

H : {α : Ty} (p : G α) → Set
H {⋆} p = ⊥
H {α ⇒ β} p = ∀ (q : G α) → H q →
  H (p ⟨∙⟩ q)
    × ⟪ p ⟫ ∙ ⟪ q ⟫ ≈ ⟪ p ⟨∙⟩ q ⟫

mutual

  all-H : ∀ {α} (x : Tm α) → H {α} ⟦ x ⟧
  all-H K p f =
    (λ q g → f , ≈K) , ≈refl
  all-H S p f =
    (λ q g → (λ r h → all-H-S₁ p f q g r h , all-H-S₂ p f q g r h)
      , ≈refl) , ≈refl
  all-H (x ∙ y) =
    all-H∙ ⟦ x ⟧ (all-H x) ⟦ y ⟧ (all-H y)

  all-H∙ : ∀ {α β}
    (p : G (α ⇒ β)) (f : H p) (q : G α) (g : H q) → H (p ⟨∙⟩ q)
  all-H∙ p f q g = proj₁ (f q g)

  all-H-S₁ : ∀ {α β γ}
    (p : G (α ⇒ β ⇒ γ)) (f : H p)
    (q : G (α ⇒ β)) (g : H q) (r : G α) (h : H r) →
      H ((p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r))
  all-H-S₁ p f q g r h =
    all-H∙ (p ⟨∙⟩ r) (all-H∙ p f r h)
           (q ⟨∙⟩ r) (all-H∙ q g r h)

  all-H-S₂ : ∀ {α β γ}
    (p : G (α ⇒ β ⇒ γ)) (f : H p)
    (q : G (α ⇒ β)) (g : H q) (r : G α) (h : H r) →
      S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫ ≈ ⟪ p ⟨∙⟩ r ⟨∙⟩ (q ⟨∙⟩ r) ⟫
  all-H-S₂ p f q g r h = begin
    S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫
      ≈⟨ ≈S ⟩
    (⟪ p ⟫ ∙ ⟪ r ⟫) ∙ (⟪ q ⟫ ∙ ⟪ r ⟫)
      ≈⟨ ∙-cong (proj₂ (f r h)) (proj₂ (g r h)) ⟩
    ⟪ p ⟨∙⟩ r ⟫ ∙ ⟪ q ⟨∙⟩ r ⟫
      ≈⟨ proj₂ ((all-H∙ p f r h) (q ⟨∙⟩ r) (all-H∙ q g r h)) ⟩
    ⟪ (p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r) ⟫
    ∎
    where open ≈-Reasoning

-- x ≈ norm x

norm-complete : ∀ {α} (x : Tm α) → x ≈ norm x

norm-complete K = ≈refl
norm-complete S = ≈refl
norm-complete (x ∙ y) = begin
  x ∙ y
    ≈⟨ ∙-cong (norm-complete x) (norm-complete y) ⟩
  ⟪ ⟦ x ⟧ ⟫ ∙ ⟪ ⟦ y ⟧ ⟫
    ≈⟨ proj₂ (all-H x ⟦ y ⟧ (all-H y)) ⟩
  ⟪ ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧ ⟫
  ∎
  where open ≈-Reasoning
