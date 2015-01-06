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

module STCC-SystemT where

open import Data.Nat
open import Data.Empty
open import Data.Unit
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
  N   :  Ty
  _⇒_ : (α β : Ty) → Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  ZERO : Tm N
  SUC  : Tm (N ⇒ N)
  R    : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (N ⇒ N)
III = I {N ⇒ N} ∙ (I {N ⇒ N} ∙ I {N})

#2 : Tm N
#2 = SUC ∙ (SUC ∙ ZERO)

-- suc1 x y = suc x

suc1 : Tm (N ⇒ N ⇒ N)
suc1 = S ∙ (K ∙ K) ∙ SUC

-- suc2 x y = suc y

suc2 : Tm (N ⇒ N ⇒ N)
suc2 = K ∙ SUC

-- add x y = x + y

add : Tm N → Tm N → Tm N
add m n = R ∙ n ∙ (K ∙ SUC) ∙ m

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
  ≈RZ    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
             R ∙ x ∙ y ∙ ZERO ≈ x 
  ≈RS    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
            R ∙ x ∙ y ∙ (SUC ∙ z) ≈ y ∙ z ∙ (R ∙ x ∙ y ∙ z)

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
  ZERO0 : Nf N
  SUC0  : Nf (N ⇒ N)
  SUC1  : ∀ (u : Nf N) →
            Nf N
  R0    : ∀ {α} →
            Nf (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
  R1    : ∀ {α} (u : Nf α) →
            Nf ((N ⇒ α ⇒ α) ⇒ N ⇒ α)
  R2    : ∀ {α} (u : Nf α) (v : Nf (N ⇒ α ⇒ α)) →
            Nf (N ⇒ α)


reify : ∀ {α} (n : Nf α) → Tm α

reify K0 = K
reify (K1 u) = K ∙ reify u
reify S0 = S
reify (S1 u) = S ∙ reify u
reify (S2 u v) = S ∙ reify u ∙ reify v
reify ZERO0 = ZERO
reify SUC0 = SUC
reify (SUC1 u) = SUC ∙ reify u
reify R0 = R
reify (R1 u) = R ∙ reify u
reify (R2 u v) = R ∙ reify u ∙ reify v

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  infixl 5 _⟨∙⟩_

  {-# TERMINATING #-}

  _⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (w : Nf α) → Nf β
  K0 ⟨∙⟩ w = K1 w
  K1 u ⟨∙⟩ w = u
  S0 ⟨∙⟩ w = S1 w
  S1 u ⟨∙⟩ w = S2 u w
  S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)
  SUC0 ⟨∙⟩ w = SUC1 w
  R0 ⟨∙⟩ w = R1 w
  R1 u ⟨∙⟩ w = R2 u w
  R2 u v ⟨∙⟩ ZERO0 = u
  R2 u v ⟨∙⟩ SUC1 w = v ⟨∙⟩ w ⟨∙⟩ (R2 u v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
  ⟦ ZERO ⟧ = ZERO0
  ⟦ SUC ⟧ = SUC0
  ⟦ R ⟧ = R0

  norm : ∀ {α} → Tm α → Tm α
  norm = reify ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

  norm-1+1 : norm (add (SUC ∙ ZERO) (SUC ∙ ZERO)) ≡ SUC ∙ (SUC ∙ ZERO)
  norm-1+1 = refl

--
-- Primitive recursion
--

rec : ∀ {A : Set} (x : A) (f : ℕ → A → A) (n : ℕ) → A
rec x f zero = x
rec x f (suc n) = f n (rec x f n)

--
-- A "denotational" semantics for `Term α`.
--

module DenotationalNorm where

  D : (α : Ty) → Set
  D N = ℕ
  D (α ⇒ β) = D α → D β

  ⟦_⟧ : ∀ {α} (x : Tm α) → D α
  ⟦ K ⟧ = λ x y → x
  ⟦ S ⟧ = λ x y z → (x z) (y z)
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟦ y ⟧
  ⟦ ZERO ⟧ = zero
  ⟦ SUC ⟧ = suc
  ⟦ R ⟧ = rec

  -- The problem is how to "reify" D-values?
  -- (= How to go back to first-order terms?)
  -- (How compare functions for equality?)

--
-- Glueing
--

G : (α : Ty) → Set
G N = ℕ
G (α ⇒ β) = Nf (α ⇒ β) × (G α → G β)

-- ⌈_⌉

⌈_⌉ : ∀ {α} (p : G α) → Nf α
⌈_⌉ {N} zero = ZERO0
⌈_⌉ {N} (suc p) = SUC1 ⌈ p ⌉
⌈_⌉ {α ⇒ β} p = proj₁ p

-- ⟪_⟫

⟪_⟫ : ∀ {α} (p : G α) → Tm α
⟪_⟫ = reify ∘ ⌈_⌉

-- Application for glued values.

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} (p : G (α ⇒ β)) (q : G α) → G β
p ⟨∙⟩ q = proj₂ p q

--
-- Now ⟦_⟧ terminates!
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
⟦ ZERO ⟧ =
  zero
⟦ SUC ⟧ =
  SUC0 , suc
⟦ R ⟧ =
  R0 , λ p →
    R1 ⌈ p ⌉ , λ q →
      R2 ⌈ p ⌉ ⌈ q ⌉ , rec p (λ n r → q ⟨∙⟩ n ⟨∙⟩ r)

--
-- Normalization.
--

norm : ∀ {α} → Tm α → Tm α
norm = ⟪_⟫ ∘ ⟦_⟧

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl

norm-1+1 : norm (add (SUC ∙ ZERO) (SUC ∙ ZERO)) ≡ SUC ∙ (SUC ∙ ZERO)
norm-1+1 = refl

--
-- Soundness: the normal forms of two convertible terms are equal
--     x₁ ≈ x₂ → norm x₁ ≡ norm x₂
--

≈→⟦⟧≡⟦⟧ : ∀ {α} {x₁ x₂ : Tm α} → x₁ ≈ x₂ → ⟦ x₁ ⟧ ≡ ⟦ x₂ ⟧

≈→⟦⟧≡⟦⟧ ≈refl = refl
≈→⟦⟧≡⟦⟧ (≈sym x₂≈x₁) =
  sym (≈→⟦⟧≡⟦⟧ x₂≈x₁)
≈→⟦⟧≡⟦⟧ (≈trans x≈y y≈z) =
  trans (≈→⟦⟧≡⟦⟧ x≈y) (≈→⟦⟧≡⟦⟧ y≈z)
≈→⟦⟧≡⟦⟧ ≈K = refl
≈→⟦⟧≡⟦⟧ ≈S = refl
≈→⟦⟧≡⟦⟧ (∙-cong {α} {β} {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂) = begin
  ⟦ x₁ ∙ y₁ ⟧
    ≡⟨⟩
  ⟦ x₁ ⟧ ⟨∙⟩ ⟦ y₁ ⟧
    ≡⟨ cong₂ _⟨∙⟩_ (≈→⟦⟧≡⟦⟧ x₁≈x₂) (≈→⟦⟧≡⟦⟧ y₁≈y₂) ⟩
  ⟦ x₂ ⟧ ⟨∙⟩ ⟦ y₂ ⟧
    ≡⟨⟩
  ⟦ x₂ ∙ y₂ ⟧
  ∎
  where open ≡-Reasoning
≈→⟦⟧≡⟦⟧ ≈RZ = refl
≈→⟦⟧≡⟦⟧ ≈RS = refl

norm-sound : ∀ {α} {x₁ x₂ : Tm α} →
  x₁ ≈ x₂ → norm x₁ ≡ norm x₂
norm-sound x₁≈x₂ =
  cong ⟪_⟫ (≈→⟦⟧≡⟦⟧ x₁≈x₂)

--
-- Completeness: terms are convertible to their normal forms
--     x ≈ norm x
-- 

H : {α : Ty} (p : G α) → Set
H {N} p = ⊤
H {α ⇒ β} p = ∀ (q : G α) → H q →
  ⟪ p ⟫ ∙ ⟪ q ⟫ ≈ ⟪ p ⟨∙⟩ q ⟫
    × H (p ⟨∙⟩ q)

mutual

  all-H : ∀ {α} (x : Tm α) → H {α} ⟦ x ⟧
  all-H K p f =
    ≈refl , λ q g →
      ≈K , f
  all-H S p f =
    ≈refl , λ q g →
      ≈refl , λ r h →
        all-H-S₁ p f q g r h , all-H-S₂ p f q g r h
  all-H (x ∙ y) =
    all-H∙ ⟦ x ⟧ (all-H x) ⟦ y ⟧ (all-H y)
  all-H ZERO =
    tt
  all-H SUC =
    λ p _ → ≈refl , tt
  all-H R p f =
    ≈refl , λ q g →
      ≈refl , λ n r →
        all-H-R₁ p f q g n , all-H-R₂ p f q g n

  all-H∙ : ∀ {α β}
    (p : G (α ⇒ β)) (f : H p) (q : G α) (g : H q) → H (p ⟨∙⟩ q)
  all-H∙ p f q g = proj₂ (f q g)

  all-H-S₁ : ∀ {α β γ} (p : G (α ⇒ β ⇒ γ)) (f : H p)
    (q : G (α ⇒ β)) (g : H q) (r : G α) (h : H r) →
      S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫ ≈ ⟪ p ⟨∙⟩ r ⟨∙⟩ (q ⟨∙⟩ r) ⟫
  all-H-S₁ p f q g r h = begin
    S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫
      ≈⟨ ≈S ⟩
    (⟪ p ⟫ ∙ ⟪ r ⟫) ∙ (⟪ q ⟫ ∙ ⟪ r ⟫)
      ≈⟨ ∙-cong (proj₁ (f r h)) (proj₁ (g r h)) ⟩
    ⟪ p ⟨∙⟩ r ⟫ ∙ ⟪ q ⟨∙⟩ r ⟫
      ≈⟨ proj₁ ((all-H∙ p f r h) (q ⟨∙⟩ r) (all-H∙ q g r h)) ⟩
    ⟪ (p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r) ⟫
    ∎
    where open ≈-Reasoning

  all-H-S₂ : ∀ {α β γ} (p : G (α ⇒ β ⇒ γ)) (f : H p)
    (q : G (α ⇒ β)) (g : H q) (r : G α) (h : H r) →
      H ((p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r))
  all-H-S₂ p f q g r h =
    all-H∙ (p ⟨∙⟩ r) (all-H∙ p f r h)
           (q ⟨∙⟩ r) (all-H∙ q g r h)

  all-H-R₁ : ∀ {α} (p : G α) (f : H p)
    (q : G (N ⇒ α ⇒ α)) (g : H q) (m : ℕ) →
      ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ m ⟫ ≈ ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫
  all-H-R₁ p f q g zero = begin
    ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ zero ⟫
      ≡⟨⟩
    R ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ZERO
      ≈⟨ ≈RZ ⟩
    ⟪ p ⟫
      ≡⟨⟩
    ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ zero ⟫
    ∎
    where open ≈-Reasoning
  all-H-R₁ p f q g (suc m) = begin
    ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ suc m ⟫
      ≡⟨⟩
    R ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ (SUC ∙ ⟪ m ⟫)
      ≈⟨ ≈RS ⟩
    (⟪ q ⟫ ∙ ⟪ m ⟫) ∙ (R ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ m ⟫)
      ≈⟨ ∙-cong (proj₁ $ g m tt) (all-H-R₁ p f q g m) ⟩
    ⟪ (q ⟨∙⟩ m) ⟫ ∙ ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫
      ≈⟨ proj₁ $ all-H∙ q g m tt (⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m)
                 (all-H-R₂ p f q g m) ⟩
    ⟪ (q ⟨∙⟩ m) ⟨∙⟩ (⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) ⟫
      ≡⟨⟩
    ⟪ ⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ suc m ⟫
    ∎
    where open ≈-Reasoning

  all-H-R₂ : ∀ {α} (p : G α) (f : H p)
    (q : G (N ⇒ α ⇒ α)) (g : H q) (n : ℕ) →
      H (⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ n)
  all-H-R₂ p f q g zero =
    H p ∋ f
  all-H-R₂ p f q g (suc m) =
    H (q ⟨∙⟩ m ⟨∙⟩ (⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m))
      ∋ all-H∙ (q ⟨∙⟩ m) (all-H∙ q g m tt)
               (⟦ R ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) (all-H-R₂ p f q g m)

-- x ≈ norm x

norm-complete : ∀ {α} (x : Tm α) → x ≈ norm x

norm-complete K = ≈refl
norm-complete S = ≈refl
norm-complete (x ∙ y) = begin
  x ∙ y
    ≈⟨ ∙-cong (norm-complete x) (norm-complete y) ⟩
  norm x ∙ norm y
    ≡⟨⟩
  ⟪ ⟦ x ⟧ ⟫ ∙ ⟪ ⟦ y ⟧ ⟫
    ≈⟨ proj₁ (all-H x ⟦ y ⟧ (all-H y)) ⟩
  ⟪ ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧ ⟫
    ≡⟨⟩
  norm (x ∙ y)
  ∎
  where open ≈-Reasoning
norm-complete ZERO = ≈refl
norm-complete SUC = ≈refl
norm-complete R = ≈refl


--
-- Reduction.
--

infix 4 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K : ∀ {α β} {x : Tm α} {y : Tm β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶AL : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y   : Tm α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y
  ⟶AR : ∀ {α β} {x : Tm (α ⇒ β)} {y y′ : Tm α} →
            y ⟶ y′  →  x ∙ y ⟶ x ∙ y′
  ⟶RZ : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
            R ∙ x ∙ y ∙ ZERO ⟶ x 
  ⟶RS : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
            R ∙ x ∙ y ∙ (SUC ∙ z) ⟶ y ∙ z ∙ (R ∙ x ∙ y ∙ z)

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

-- Example: 1 + 1.

1+1 : add (SUC ∙ ZERO) (SUC ∙ ZERO) ⟶* SUC ∙ (SUC ∙ ZERO)
1+1 = there ⟶RS (there (⟶AL ⟶K) (there (⟶AR ⟶RZ) here))

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
reify→nf ZERO0 (y , ())
reify→nf SUC0 (y , ())
reify→nf (SUC1 u) (._ , ⟶AL ())
reify→nf (SUC1 u) (._ , ⟶AR ⟶y) =
 reify→nf u (, ⟶y)
reify→nf R0 (y , ())
reify→nf (R1 u) (._ , ⟶AL ())
reify→nf (R1 u) (._ , ⟶AR ⟶y) =
  reify→nf u (, ⟶y)
reify→nf (R2 u v) (._ , ⟶AL (⟶AL ()))
reify→nf (R2 u v) (._ , ⟶AL (⟶AR ⟶y)) =
  reify→nf u (, ⟶y)
reify→nf (R2 u v) (._ , ⟶AR ⟶y) =
  reify→nf v (, ⟶y)
