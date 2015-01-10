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

module STCC-SystemT-norm where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Product

open import Function

open import Relation.Nullary
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
  REC  : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

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
add m n = REC ∙ n ∙ (K ∙ SUC) ∙ m

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
             REC ∙ x ∙ y ∙ ZERO ≈ x 
  ≈RS    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
             REC ∙ x ∙ y ∙ (SUC ∙ z) ≈ y ∙ z ∙ (REC ∙ x ∙ y ∙ z)

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
  REC0  : ∀ {α} →
            Nf (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)
  REC1  : ∀ {α} (u : Nf α) →
            Nf ((N ⇒ α ⇒ α) ⇒ N ⇒ α)
  REC2  : ∀ {α} (u : Nf α) (v : Nf (N ⇒ α ⇒ α)) →
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
reify REC0 = REC
reify (REC1 u) = REC ∙ reify u
reify (REC2 u v) = REC ∙ reify u ∙ reify v

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
  REC0 ⟨∙⟩ w = REC1 w
  REC1 u ⟨∙⟩ w = REC2 u w
  REC2 u v ⟨∙⟩ ZERO0 = u
  REC2 u v ⟨∙⟩ SUC1 w = v ⟨∙⟩ w ⟨∙⟩ (REC2 u v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧
  ⟦ ZERO ⟧ = ZERO0
  ⟦ SUC ⟧ = SUC0
  ⟦ REC ⟧ = REC0

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
  ⟦ REC ⟧ = rec

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
⟦ REC ⟧ =
  REC0 , λ p →
    REC1 ⌈ p ⌉ , λ q →
      REC2 ⌈ p ⌉ ⌈ q ⌉ , rec p (λ n r → q ⟨∙⟩ n ⟨∙⟩ r)

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
-- Completeness: the normal forms of two convertible terms are equal
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

norm-complete : ∀ {α} {x₁ x₂ : Tm α} →
  x₁ ≈ x₂ → norm x₁ ≡ norm x₂
norm-complete x₁≈x₂ =
  cong ⟪_⟫ (≈→⟦⟧≡⟦⟧ x₁≈x₂)

--
-- Now we are going to prove "soundness" -
-- normalization preserves convertibility:
--     x ≈ norm x
-- 

H : {α : Ty} (p : G α) → Set
H {N} p = ⊤
H {α ⇒ β} p = ∀ (q : G α) → H q →
  ⟪ p ⟫ ∙ ⟪ q ⟫ ≈ ⟪ p ⟨∙⟩ q ⟫
    × H (p ⟨∙⟩ q)

-- "Application" for H-values.

|∙| : ∀ {α β}
  (p : G (α ⇒ β)) (f : H p) (q : G α) (g : H q) → H (p ⟨∙⟩ q)
|∙| p f q g = proj₂ (f q g)

-- all-H-R∙

all-H-R∙ : ∀ {α} (p : G α) (f : H p)
  (q : G (N ⇒ α ⇒ α)) (g : H q) (n : ℕ) →
    H (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ n)

all-H-R∙ p f q g zero =
  H p ∋ f

all-H-R∙ p f q g (suc m) =
  H (q ⟨∙⟩ m ⟨∙⟩ (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m))
    ∋ |∙| (q ⟨∙⟩ m) (|∙| q g m tt)
          (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) (all-H-R∙ p f q g m)

-- all-H-R≈

all-H-R≈ : ∀ {α} (p : G α) (f : H p)
  (q : G (N ⇒ α ⇒ α)) (g : H q) (m : ℕ) →
    ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ m ⟫ ≈ ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫

all-H-R≈ p f q g zero = begin
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ zero ⟫
    ≡⟨⟩
  REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ZERO
    ≈⟨ ≈RZ ⟩
  ⟪ p ⟫
    ≡⟨⟩
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ zero ⟫
  ∎
  where open ≈-Reasoning

all-H-R≈ p f q g (suc m) = begin
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟫ ∙ ⟪ suc m ⟫
    ≡⟨⟩
  REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ (SUC ∙ ⟪ m ⟫)
    ≈⟨ ≈RS ⟩
  (⟪ q ⟫ ∙ ⟪ m ⟫) ∙ (REC ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ m ⟫)
    ≈⟨ ∙-cong (proj₁ $ g m tt) (all-H-R≈ p f q g m) ⟩
  ⟪ (q ⟨∙⟩ m) ⟫ ∙ ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m ⟫
    ≈⟨ proj₁ $ |∙| q g m tt (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m)
               (all-H-R∙ p f q g m) ⟩
  ⟪ (q ⟨∙⟩ m) ⟨∙⟩ (⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ m) ⟫
    ≡⟨⟩
  ⟪ ⟦ REC ⟧ ⟨∙⟩ p ⟨∙⟩ q ⟨∙⟩ suc m ⟫
  ∎
  where open ≈-Reasoning

--
-- Any G-value produced from a term is an H-value!
--

all-H : ∀ {α} (x : Tm α) → H ⟦ x ⟧

all-H K p f =
  ≈refl , λ q g →
    ≈K , f

all-H S p f =
  ≈refl , λ q g →
    ≈refl , λ r h →
      (begin
        S ∙ ⟪ p ⟫ ∙ ⟪ q ⟫ ∙ ⟪ r ⟫
          ≈⟨ ≈S ⟩
        (⟪ p ⟫ ∙ ⟪ r ⟫) ∙ (⟪ q ⟫ ∙ ⟪ r ⟫)
          ≈⟨ ∙-cong (proj₁ (f r h)) (proj₁ (g r h)) ⟩
        ⟪ p ⟨∙⟩ r ⟫ ∙ ⟪ q ⟨∙⟩ r ⟫
          ≈⟨ proj₁ ((|∙| p f r h) (q ⟨∙⟩ r) (|∙| q g r h)) ⟩
        ⟪ (p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r) ⟫
      ∎)
      ,
      |∙| (p ⟨∙⟩ r) (|∙| p f r h)
          (q ⟨∙⟩ r) (|∙| q g r h)
  where open ≈-Reasoning

all-H (x ∙ y) =
  |∙| ⟦ x ⟧ (all-H x) ⟦ y ⟧ (all-H y)

all-H ZERO =
  tt

all-H SUC =
  λ p _ → ≈refl , tt

all-H REC p f =
  ≈refl , λ q g →
    ≈refl , λ n r →
      all-H-R≈ p f q g n , all-H-R∙ p f q g n

--
-- Soundness: terms are convertible to their normal forms
--     x ≈ norm x
-- 

norm-sound : ∀ {α} (x : Tm α) → x ≈ norm x

norm-sound K = ≈refl
norm-sound S = ≈refl
norm-sound (x ∙ y) = begin
  x ∙ y
    ≈⟨ ∙-cong (norm-sound x) (norm-sound y) ⟩
  norm x ∙ norm y
    ≡⟨⟩
  ⟪ ⟦ x ⟧ ⟫ ∙ ⟪ ⟦ y ⟧ ⟫
    ≈⟨ proj₁ (all-H x ⟦ y ⟧ (all-H y)) ⟩
  ⟪ ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧ ⟫
    ≡⟨⟩
  norm (x ∙ y)
  ∎
  where open ≈-Reasoning
norm-sound ZERO = ≈refl
norm-sound SUC = ≈refl
norm-sound REC = ≈refl
