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

--
-- Types.
--

infixr 5 _⇒_

data Type : Set where
  ⋆   :  Type
  _⇒_ : (α β : Type) → Type

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Type → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

K2 : ∀ α β → Tm (α ⇒ β ⇒ β)
K2 α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Head reduction.
--

infix 3 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K : ∀ {α β} {x : Tm α} {y : Tm β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶A : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y   : Tm α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y

-- Reflexive and transitive closure of _⟶_ .

infix 3 _⟶*_

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

data Nf : Type → Set where
  K0 : ∀ {α β} →
         Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} (x : Nf α) →
         Nf (β ⇒ α)
  S0 : ∀ {α β γ} →
         Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} (x : Nf (α ⇒ β ⇒ γ)) →
         Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} (x : Nf (α ⇒ β ⇒ γ)) (x : Nf (α ⇒ β))→
         Nf (α ⇒ γ)

reify : ∀ {α} (n : Nf α) → Tm α
reify K0 = K
reify (K1 nx) = K ∙ reify nx
reify S0 = S
reify (S1 nx) = S ∙ reify nx
reify (S2 nx ny) = S ∙ reify nx ∙ reify ny

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  {-# TERMINATING #-}

  reflect∙ : ∀ {α β} (x : Nf (α ⇒ β)) (u : Nf α) → Nf β
  reflect∙ K0 nu = K1 nu
  reflect∙ (K1 nx) nu = nx
  reflect∙ S0 nu = S1 nu
  reflect∙ (S1 nx) nu = S2 nx nu
  reflect∙ (S2 nx ny) nu =
    reflect∙ (reflect∙ nx nu) (reflect∙ ny nu)

  reflect : ∀ {α} (x : Tm α) → Nf α
  reflect K = K0
  reflect S = S0
  reflect (x ∙ y) = reflect∙ (reflect x) (reflect y)

  norm : ∀ {α} → Tm α → Tm α
  norm = reify ∘ reflect

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- Glueing
--

Gl : (α : Type) → Set
Gl ⋆ = ⊥
Gl (α ⇒ β) = Nf (α ⇒ β) × (Gl α → Gl β)

-- ⌈_⌉

⌈_⌉ : ∀ {α} (g : Gl α) → Nf α
⌈_⌉ {⋆} ()
⌈_⌉ {α ⇒ β} (n , f) = n

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} (gx : Gl (α ⇒ β)) (gy : Gl α) → Gl β
(nx , fx) ⟨∙⟩ gy = fx gy

--
-- Now `reflect` terminates!
--

reflect : ∀ {α} (x : Tm α) → Gl α
reflect K =
  K0 , λ gx →
    K1 ⌈ gx ⌉ , λ gy →
      gx
reflect S =
  S0 , λ gx →
    S1 ⌈ gx ⌉ , λ gy →
      S2 ⌈ gx ⌉ ⌈ gy ⌉ , λ gz →
        (gx ⟨∙⟩ gz) ⟨∙⟩ (gy ⟨∙⟩ gz)
reflect (x ∙ y) =
  reflect x ⟨∙⟩ reflect y

--
-- Normalization.
--

norm : ∀ {α} → Tm α → Tm α
norm = reify ∘ ⌈_⌉ ∘ reflect

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl
