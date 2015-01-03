{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  The original proof (in Alf) was presented in

    Veronica Gaspes and Jan M. Smith. 1992.
    Machine checked normalization proofs for typed combinator calculi.
    In *Proceedings of the Workshop on Types for Proofs and Programs*,
    pages 177-192, Båstad, Sweden. 

  The Agda version was written by Wojciech Jedynak
    <https://github.com/wjzz/Agda-small-developments-and-examples>
  and modified by Sergei Romanenko.
-}

module GaspesSmith-STCC-SK where

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Function

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

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

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
-- Normalizable terms.
--

data Normalizable : ∀ {α} → Tm α → Set where
  K0 : ∀ {α β} →
         Normalizable (K {α} {β})
  K1 : ∀ {α β} {x : Tm α} →
         Normalizable x → Normalizable (K {α} {β} ∙ x)
  S0 : ∀ {α β γ} →
         Normalizable (S {α} {β} {γ})
  S1 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} →
         Normalizable x → Normalizable (S ∙ x)
  S2 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} →
         Normalizable x → Normalizable y → Normalizable (S ∙ x ∙ y)
  ⟶N : ∀ {α} {x x′ : Tm α} →
           x ⟶ x′  → Normalizable x′ → Normalizable x

--
-- Computable terms
--

-- The proof of the normalization theorem, that is, that every typable term x
-- is normalizable, is by Tait's computability method. The idea of this method
-- is that the normalizability of a term x of type α is proved by induction
-- on the derivation of x : α using a stronger induction hypothesis,
-- namely that x is a computable term of type α.

Computable : ∀ {α} → Tm α → Set
Computable {⋆} x = ⊥
Computable {α ⇒ β} x =
  Normalizable x
    × ({y : Tm α} → Computable y → Computable (x ∙ y))

-- The definition of `Computable` implies that
-- a computable term is normalizable.
-- (Hence, if we show that "any typable term is computable", it will imply that
-- "any typable term is normalizable").

⟪_⟫ : ∀ {α} {x : Tm α} → Computable x → Normalizable x
⟪_⟫ {⋆} ()
⟪_⟫ {α ⇒ β} p = proj₁ p

-- Applying a computable to a computable

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α}
  (p : Computable x) (q : Computable y) → Computable (x ∙ y)
p ⟨∙⟩ q = proj₂ p q

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Tm α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {⋆} x⟶x′ ()
red-comp {α ⇒ β} x⟶x′ p =
  ⟶N x⟶x′ ⟪ p ⟫ , λ q → red-comp {β} (⟶A x⟶x′) (p ⟨∙⟩ q)


-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Tm α) → Computable x
all-computable K =
  K0 , λ p → K1 ⟪ p ⟫ , λ q → red-comp ⟶K p
all-computable S =
  S0 , λ p →
    S1 ⟪ p ⟫ , λ q →
      S2 ⟪ p ⟫ ⟪ q ⟫ , λ r →
        red-comp ⟶S ((p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r))
all-computable (x ∙ y) =
  all-computable x ⟨∙⟩ all-computable y

-- Main result:
-- all typable terms are normalizable.

all-normalizable : ∀ {α} (x : Tm α) → Normalizable x
all-normalizable = ⟪_⟫ ∘ all-computable

--
-- Extracting the normal form from the proof:
-- given a proof that x is normalizable, we can extract the normal form.
--

⌈_⌉ : ∀ {α} {x : Tm α} → Normalizable x → Tm α
⌈ K0 ⌉ = K
⌈ K1 nx ⌉ = K ∙ ⌈ nx ⌉
⌈ S0 ⌉ = S
⌈ S1 nx ⌉ = S ∙ ⌈ nx ⌉
⌈ S2 nx ny ⌉ = S ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉
⌈ ⟶N x⟶x′ nx′ ⌉ = ⌈ nx′ ⌉

--
-- Normalization.
--

norm : ∀ {α} (x : Tm α) → Tm α
norm = ⌈_⌉ ∘ all-normalizable

--
-- Example
--

open import Relation.Binary.PropositionalEquality

norm-III : Tm (⋆ ⇒ ⋆)
norm-III = norm (I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆}))

norm-III≡ : norm-III ≡ S ∙ K ∙ K
norm-III≡ = refl
