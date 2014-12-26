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
-- Normalizable terms.
--

data Normalizable : ∀ {α} → Tm α → Set where
  nK  : ∀ {α β} →
          Normalizable (K {α} {β})
  nK1 : ∀ {α β} {x : Tm α} →
          Normalizable x → Normalizable (K {α} {β} ∙ x)
  nS  : ∀ {α β γ} →
          Normalizable (S {α} {β} {γ})
  nS1 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} →
          Normalizable x → Normalizable (S ∙ x)
  nS2 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} →
          Normalizable x → Normalizable y → Normalizable (S ∙ x ∙ y)
  n⟶ : ∀ {α} {x x′ : Tm α} →
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

→norm : ∀ {α} {x : Tm α} → Computable x → Normalizable x
→norm {⋆} ()
→norm {α ⇒ β} (nx , h) = nx

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Tm α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {⋆} r ()
red-comp {α ⇒ β} r (nx′ , h) =
  n⟶ r nx′ , (λ cy → red-comp {β} (⟶A r) (h cy))

-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Tm α) → Computable x
all-computable K =
  nK , (λ cx → nK1 (→norm cx) , (λ cy → red-comp ⟶K cx))
all-computable S =
  nS , (λ {(nx , hx) → nS1 nx
          , (λ {(ny , hy) → (nS2 nx ny)
               , (λ cz → red-comp ⟶S (proj₂ (hx cz) (hy cz)))})})
all-computable (x ∙ y)
  with all-computable x | all-computable y
... | cx | cy = proj₂ cx cy

-- Main result:
-- all typable terms are normalizable.

all-normalizable : ∀ {α} (x : Tm α) → Normalizable x
all-normalizable x =
  →norm (all-computable x)

--
-- Extracting the normal form from the proof:
-- given a proof that x is normalizable, we can extract the normal form.
--

⌈_⌉ : ∀ {α} {x : Tm α} → Normalizable x → Tm α
⌈ nK ⌉ = K
⌈ nS ⌉ = S
⌈ nK1 nx ⌉ = K ∙ ⌈ nx ⌉
⌈ nS1 nx ⌉ = S ∙ ⌈ nx ⌉
⌈ nS2 nx ny ⌉ = S ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉
⌈ n⟶ r nx′ ⌉ = ⌈ nx′ ⌉

--
-- Normalization.
--

norm : ∀ {α} (x : Tm α) → Tm α
norm x = ⌈ all-normalizable x ⌉

--
-- Example
--

open import Relation.Binary.PropositionalEquality

norm-III : Tm (⋆ ⇒ ⋆)
norm-III = norm (I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆}))

norm-III≡ : norm-III ≡ S ∙ K ∙ K
norm-III≡ = refl

