{-
  Normalization Theorem for the Simply Typed Combinators:

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
  ι   :  Type
  _⇒_ : (α β : Type) → Type

--
-- Typed terms.
--

infixl 5 _∙_

data Term : Type → Set where
  K   : ∀ {α β} → Term (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Term ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Term (α ⇒ β) → Term α → Term β

--
-- Example terms.
--

I : ∀ {α} → Term (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

K2 : ∀ α β → Term (α ⇒ β ⇒ β)
K2 α β = K ∙ (S ∙ K ∙ K {β = α})

--
-- Head reduction.
--

infix 3 _⟶_

data _⟶_ : ∀ {α} → Term α → Term α → Set where
  ⟶K : ∀ {α β} {x : Term α} {y : Term β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} {y : Term (α ⇒ β)} {z : Term α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶R : ∀ {α β} {x x′ : Term (α ⇒ β)} {y   : Term α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y

-- Reflexive and transitive closure of _⟶_ .

infix 3 _⟶*_

data _⟶*_ : ∀ {α} → Term α → Term α → Set where
  here  : ∀ {α} {t : Term α} →
            t ⟶* t
  there : ∀ {α} {t1 t2 t3 : Term α} →
            t1 ⟶  t2  →  t2 ⟶* t3  →  t1 ⟶* t3

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Term α) → (I {α}) ∙ x ⟶* x
reduction-example x = there ⟶S (there ⟶K here)

--
-- Normalizable terms.
--

data Normalizable : ∀ {α} → Term α → Set where
  nK  : ∀ {α β} →
          Normalizable (K {α} {β})
  nS  : ∀ {α β γ} →
          Normalizable (S {α} {β} {γ})
  nK1 : ∀ {α β} {x : Term α} →
          Normalizable x → Normalizable (K {α} {β} ∙ x)
  nS1 : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} →
          Normalizable x → Normalizable (S ∙ x)
  nS2 : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} {y : Term (α ⇒ β)} →
          Normalizable x → Normalizable y → Normalizable (S ∙ x ∙ y)
  nR  : ∀ {α} {x x′ : Term α} →
          x ⟶ x′  → Normalizable x′ → Normalizable x

--
-- Computable terms
--

-- The proof of the normalization theorem, that is, that every typable term x
-- is normalizable, is by Tait's computability method. The idea of this method
-- is that the normalizability of a term x of type α is proved by induction
-- on the derivation of x : α using a stronger induction hypothesis,
-- namely that x is a computable term of type α.

Computable : ∀ {α} → Term α → Set
Computable {ι} x = ⊥
Computable {α ⇒ β} x =
  Normalizable x
    × ({y : Term α} → Computable y → Computable (x ∙ y))

-- The definition of `Computable` implies that
-- a computable term is normalizable.
-- (Hence, if we show that "any typable term is computable", it will imply that
-- "any typable term is normalizable").

comp→norm : ∀ {α} {x : Term α} → Computable x → Normalizable x
comp→norm {ι} ()
comp→norm {α ⇒ β} (nx , h) = nx

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Term α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {ι} r ()
red-comp {α ⇒ β} r (nx′ , h) =
  nR r nx′ , (λ cy → red-comp {β} (⟶R r) (h cy))

-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Term α) → Computable x
all-computable K =
  nK , (λ cx → nK1 (comp→norm cx) , (λ cy → red-comp ⟶K cx))
all-computable S =
  nS , (λ {(nx , hx) → nS1 nx
          , (λ {(ny , hy) → (nS2 nx ny)
               , (λ cz → red-comp ⟶S (proj₂ (hx cz) (hy cz)))})})
all-computable (x ∙ y)
  with all-computable x | all-computable y
... | cx | cy = proj₂ cx cy

-- Main result:
-- all typable terms are normalizable.

all-normalizable : ∀ {α} (x : Term α) → Normalizable x
all-normalizable x =
  comp→norm (all-computable x)

--
-- Extracting the normal form from the proof:
-- given a proof that x is normalizable, we can extract the normal form.
--

⌈_⌉ : ∀ {α} {x : Term α} → Normalizable x → Term α
⌈ nK ⌉ = K
⌈ nS ⌉ = S
⌈ nK1 nx ⌉ = K ∙ ⌈ nx ⌉
⌈ nS1 nx ⌉ = S ∙ ⌈ nx ⌉
⌈ nS2 nx ny ⌉ = S ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉
⌈ nR x⟶x′ nx′ ⌉ = ⌈ nx′ ⌉
  -- this step actually performs the reduction

--
-- Example
--

open import Relation.Binary.PropositionalEquality

III : Term (ι ⇒ ι)
III = ⌈ all-normalizable (I {ι ⇒ ι} ∙ (I {ι ⇒ ι} ∙ I {ι})) ⌉

III≡ : III ≡ S ∙ K ∙ K
III≡ = refl
