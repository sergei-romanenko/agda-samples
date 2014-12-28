{-
  Normalization theorem for Gödel's System T

    "every typable term is normalizable".

  The original proof (in Alf) was presented in

    Veronica Gaspes and Jan M. Smith. 1992.
    Machine checked normalization proofs for typed combinator calculi.
    In *Proceedings of the Workshop on Types for Proofs and Programs*,
    pages 177-192, Båstad, Sweden. 

  This Agda version is based on the normalization theorem for
  the Simply Typed Combinators in `GaspesSmith-STCC-SK`,
  written by Wojciech Jedynak
    <https://github.com/wjzz/Agda-small-developments-and-examples>
  and modified by Sergei Romanenko.
-}

module GaspesSmith-STCC-SystemT where

open import Data.Empty
open import Data.Product

open import Function

--
-- Types.
--

infixr 5 _⇒_

data Type : Set where
  N   :  Type
  _⇒_ : (α β : Type) → Type

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Type → Set where
  K    : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S    : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_  : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β
  ZERO : Tm N
  SUC  : Tm (N ⇒ N)
  R    : ∀ {α} → Tm (α ⇒ (N ⇒ α ⇒ α) ⇒ N ⇒ α)

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

K2 : ∀ α β → Tm (α ⇒ β ⇒ β)
K2 α β = K ∙ (S ∙ K ∙ K {β = α})

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
  ⟶RZ : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
            R ∙ x ∙ y ∙ ZERO ⟶ x 
  ⟶RS : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z : Tm N} →
            R ∙ x ∙ y ∙ (SUC ∙ z) ⟶ y ∙ z ∙ (R ∙ x ∙ y ∙ z)
  ⟶RN : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} {z z′ : Tm N} →
            z ⟶ z′  →  R ∙ x ∙ y ∙ z ⟶ R ∙ x ∙ y ∙ z′

-- Reflexive and transitive closure of _⟶_ .

infix 3 _⟶*_

data _⟶*_ : ∀ {α} → Tm α → Tm α → Set where
  here  : ∀ {α} {t : Tm α} →
            t ⟶* t
  there : ∀ {α} {t1 t2 t3 : Tm α} →
            t1 ⟶  t2  →  t2 ⟶* t3  →  t1 ⟶* t3

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Tm α) → (I {α}) ∙ x ⟶* x
reduction-example x = there ⟶S $ there ⟶K here

-- Example: 1 + 1.

1+1 : add (SUC ∙ ZERO) (SUC ∙ ZERO) ⟶*
               SUC ∙ (R ∙ (SUC ∙ ZERO) ∙ (K ∙ SUC) ∙ ZERO)
1+1 = there ⟶RS (there (⟶A ⟶K) here)

--
-- Normalizable terms.
--

data Normalizable : ∀ {α} → Tm α → Set where
  nK0 : ∀ {α β} →
          Normalizable (K {α} {β})
  nK1 : ∀ {α β} {x : Tm α} →
          Normalizable x → Normalizable (K {α} {β} ∙ x)
  nS0 : ∀ {α β γ} →
          Normalizable (S {α} {β} {γ})
  nS1 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} →
          Normalizable x → Normalizable (S ∙ x)
  nS2 : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} →
          Normalizable x → Normalizable y → Normalizable (S ∙ x ∙ y)
  n⟶ : ∀ {α} {x x′ : Tm α} →
          x ⟶ x′  → Normalizable x′ → Normalizable x
  nZERO0 : Normalizable ZERO
  nSUC0  : Normalizable SUC
  nSUC1  : ∀ {x : Tm N} →
             Normalizable x → Normalizable (SUC ∙ x)
  nR0    : ∀ {α} →
             Normalizable (R {α})
  nR1    : ∀ {α} {x : Tm α} →
             Normalizable x → Normalizable (R ∙ x)
  nR2    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
             Normalizable x → Normalizable y → Normalizable (R ∙ x ∙ y)


-- Example: 1 + 1 is normalizable.

norm-1+1 : Normalizable (R ∙ (SUC ∙ ZERO) ∙ (K ∙ SUC) ∙ (SUC ∙ ZERO))
norm-1+1 = n⟶ ⟶RS (n⟶ (⟶A ⟶K) (nSUC1 (n⟶ ⟶RZ (nSUC1 nZERO0))))

--
-- Computable terms
--

-- The proof of the normalization theorem, that is, that every typable term x
-- is normalizable, is by Tait's computability method. The idea of this method
-- is that the normalizability of a term x of type α is proved by induction
-- on the derivation of x : α using a stronger induction hypothesis,
-- namely that x is a computable term of type α.

data CompN : (x : Tm N) → Set where
  cZERO : CompN ZERO
  cSUC  : ∀ {x} → CompN x → CompN (SUC ∙ x)
  c⟶  : ∀ {x x′} →
          x ⟶ x′  → CompN x′ → CompN x

Computable : ∀ {α} → Tm α → Set
Computable {N} x = CompN x
Computable {α ⇒ β} x =
  Normalizable x
    × ({y : Tm α} → Computable y → Computable (x ∙ y))

-- The definition of `Computable` implies that
-- a computable term is normalizable.
-- (Hence, if we show that "any typable term is computable", it will imply that
-- "any typable term is normalizable").

N↓ : ∀ {x : Tm N} → CompN x → Normalizable x
N↓ cZERO = nZERO0
N↓ (cSUC x) = nSUC1 (N↓ x)
N↓ (c⟶ x y) = n⟶ x (N↓ y)

↓ : ∀ {α} {x : Tm α} → Computable x → Normalizable x
↓ {N} {x} h = N↓ h
↓ {α ⇒ β} {x} (nx , h) = nx

-- Applying a computable to a computable

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α}
  (cx : Computable x) (cy : Computable y) → Computable (x ∙ y)
_⟨∙⟩_ (nx , hx) cy = hx cy

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Tm α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {N} r h = c⟶ r h
red-comp {α ⇒ β} r (nx′ , h) =
  n⟶ r nx′ , (λ cy → red-comp (⟶A r) (h cy))


-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Tm α) → Computable x
all-computable K =
  nK0 , (λ cx → nK1 (↓ cx) , (λ cy → red-comp ⟶K cx))
all-computable S =
  nS0 , λ cx →
    nS1 (↓ cx) , λ cy →
      nS2 (↓ cx) (↓ cy) , λ cz →
        red-comp ⟶S ((cx ⟨∙⟩ cz) ⟨∙⟩ (cy ⟨∙⟩ cz))
all-computable (x ∙ y) =
  all-computable x ⟨∙⟩ all-computable y
all-computable ZERO = cZERO
all-computable SUC = nSUC0 , cSUC
all-computable (R {α}) =
  nR0 , (λ {x} cx →
    nR1 (↓ cx) , (λ {y} cy →
      nR2 (↓ cx) (↓ cy) , (λ {z} cnz →
        helper cx cy cnz)))
  where
  helper : ∀ {x} (cx : Computable {α} x) {y} (cy : Computable y)
             {z} (cn : CompN z) → Computable (R ∙ x ∙ y ∙ z)
  helper cx cy cZERO = red-comp ⟶RZ cx
  helper cx cy (cSUC cn) =
    red-comp ⟶RS ((cy ⟨∙⟩ cn) ⟨∙⟩ (helper cx cy cn))
  helper cx cy (c⟶ n⟶n′ cn′) =
    red-comp (⟶RN n⟶n′) (helper cx cy cn′)

-- Main result:
-- all typable terms are normalizable.

all-normalizable : ∀ {α} (x : Tm α) → Normalizable x
all-normalizable = ↓ ∘ all-computable

--
-- Extracting the normal form from the proof:
-- given a proof that x is normalizable, we can extract the normal form.
--

⌈_⌉ : ∀ {α} {x : Tm α} → Normalizable x → Tm α
⌈ nK0 ⌉ = K
⌈ nK1 nx ⌉ = K ∙ ⌈ nx ⌉
⌈ nS0 ⌉ = S
⌈ nS1 nx ⌉ = S ∙ ⌈ nx ⌉
⌈ nS2 nx ny ⌉ = S ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉
⌈ n⟶ r nx′ ⌉ = ⌈ nx′ ⌉
⌈ nZERO0 ⌉ = ZERO
⌈ nSUC0 ⌉ = SUC
⌈ nSUC1 nx ⌉ = SUC ∙ ⌈ nx ⌉
⌈ nR0 ⌉ = R
⌈ nR1 nx ⌉ = R ∙ ⌈ nx ⌉
⌈ nR2 nx ny ⌉ = R ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉

--
-- Normalization.
--

norm : ∀ {α} (x : Tm α) → Tm α
norm = ⌈_⌉ ∘ all-normalizable

--
-- Example
--

open import Relation.Binary.PropositionalEquality

III : Tm (N ⇒ N)
III = norm (I {N ⇒ N} ∙ (I {N ⇒ N} ∙ I {N}))

III≡ : III ≡ S ∙ K ∙ K
III≡ = refl
