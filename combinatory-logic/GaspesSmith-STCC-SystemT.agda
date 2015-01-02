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

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

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
  n⟶ : ∀ {α} {x x′ : Tm α} →
           x ⟶ x′  → Normalizable x′ → Normalizable x
  ZERO0 : Normalizable ZERO
  SUC0  : Normalizable SUC
  SUC1  : ∀ {x : Tm N} →
             Normalizable x → Normalizable (SUC ∙ x)
  R0    : ∀ {α} →
            Normalizable (R {α})
  R1    : ∀ {α} {x : Tm α} →
            Normalizable x → Normalizable (R ∙ x)
  R2    : ∀ {α} {x : Tm α} {y : Tm (N ⇒ α ⇒ α)} →
            Normalizable x → Normalizable y → Normalizable (R ∙ x ∙ y)


-- Example: 1 + 1 is normalizable.

norm-1+1 : Normalizable (R ∙ (SUC ∙ ZERO) ∙ (K ∙ SUC) ∙ (SUC ∙ ZERO))
norm-1+1 = n⟶ ⟶RS (n⟶ (⟶A ⟶K) (SUC1 (n⟶ ⟶RZ (SUC1 ZERO0))))

--
-- Computable terms
--

-- The proof of the normalization theorem, that is, that every typable term x
-- is normalizable, is by Tait's computability method. The idea of this method
-- is that the normalizability of a term x of type α is proved by induction
-- on the derivation of x : α using a stronger induction hypothesis,
-- namely that x is a computable term of type α.

data NComputable : (x : Tm N) → Set where
  CZERO : NComputable ZERO
  CSUC  : ∀ {x} → NComputable x → NComputable (SUC ∙ x)
  c⟶  : ∀ {x x′} →
          x ⟶ x′  → NComputable x′ → NComputable x

Computable : ∀ {α} → Tm α → Set
Computable {N} x = NComputable x
Computable {α ⇒ β} x =
  Normalizable x
    × ({y : Tm α} → Computable y → Computable (x ∙ y))

-- The definition of `Computable` implies that
-- a computable term is normalizable.
-- (Hence, if we show that "any typable term is computable", it will imply that
-- "any typable term is normalizable").

n⟪_⟫ : ∀ {x : Tm N} → NComputable x → Normalizable x
n⟪ CZERO ⟫ = ZERO0
n⟪ CSUC x ⟫ = SUC1 n⟪ x ⟫
n⟪ c⟶ x y ⟫ = n⟶ x n⟪ y ⟫

⟪_⟫ : ∀ {α} {x : Tm α} → Computable x → Normalizable x
⟪_⟫ {N} {x} p = n⟪ p ⟫
⟪_⟫ {α ⇒ β} {x} p = proj₁ p

-- Applying a computable to a computable

infixl 5 _⟨∙⟩_

_⟨∙⟩_ : ∀ {α β} {x : Tm (α ⇒ β)} {y : Tm α}
  (p : Computable x) (q : Computable y) → Computable (x ∙ y)
p ⟨∙⟩ q = proj₂ p q

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Tm α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {N} r h = c⟶ r h
red-comp {α ⇒ β} r p =
  n⟶ r ⟪ p ⟫ , (λ q → red-comp (⟶A r) (p ⟨∙⟩ q))


-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Tm α) → Computable x
all-computable K =
  K0 , λ p → K1 ⟪ p ⟫ , (λ q → red-comp ⟶K p)
all-computable S =
  S0 , λ p →
    S1 ⟪ p ⟫ , λ q →
      S2 ⟪ p ⟫ ⟪ q ⟫ , λ r →
        red-comp ⟶S ((p ⟨∙⟩ r) ⟨∙⟩ (q ⟨∙⟩ r))
all-computable (x ∙ y) =
  all-computable x ⟨∙⟩ all-computable y
all-computable ZERO = CZERO
all-computable SUC = SUC0 , CSUC
all-computable (R {α}) =
  R0 , (λ {x} p →
    R1 ⟪ p ⟫ , (λ {y} q →
      R2 ⟪ p ⟫ ⟪ q ⟫ , (λ {z} r →
        helper p q r)))
  where
  helper : ∀ {x} (p : Computable {α} x) {y} (q : Computable y)
             {z} (r : NComputable z) → Computable (R ∙ x ∙ y ∙ z)
  helper p q CZERO = red-comp ⟶RZ p
  helper p q (CSUC r) =
    red-comp ⟶RS ((q ⟨∙⟩ r) ⟨∙⟩ (helper p q r))
  helper p q (c⟶ n⟶n′ r′) =
    red-comp (⟶RN n⟶n′) (helper p q r′)

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
⌈ n⟶ r nx′ ⌉ = ⌈ nx′ ⌉
⌈ ZERO0 ⌉ = ZERO
⌈ SUC0 ⌉ = SUC
⌈ SUC1 nx ⌉ = SUC ∙ ⌈ nx ⌉
⌈ R0 ⌉ = R
⌈ R1 nx ⌉ = R ∙ ⌈ nx ⌉
⌈ R2 nx ny ⌉ = R ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉

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
