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

data Term : Type → Set where
  K    : ∀ {α β} → Term (α ⇒ β ⇒ α)
  S    : ∀ {α β γ} → Term ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_  : ∀ {α β} → Term (α ⇒ β) → Term α → Term β
  ZERO : Term N
  SUC  : Term (N ⇒ N)
  R    : ∀ {α} → Term (α ⇒ (α ⇒ N ⇒ α) ⇒ N ⇒ α)

--
-- Example terms.
--

I : ∀ {α} → Term (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

K2 : ∀ α β → Term (α ⇒ β ⇒ β)
K2 α β = K ∙ (S ∙ K ∙ K {β = α})

#2 : Term N
#2 = SUC ∙ (SUC ∙ ZERO)

-- suc1 x y = suc x

suc1 : Term (N ⇒ N ⇒ N)
suc1 = S ∙ (K ∙ K) ∙ SUC

-- add x y = x + y

add : Term N → Term N → Term N
add m n = R ∙ n ∙ (S ∙ (K ∙ K) ∙ SUC) ∙ m

--
-- Head reduction.
--

infix 3 _⟶_

data _⟶_ : ∀ {α} → Term α → Term α → Set where
  ⟶K : ∀ {α β} {x : Term α} {y : Term β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} {y : Term (α ⇒ β)} {z : Term α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶A : ∀ {α β} {x x′ : Term (α ⇒ β)} {y   : Term α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y
  ⟶RZ : ∀ {α} {x : Term α} {y : Term (α ⇒ N ⇒ α)} →
            R ∙ x ∙ y ∙ ZERO ⟶ x 
  ⟶RS : ∀ {α} {x : Term α} {y : Term (α ⇒ N ⇒ α)} {z : Term N} →
            R ∙ x ∙ y ∙ (SUC ∙ z) ⟶ y ∙ (R ∙ x ∙ y ∙ z) ∙ z
  ⟶RN : ∀ {α} {x : Term α} {y : Term (α ⇒ N ⇒ α)} {z z′ : Term N} →
            z ⟶ z′  →  R ∙ x ∙ y ∙ z ⟶ R ∙ x ∙ y ∙ z′

-- Reflexive and transitive closure of _⟶_ .

infix 3 _⟶*_

data _⟶*_ : ∀ {α} → Term α → Term α → Set where
  here  : ∀ {α} {t : Term α} →
            t ⟶* t
  there : ∀ {α} {t1 t2 t3 : Term α} →
            t1 ⟶  t2  →  t2 ⟶* t3  →  t1 ⟶* t3

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Term α) → (I {α}) ∙ x ⟶* x
reduction-example x = there ⟶S $ there ⟶K here

-- Example: 1 + 1.

1+1 : add (SUC ∙ ZERO) (SUC ∙ ZERO) ⟶*
          SUC ∙ (R ∙ (SUC ∙ ZERO) ∙ (S ∙ (K ∙ K) ∙ SUC) ∙ ZERO)
1+1 = there ⟶RS $ there (⟶A ⟶S) $ there (⟶A (⟶A ⟶K)) $ there ⟶K here
      

--
-- Normalizable terms.
--

data Normalizable : ∀ {α} → Term α → Set where
  nK  : ∀ {α β} →
          Normalizable (K {α} {β})
  nK1 : ∀ {α β} {x : Term α} →
          Normalizable x → Normalizable (K {α} {β} ∙ x)
  nS  : ∀ {α β γ} →
          Normalizable (S {α} {β} {γ})
  nS1 : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} →
          Normalizable x → Normalizable (S ∙ x)
  nS2 : ∀ {α β γ} {x : Term (α ⇒ β ⇒ γ)} {y : Term (α ⇒ β)} →
          Normalizable x → Normalizable y → Normalizable (S ∙ x ∙ y)
  n⟶ : ∀ {α} {x x′ : Term α} →
          x ⟶ x′  → Normalizable x′ → Normalizable x
  nZ    : Normalizable ZERO
  nSUC  : Normalizable SUC
  nSUC1 : ∀ {x : Term N} →
             Normalizable x → Normalizable (SUC ∙ x)
  nR  : ∀ {α} →
          Normalizable (R {α})
  nR1 : ∀ {α} {x : Term α} →
          Normalizable x → Normalizable (R ∙ x)
  nR2 : ∀ {α} {x : Term α} {y : Term (α ⇒ N ⇒ α)} →
          Normalizable x → Normalizable y → Normalizable (R ∙ x ∙ y)

--
-- Computable terms
--

-- The proof of the normalization theorem, that is, that every typable term x
-- is normalizable, is by Tait's computability method. The idea of this method
-- is that the normalizability of a term x of type α is proved by induction
-- on the derivation of x : α using a stronger induction hypothesis,
-- namely that x is a computable term of type α.

data CompN : (x : Term N) → Set where
  cZERO : CompN ZERO
  cSUC  : ∀ {x} → CompN x → CompN (SUC ∙ x)
  c⟶  : ∀ {x x′} →
          x ⟶ x′  → CompN x′ → CompN x

Computable : ∀ {α} → Term α → Set
Computable {N} x = CompN x
Computable {α ⇒ β} x =
  Normalizable x
    × ({y : Term α} → Computable y → Computable (x ∙ y))

-- The definition of `Computable` implies that
-- a computable term is normalizable.
-- (Hence, if we show that "any typable term is computable", it will imply that
-- "any typable term is normalizable").

compN→norm : ∀ {x : Term N} → CompN x → Normalizable x
compN→norm cZERO = nZ
compN→norm (cSUC x) = nSUC1 (compN→norm x)
compN→norm (c⟶ x y) = n⟶ x (compN→norm y)

comp→norm : ∀ {α} {x : Term α} → Computable x → Normalizable x
comp→norm {N} {x} h = compN→norm h
comp→norm {α ⇒ β} {x} (nx , h) = nx

-- Main lemma:
-- a reduction step preserves computability.

red-comp : ∀ {α} {x x′ : Term α} →
  x ⟶ x′ → Computable x′ → Computable x
red-comp {N} r h = c⟶ r h
red-comp {α ⇒ β} r (nx′ , h) =
  n⟶ r nx′ , (λ cy → red-comp (⟶A r) (h cy))


-- Main theorem:
-- all typable terms are computable.

all-computable : ∀ {α} (x : Term α) → Computable x
all-computable K =
  nK , (λ cx → nK1 (comp→norm cx) , (λ cy → red-comp ⟶K cx))
all-computable S =
  nS , (λ {(nx , hx) → nS1 nx
          , (λ {(ny , hy) → nS2 nx ny
               , (λ cz → red-comp ⟶S (proj₂ (hx cz) (hy cz)))})})
all-computable (x ∙ y)
  with all-computable x | all-computable y
... | cx | cy = proj₂ cx cy
all-computable ZERO = cZERO
all-computable SUC = nSUC , cSUC
all-computable (R {α}) =
  nR , (λ {x} cx → nR1 (comp→norm cx)
          , (λ {y} cy → nR2 (comp→norm cx) (comp→norm cy)
               , (λ {z} cnz → helper cx cy cnz)))
  where
  helper : ∀ {x} (cx : Computable {α} x) {y} (cy : Computable y)
             {z} (cnz : CompN z) → Computable (R ∙ x ∙ y ∙ z)
  helper cx cy cZERO = red-comp ⟶RZ cx
  helper cx cy (cSUC cnz) =
    red-comp ⟶RS (proj₂ (proj₂ cy (helper cx cy cnz)) cnz)
  helper cx cy (c⟶ z⟶z′ cnz′) =
   red-comp (⟶RN z⟶z′) (helper cx cy cnz′)

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
⌈ nK1 nx ⌉ = K ∙ ⌈ nx ⌉
⌈ nS ⌉ = S
⌈ nS1 nx ⌉ = S ∙ ⌈ nx ⌉
⌈ nS2 nx ny ⌉ = S ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉
⌈ n⟶ r nx′ ⌉ = ⌈ nx′ ⌉
⌈ nZ ⌉ = ZERO
⌈ nSUC ⌉ = SUC
⌈ nSUC1 nx ⌉ = SUC ∙ ⌈ nx ⌉
⌈ nR ⌉ = R
⌈ nR1 nx ⌉ = R ∙ ⌈ nx ⌉
⌈ nR2 nx ny ⌉ = R ∙ ⌈ nx ⌉ ∙ ⌈ ny ⌉

--
-- Example
--

open import Relation.Binary.PropositionalEquality

III : Term (N ⇒ N)
III = ⌈ all-normalizable (I {N ⇒ N} ∙ (I {N ⇒ N} ∙ I {N})) ⌉

III≡ : III ≡ S ∙ K ∙ K
III≡ = refl
