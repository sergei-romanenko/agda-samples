--
-- Small-step Operational Semantics
-- for a Nondeterministic Language
--

{-
  Based on

    Software Foundations
    by Benjamin C. Pierce, ...
    http://www.cis.upenn.edu/~bcpierce/sf/

  and

    Liyang Hu and Graham Hutton.
    Compiling concurrency correctly: cutting out the middle man.
    Trends in Functional Programming volume 10 (Zoltan Horvath and
    Viktoria Zsok, editors), Intellect, September 2010.
    Selected papers from the Tenth Symposium on Trends in Functional
    Programming, Komarno, Slovakia, June 2009. 

  and

    Liyang Hu. 2012. Compiling Concurrency Correctly:
    Verifying Software Transactional Memory.
    A Thesis submitted for the degree of Doctor of Philosophy.
    http://www.cs.nott.ac.uk/~gmh/hu-thesis.pdf
-}

module SmallStepNondet where

open import Data.Nat
open import Data.List
open import Data.Product
  renaming (map to map×)
open import Data.Sum
  renaming (map to map⊎)
open import Data.Empty
open import Data.Maybe

open import Data.Star as Star
open import Data.Star.Properties

open import Function

open import Function.Equivalence
  using (_⇔_; equivalence)

open import Coinduction

open import Relation.Nullary
open import Relation.Binary
  using (Rel; Setoid; _⇒_; Sym; Symmetric; Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

--
-- A Toy Language
--

infixl 6 _⊕_

data Tm : Set where
  #_  : (n : ℕ) → Tm
  _⊕_ : (t₁ t₂ : Tm) → Tm


data Action : Set where
  ⊞ : Action
  ↯ : Action
  ◻ : ℕ → Action

data Label : Set where
  τ : Label
  ! : Action → Label


-- Labeled transition systems

LTS : Set → Set → Set₁
LTS L X = X → L → X → Set

-- Small-step evaluation relation

infix 3 _↦<_>_

data _↦<_>_ : LTS Label Tm where
  n+n : ∀ {n₁ n₂} →
    # n₁ ⊕ # n₂ ↦< ! ⊞ > # (n₁ + n₂)
  n↯n : ∀ {n₁ n₂} →
    # n₁ ⊕ # n₂ ↦< ! ↯ > # 0
  r+t : ∀ {t₁ t′₁ t₂ Λ} →
    (t₁↦ : t₁ ↦< Λ > t′₁) →
    t₁ ⊕ t₂ ↦< Λ > t′₁ ⊕ t₂
  n+r : ∀ {n₁ t₂ t′₂ Λ} →
    (t₂↦ : t₂ ↦< Λ > t′₂) →
    # n₁ ⊕ t₂ ↦< Λ > # n₁ ⊕ t′₂

--
-- Virtual machine
--

-- Program

data Instruction : Set where
  push : ℕ → Instruction
  add  : Instruction

Program : Set
Program = List Instruction

-- State

Stack : Set
Stack = List ℕ

data State : Set where
  ⟨_,_⟩ : Program → Stack → State

-- Execution

infix 3 _↣<_>_ -- _↣*_

data _↣<_>_ : LTS Label State where
  ↣-push : ∀ {c s m} →
    ⟨ push m ∷ c , s ⟩ ↣< τ >  ⟨ c , m ∷ s ⟩
  ↣-add  : ∀ {c s m n} →
    ⟨ add ∷ c , n ∷ m ∷ s ⟩ ↣< ! ⊞ > ⟨ c , m + n ∷ s ⟩ 
  ↣-zap  : ∀ {c s m n} →
    ⟨ add ∷ c , n ∷ m ∷ s ⟩ ↣< ! ↯ > ⟨ c , 0 ∷ s ⟩ 

-- Compiler

compile : Tm → Program → Program
compile (# n) c = push n ∷ c
compile (t₁ ⊕ t₂) c = compile t₁ (compile t₂ (add ∷ c))

--
-- Bisimulation
--

infix 3 _↠<_>_ _↠<τ>_ _↠<τ>*_
 
data Combined : Set where
  ⟪_▷_⟫ : (t : Tm) → (σ : State) → Combined
  ⟪_⟫    : (σ : State) → Combined
  ⟪⟫     : Combined

data _↠<_>_ : LTS Label Combined where
  ↠-↦ : ∀ {t₁ t₂ σ Λ} →
    t₁ ↦< Λ > t₂ → ⟪ t₁ ▷ σ ⟫ ↠< Λ > ⟪ t₂ ▷ σ ⟫
  ↠-↣ : ∀ {σ₁ σ₂ Λ} →
    σ₁ ↣< Λ > σ₂ → ⟪ σ₁ ⟫ ↠< Λ > ⟪ σ₂ ⟫
  ↠-switch : ∀ {m c s} →
    ⟪ # m ▷ ⟨ c , s ⟩ ⟫ ↠< τ > ⟪ ⟨ c , m ∷ s ⟩ ⟫
  ↠-done : ∀ {m} →
    ⟪ ⟨ [] , m ∷ [] ⟩ ⟫ ↠< ! (◻ m) > ⟪⟫


_↠<τ>_ : Rel Combined _
x ↠<τ> y = x ↠< τ > y

_↠<τ>*_ : Rel Combined _
_↠<τ>*_ = Star _↠<τ>_

-- Visible transition

infix 3 _⤇<_>_

data _⤇<_>_ : LTS Action Combined where
  ⤇ : ∀ {x x′ y y′ α}
    (h₁ : x ↠<τ>* x′) (h₂ : x′ ↠< ! α > y′) (h₃ : y′ ↠<τ>* y) → x ⤇< α > y

-- Simulation

mutual

  data _≈′_ : Rel Combined _ where
    ≈⇒≈′    : _≈_ ⇒ _≈′_
    ≈′-sym   : Symmetric _≈′_
    ≈′-trans : Transitive _≈′_

  _≼_ : Rel Combined _
  x ≼ y = ∀ x′ {α} → x ⤇< α > x′ → ∃ λ y′ → y ⤇< α > y′ × x′ ≈′ y′

  data _≈_ : Combined → Combined → Set where
    _&_ :  ∀ {x y} (x≼y : ∞ (x ≼ y)) (y≼x : ∞ (y ≼ x)) → x ≈ y


mutual

  ≼-refl : Reflexive _≼_
  ≼-refl x′ x⤇x′ = x′ , x⤇x′ , ≈⇒≈′ ≈-refl

  ≈-refl : Reflexive _≈_
  ≈-refl {x} = ♯ ≼-refl & ♯ ≼-refl

≈-sym : Symmetric _≈_
≈-sym (x≼y & y≼x) = y≼x & x≼y

mutual

  ≼-trans : Transitive _≼_
  ≼-trans {x} {y} {z} h g x′ x⤇x′ with h x′ x⤇x′
  ... | y′ , y⤇y′ , x′≈′y′ with g y′ y⤇y′
  ... | z′ , z⤇z′ , y′≈′z′ = z′ , z⤇z′ , ≈′-trans x′≈′y′ y′≈′z′

  ≈-trans : Transitive _≈_
  ≈-trans {x} {y} {z} (x≼y & y≼x) (y≼z & z≼y) =
    ♯ ≼-trans (♭ x≼y) (♭ y≼z) &
    ♯ ≼-trans (♭ z≼y) (♭ y≼x)


≈′⇒≈ : _≈′_ ⇒ _≈_

≈′⇒≈ (≈⇒≈′ x≈y) = x≈y
≈′⇒≈ (≈′-sym x≈′y) = ≈-sym (≈′⇒≈ x≈′y)
≈′⇒≈ {x} {y} (≈′-trans x≈′z z≈′y) = ≈-trans (≈′⇒≈ x≈′z) (≈′⇒≈ z≈′y)

≈⇔≈′ : ∀ {x y} → x ≈ y ⇔ x ≈′ y
≈⇔≈′ = equivalence ≈⇒≈′ ≈′⇒≈


--
-- ≈-Reasoning
--

import Relation.Binary.EqReasoning as EqR

≈-setoid : Setoid _ _

≈-setoid = record
  { Carrier = Combined
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans } }

module ≈-Reasoning = EqR ≈-setoid


¬↦<τ> : ∀ {t₁ t₂} → t₁ ↦< τ > t₂ → ⊥
¬↦<τ> (r+t h) = ⊥-elim (¬↦<τ> h)
¬↦<τ> (n+r h) = ⊥-elim (¬↦<τ> h)

unique-τ : ∀ {x y Λ y′} → x ↠<τ> y → x ↠< Λ > y′ → Λ ≡ τ × y′ ≡ y

unique-τ (↠-↦ t₁↦<τ>t₂) q = ⊥-elim (¬↦<τ> t₁↦<τ>t₂)
unique-τ (↠-↣ ↣-push) (↠-↣ ↣-push) = refl , refl
unique-τ ↠-switch (↠-↦ ())
unique-τ ↠-switch ↠-switch = refl , refl

--
-- elide-τ
--

elide-τ : _↠<τ>_ ⇒ _≈_

elide-τ {x} {y} x↠<τ>y = ♯ x≼y & ♯ y≼x
  where
  x≼y : x ≼ y
  x≼y x′ (⤇ ε x↠y′ h₃) with unique-τ x↠<τ>y x↠y′
  x≼y x′ (⤇ ε x↠y′ h₃) | () , _
  x≼y x′ (⤇ (x↠z ◅ z↠x′) x′↠y′ h) with unique-τ x↠<τ>y x↠z
  x≼y x′ (⤇ (x↠z ◅ z↠x′) x′↠y′ h) | refl , refl =
    x′ , ⤇ z↠x′ x′↠y′ h , ≈⇒≈′ ≈-refl
  y≼x : y ≼ x
  y≼x y′ (⤇ h₁ h₂ h₃) = y′ , ⤇ (x↠<τ>y ◅ h₁) h₂ h₃ , ≈⇒≈′ ≈-refl


elide-τ* : _↠<τ>*_ ⇒ _≈_
elide-τ* = (Star.fold _≈_ ≈-trans ≈-refl) ∘ Star.map elide-τ

{-
elide-τ* ε = ≈-refl
elide-τ* (x↠z ◅ z↠*y) =
  ≈-trans (elide-τ x↠y) (elide-τ* y↠*z)
-}

sym-elide-τ* : Sym _↠<τ>*_ _≈_
sym-elide-τ* = ≈-sym ∘ elide-τ*


postulate

  eval-left′ : ∀ {a b c σ} →
    ⟪ a ▷ ⟨ compile b (add ∷ c) , σ ⟩ ⟫ ≈ ⟪ a ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  eval-right′ : ∀ {m b c σ} →
    ⟪ b ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ # m ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  add≈m⊕n′ : ∀ {m n c σ} →
    ⟪ # n ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ # m ⊕ # n ▷ ⟨ c , σ ⟩ ⟫


--
-- correctness
--

mutual

  correctness : ∀ {a c σ} →
    ⟪ ⟨ compile a c , σ ⟩ ⟫ ≈ ⟪ a ▷ ⟨ c , σ ⟩ ⟫

  correctness {# n} {c} {σ} = begin
    ⟪ ⟨ compile (# n) c , σ ⟩ ⟫
      ≡⟨⟩
    ⟪ ⟨ push n ∷ c , σ ⟩ ⟫
      ≈⟨ elide-τ (↠-↣ ↣-push) ⟩
    ⟪ ⟨ c , n ∷ σ ⟩ ⟫
      ≈⟨ ≈-sym (elide-τ ↠-switch)  ⟩
    ⟪ # n ▷ ⟨ c , σ ⟩ ⟫
    ∎
    where open ≈-Reasoning


  correctness {a ⊕ b} {c} {σ} = begin
    ⟪ ⟨ compile (a ⊕ b) c , σ ⟩ ⟫
      ≡⟨⟩
    ⟪ ⟨ compile a (compile b (add ∷ c)) , σ ⟩ ⟫
      ≈⟨ correctness ⟩
    ⟪ a ▷ ⟨ compile b (add ∷ c) , σ ⟩ ⟫
      ≈⟨ eval-left′ ⟩
    ⟪ a ⊕ b ▷ ⟨ c , σ ⟩ ⟫
    ∎
    where open ≈-Reasoning

--
