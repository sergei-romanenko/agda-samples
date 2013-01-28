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

open import Data.Star
open import Data.Star.Properties

open import Function

open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Nullary
open import Relation.Binary
  using (Rel)
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

--
-- A Toy Language
--

infixl 6 _⊕_

data Tm : Set where
  val : (n : ℕ) → Tm
  _⊕_  : (t₁ t₂ : Tm) → Tm


data Action : Set where
  ⊞ : Action
  ↯ : Action
  ◻ : ℕ → Action

data Label : Set where
  τ : Label
  ! : Action → Label

-- Small-step evaluation relation

infix 3 _↦<_>_

data _↦<_>_ : Tm → Label → Tm → Set where
  n+n : ∀ {n₁ n₂} →
    val n₁ ⊕ val n₂ ↦< ! ⊞ > val (n₁ + n₂)
  n↯n : ∀ {n₁ n₂} →
    val n₁ ⊕ val n₂ ↦< ! ↯ > val 0
  r+t : ∀ {t₁ t′₁ t₂ Λ} →
    (t₁↦ : t₁ ↦< Λ > t′₁) →
    t₁ ⊕ t₂ ↦< Λ > t′₁ ⊕ t₂
  n+r : ∀ {n₁ t₂ t′₂ Λ} →
    (t₂↦ : t₂ ↦< Λ > t′₂) →
    val n₁ ⊕ t₂ ↦< Λ > val n₁ ⊕ t′₂

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

data _↣<_>_ : State → Label → State → Set where
  ↣-push : ∀ {c s m} →
    ⟨ push m ∷ c , s ⟩ ↣< τ >  ⟨ c , m ∷ s ⟩
  ↣-add  : ∀ {c s m n} →
    ⟨ add ∷ c , n ∷ m ∷ s ⟩ ↣< ! ⊞ > ⟨ c , m + n ∷ s ⟩ 
  ↣-zap  : ∀ {c s m n} →
    ⟨ add ∷ c , n ∷ m ∷ s ⟩ ↣< ! ↯ > ⟨ c , 0 ∷ s ⟩ 

-- Compiler

compile : Tm → Program → Program
compile (val n) c = push n ∷ c
compile (t₁ ⊕ t₂) c = compile t₁ (compile t₂ (add ∷ c))

--
-- Bisimulation
--

infix 3 _↠<_>_ _↠<τ>*_
 
data Combined : Set where
  ⟪_▷_⟫ : (t : Tm) → (σ : State) → Combined
  ⟪_⟫    : (σ : State) → Combined
  ⟪⟫     : Combined

data _↠<_>_ : Combined → Label → Combined → Set where
  ↠-↦ : ∀ {t₁ t₂ σ Λ} →
    t₁ ↦< Λ > t₂ → ⟪ t₁ ▷ σ ⟫ ↠< Λ > ⟪ t₂ ▷ σ ⟫
  ↠-↣ : ∀ {σ₁ σ₂ Λ} →
    σ₁ ↣< Λ > σ₂ → ⟪ σ₁ ⟫ ↠< Λ > ⟪ σ₂ ⟫
  ↠-switch : ∀ { m c s } →
    ⟪ val m ▷ ⟨ c , s ⟩ ⟫ ↠< τ > ⟪ ⟨ c , m ∷ s ⟩ ⟫
  ↠-done : ∀ {m} →
    ⟪ ⟨ [] , m ∷ [] ⟩ ⟫ ↠< ! (◻ m) > ⟪⟫

_↠<τ>*_ : Combined → Combined → Set
_↠<τ>*_ = Star (λ x y → x ↠< τ > y)

-- Visible transition

infix 3 _⟾<_>_

data _⟾<_>_ : Combined → Action → Combined → Set where
  ⟾ : ∀ {x x′ y y′ α} →
    x ↠<τ>* x′ → x′ ↠< ! α > y′ → y′ ↠<τ>* y → x ⟾< α > y

-- Bisimulation

data _≈_ : Combined → Combined → Set where
  bisim : ∀ {x y} →
    (∀ {x′ α} → x ⟾< α > x′ → ∃ λ y′ → y ⟾< α > y′ × x′ ≈ y′) →
    (∀ {y′ α} → y ⟾< α > y′ → ∃ λ x′ → x ⟾< α > x′ × y′ ≈ x′) →
    x ≈ y

≈-refl : ∀ {x} → x ≈ x
-- A proof by coinduction would be easy... :-(
≈-refl {x} = bisim {x} {x}
       (λ {x′} {α} x⟾ → x′ , x⟾ , {!!})
       (λ {y′} {α} y⟾ → y′ , y⟾ , {!!})

--
