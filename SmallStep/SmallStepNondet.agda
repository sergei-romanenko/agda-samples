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

open import Data.Star
open import Data.Star.Properties

open import Function

open import Function.Equivalence
  using (_⇔_; equivalence)

open import Coinduction

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
  #_  : (n : ℕ) → Tm
  _⊕_ : (t₁ t₂ : Tm) → Tm


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

data _↣<_>_ : State → Label → State → Set where
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
  ↠-switch : ∀ {m c s} →
    ⟪ # m ▷ ⟨ c , s ⟩ ⟫ ↠< τ > ⟪ ⟨ c , m ∷ s ⟩ ⟫
  ↠-done : ∀ {m} →
    ⟪ ⟨ [] , m ∷ [] ⟩ ⟫ ↠< ! (◻ m) > ⟪⟫

_↠<τ>*_ : Combined → Combined → Set
_↠<τ>*_ = Star (λ x y → x ↠< τ > y)

-- Visible transition

infix 3 _⤇<_>_

data _⤇<_>_ : Combined → Action → Combined → Set where
  ⤇ : ∀ {x x′ y y′ α}
    (h₁ : x ↠<τ>* x′) (h₂ : x′ ↠< ! α > y′) (h₃ : y′ ↠<τ>* y) → x ⤇< α > y

-- Simulation

data _≲_ : Combined → Combined → Set where
  ≲-step : ∀ {x y} →
    (h : ∀ {x′ α} → x ⤇< α > x′ → ∃ λ y′ → y ⤇< α > y′ × ∞ (x′ ≲ y′)) →
    x ≲ y


≲-refl : ∀ {x} → x ≲ x
≲-refl {x} = ≲-step (λ {x′} x⤇x′ → x′ , x⤇x′ , ♯ ≲-refl)

≲-trans : ∀ {x y z} (x≲y : x ≲ y) (y≲z : y ≲ z) → x ≲ z
≲-trans (≲-step {x} {y} h) (≲-step {.y} {z} g) = ≲-step helper
  where
  helper : ∀ {x′ α} → x ⤇< α > x′ →
             Σ Combined (λ y′ → Σ (z ⤇< α > y′) (λ x₁ → ∞ (x′ ≲ y′)))
  helper x⤇x′ with h x⤇x′
  helper x⤇x′ | y′ , y⤇y′ , ∞x′≲y′ with g y⤇y′
  ... | z′ , z⤇z′ , ∞y′≲z′ =
    z′ , z⤇z′ , ♯ ≲-trans (♭ ∞x′≲y′) (♭ ∞y′≲z′)

-- Bisimulation

data _≈_ : Combined → Combined → Set where
  _,_ :  ∀ {x y} → (x≲y : x ≲ y) → (y≲x : y ≲ x) → x ≈ y

≈-refl : ∀ {x} → x ≈ x
≈-refl {x} = ≲-refl , ≲-refl

≈-trans : ∀ {x y z} (x≈y : x ≈ y ) (y≈z : y ≈ z) → x ≈ z
≈-trans (x≲y , y≲x) (y≲z , z≲y) =
  (≲-trans x≲y y≲z) , (≲-trans z≲y y≲x)

≈-sym : ∀ {x y} (x≈y : x ≈ y) → y ≈ x
≈-sym (x≲y , y≲x) = y≲x , x≲y

--
-- ≈-Reasoning
--

open import Relation.Binary
  using (Setoid)

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


--
-- elide-τ
--

↠<τ>∘⤇<> : ∀ {x x′ y α} → x ↠< τ > x′ → x′ ⤇< α > y → x ⤇< α > y
↠<τ>∘⤇<> h (⤇ g₁ g₂ g₃) = ⤇ (h ◅ g₁) g₂ g₃

¬↦<τ> : ∀ {t₁ t₂} → t₁ ↦< τ > t₂ → ⊥
¬↦<τ> (r+t h) = ¬↦<τ> h
¬↦<τ> (n+r h) = ¬↦<τ> h

-- elide-τ-≲

elide-τ-≲ : ∀ {x y} → x ↠< τ > y → x ≲ y

elide-τ-≲ (↠-↦ {t₁} {t₂} {σ} {.τ} h) = ⊥-elim (¬↦<τ> h)
elide-τ-≲ (↠-↣ (↣-push {c} {s} {m})) = ≲-step helper
  where
  helper : ∀ {x′ α} → ⟪ ⟨ push m ∷ c , s ⟩ ⟫ ⤇< α > x′ →
             ∃ (λ y′ → Σ (⟪ ⟨ c , m ∷ s ⟩ ⟫ ⤇< α > y′) (λ x → ∞ (x′ ≲ y′)))
  helper (⤇ ε (↠-↣ ()) _)
  helper {x′} {α} (⤇ (↠-↣ ↣-push ◅ h₁) h₂ h₃) =
    x′ , ⤇ h₁ h₂ h₃ , ♯ ≲-refl
elide-τ-≲ (↠-switch {m} {c} {s}) = ≲-step helper
  where
  helper : ∀ {x′ α} → ⟪ # m ▷ ⟨ c , s ⟩ ⟫ ⤇< α > x′ →
             ∃ (λ y′ → Σ (⟪ ⟨ c , m ∷ s ⟩ ⟫ ⤇< α > y′) (λ x → ∞ (x′ ≲ y′)))
  helper (⤇ ε (↠-↦ ()) _)
  helper (⤇ (↠-↦ () ◅ h₁) h₂ h₃)
  helper {x′} {α} (⤇ (↠-switch ◅ h₁) h₂ h₃) = x′ , ⤇ h₁ h₂ h₃ , ♯ ≲-refl

-- elide-τ-≳

elide-τ-≳ : ∀ {x y} → x ↠< τ > y → y ≲ x

elide-τ-≳ x↠<τ>y =
  ≲-step (λ {y′} y⤇y′ → y′ , ↠<τ>∘⤇<> x↠<τ>y y⤇y′ , ♯ ≲-refl)

-- elide-τ

elide-τ : ∀ {x y} → x ↠< τ > y → x ≈ y

elide-τ x↠<τ>y = elide-τ-≲ x↠<τ>y , elide-τ-≳ x↠<τ>y

postulate

  eval-left′ : ∀ {a b c σ} →
    ⟪ a ▷ ⟨ compile b (add ∷ c) , σ ⟩ ⟫ ≈ ⟪ a ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  eval-right′ : ∀ {m b c σ} →
    ⟪ b ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ # m ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  add≈m⊕n′ : ∀ {m n c σ} →
    ⟪ # n ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ # m ⊕ # n ▷ ⟨ c , σ ⟩ ⟫

{-
mutual

  eval-left : ∀ {a b c σ} →
    ⟪ a ▷ ⟨ compile b (add ∷ c) , σ ⟩ ⟫ ≈ ⟪ a ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  eval-left {a} {val n} = {!!}
  eval-left {a} {b ⊕ b₁} = {!!}

  eval-right : ∀ {m b c σ} →
    ⟪ b ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ val m ⊕ b ▷ ⟨ c , σ ⟩ ⟫

  eval-right = {!!}
-}

add≈m⊕n : ∀ {m n c σ} →
  ⟪ # n ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ≈ ⟪ # m ⊕ # n ▷ ⟨ c , σ ⟩ ⟫

--add≈m⊕n {m} {n} {c} {σ} = eval-right {m} {val n} {c} {σ}

add≈m⊕n {m} {n} {c} {σ} = (≲-step helper₁) , (≲-step helper₂)
  where
  postulate 
    helper₁ : ∀ {x′ α} → ⟪ # n ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ⤇< α > x′ →
      ∃ (λ y′ → ⟪ # m ⊕ # n ▷ ⟨ c , σ ⟩ ⟫ ⤇< α > y′ × ∞ (x′ ≲ y′))
  helper₂ : ∀ {x′ α} → ⟪ # m ⊕ # n ▷ ⟨ c , σ ⟩ ⟫ ⤇< α > x′ →
      ∃ (λ y′ → ⟪ # n ▷ ⟨ add ∷ c , m ∷ σ ⟩ ⟫ ⤇< α > y′ × ∞ (x′ ≲ y′))
  helper₂ {x′} {⊞} (⤇ h₁ (↠-↦ {t₁} {t₂} x) h₃) = {!h₁!}
  helper₂ {x′} {⊞} (⤇ h₁ (↠-↣ ↣-add) h₃) = {!!}
  helper₂ {x′} {↯} (⤇ h₁ h₂ h₃) = {!h₂!}
  helper₂ {x′} {◻ x} (⤇ h₁ h₂ h₃) = {!!}

--
-- correctness
--

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
