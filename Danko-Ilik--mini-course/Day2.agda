module Day2 (Proposition : Set) where

open import Data.List
open import Data.Unit
  hiding(_≤_)
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

----------
-- Syntax
----------

--infixr 1 _⊃_

data Formula : Set where
  _⊃_ : Formula → Formula → Formula
  $_  : Proposition → Formula

data _⊢_ : List Formula → Formula → Set where
  hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ A
  ⊃i  : ∀ {Γ A B} → (A ∷ Γ) ⊢ B → Γ ⊢ (A ⊃ B)
  ⊃e  : ∀ {Γ A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B
  wkn : ∀ {Γ A B} → Γ ⊢ A → (B ∷ Γ) ⊢ A

module SampleProofs (a b c : Formula) where

  a⊃a : [] ⊢ (a ⊃ a)
  a⊃a = ⊃i hyp

  a⊃a' : [] ⊢ (a ⊃ a)
  a⊃a' = ⊃i p
    where
      p : (a ∷ []) ⊢ a
      p = hyp

  a-b-a : [] ⊢ (a ⊃ (b ⊃ a))
  a-b-a = ⊃i (⊃i (wkn hyp)) 

  a-b-a' : [] ⊢ (a ⊃ (b ⊃ a))
  a-b-a' = ⊃i p3
    where
      p1 : (a ∷ []) ⊢ a
      p1 = hyp
      p2 : (b ∷ a ∷ []) ⊢ a
      p2 = wkn p1
      p3 : (a ∷ []) ⊢ (b ⊃ a)
      p3 = ⊃i p2

  a-ab-b : [] ⊢ (a ⊃ ((a ⊃ b) ⊃ b))
  a-ab-b = ⊃i (⊃i (⊃e hyp (wkn hyp)))

  a-ab-b' : [] ⊢ (a ⊃ ((a ⊃ b) ⊃ b))
  a-ab-b' = ⊃i s
    where
      p : (a ⊃ b ∷ a ∷ []) ⊢ (a ⊃ b)
      p = hyp
      q1 : (a ∷ []) ⊢ a
      q1 = hyp
      q : (a ⊃ b ∷ a ∷ []) ⊢ a
      q = wkn q1
      r : (a ⊃ b ∷ a ∷ []) ⊢ b
      r = ⊃e p q
      s : (a ∷ []) ⊢ ((a ⊃ b) ⊃ b)
      s = ⊃i r

-- Worlds (Kripke structures)

record Kripke : Set₁ where
  field
    K : Set
    _≤_ : K → K → Set
    ≤-refl : {w : K} → w ≤ w
    ≤-trans : {w₁ w₂ w₃ : K} → w₁ ≤ w₂ → w₂ ≤ w₃ → w₁ ≤ w₃
    _⊨ᵃ_ : K → Proposition → Set
    ⊨ᵃ-≤ : {P : Proposition}{w₁ w₂ : K} → w₁ ≤ w₂ → w₁ ⊨ᵃ P → w₂ ⊨ᵃ P

module Soundness (kripke : Kripke) where

  open Kripke kripke

  _⊨_ : K → Formula → Set
  w ⊨ (A ⊃ B) = {w' : K} → w ≤ w' → w' ⊨ A → w' ⊨ B
  w ⊨ ($ P) = w ⊨ᵃ P

  ⊨-≤ : {A : Formula}{w₁ w₂ : K} → w₁ ≤ w₂ → w₁ ⊨ A → w₂ ⊨ A
  ⊨-≤ {A ⊃ B} = λ w₁≤w₂ f w₂≤w' a → f (≤-trans w₁≤w₂ w₂≤w') a
  ⊨-≤ {$ P} = ⊨ᵃ-≤

  _⊫_ : K → List Formula → Set
  w ⊫ [] = ⊤
  w ⊫ (A ∷ Γ) = (w ⊨ A) × (w ⊫ Γ)

  ⊫-≤ : {Γ : List Formula}{w₁ w₂ : K} → w₁ ≤ w₂ → w₁ ⊫ Γ → w₂ ⊫ Γ
  ⊫-≤ {[]} w₁≤w₂ ρ = ρ
  ⊫-≤ {A ∷ Γ} w₁≤w₂ (a , ρ) = (⊨-≤ {A} w₁≤w₂ a , ⊫-≤ {Γ} w₁≤w₂ ρ) 

  soundness : ∀ {Γ A} → Γ ⊢ A → {w : K} → w ⊫ Γ → w ⊨ A
  soundness hyp (a , ρ) = a
  soundness {Γ} (⊃i p) ρ = λ w≤w' a' → soundness p (a' , (⊫-≤ {Γ} w≤w' ρ))
  soundness (⊃e p q) ρ = (soundness p ρ) ≤-refl (soundness q ρ)
  soundness (wkn p) (a , ρ) = soundness p ρ


module Completeness where

  data _≼_ : List Formula → List Formula → Set where 
    ≼-refl : ∀ {Γ} → Γ ≼ Γ
    ≼-cons : ∀ {Γ₁ Γ₂ A} → Γ₁ ≼ Γ₂ → Γ₁ ≼ (A ∷ Γ₂)

  ≼-trans : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≼ Γ₂ → Γ₂ ≼ Γ₃ → Γ₁ ≼ Γ₃
  ≼-trans ≼₁₂ ≼-refl = ≼₁₂
  ≼-trans ≼₁₂ (≼-cons ≼₂₃) = ≼-cons (≼-trans ≼₁₂ ≼₂₃)

  ⊢-≼ : {A : Formula} {Γ₁ Γ₂ : List Formula} → Γ₁ ≼ Γ₂ → Γ₁ ⊢ A → Γ₂ ⊢ A
  ⊢-≼ ≼-refl H₁ = H₁
  ⊢-≼ (≼-cons ≼₁₂) H₁ = wkn (⊢-≼ ≼₁₂ H₁)

  uks : Kripke
  uks = record { K = List Formula;
                 _≤_ = _≼_;
                 ≤-refl = ≼-refl;
                 ≤-trans = ≼-trans;
                 _⊨ᵃ_ = λ Γ P → Γ ⊢ ($ P);
                 ⊨ᵃ-≤ = ⊢-≼ }

  open Kripke uks
  open Soundness uks

  mutual
    reify : ∀ {A Γ} → Γ ⊨ A → Γ ⊢ A
    reify {A ⊃ B} =
      λ φ → ⊃i (reify {B} (φ (≼-cons ≼-refl) (reflect {A} hyp)))
    reify {$ P} = λ α → α

    reflect : ∀ {A Γ} → Γ ⊢ A → Γ ⊨ A
    reflect {A ⊃ B} =
      λ p → λ ≤' α' → reflect {B} (⊃e (⊢-≼ ≤' p) (reify {A} α'))
    reflect {$ P} = λ p → p

  nbe : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
  nbe {Γ} p = reify (soundness p (reflect-context Γ))
    where
      reflect-context : (Γ : List Formula) → Γ ⊫ Γ
      reflect-context [] = tt
      reflect-context (A ∷ Γ') =
        (reflect {A} hyp , ⊫-≤ {Γ'} (≼-cons ≼-refl) (reflect-context Γ'))

  -- Actually, for reify/reflect, and NBE, we may use the more
  -- precise data type for natural deduction, that distinguishes
  -- between neutral and normal terms

  mutual
    data _⊢ʳ_ : List Formula → Formula → Set where
      ⊃i : ∀ {Γ A B} → (A ∷ Γ) ⊢ʳ B → Γ ⊢ʳ (A ⊃ B)
      e2r : ∀ {Γ A} → Γ ⊢ᵉ A → Γ ⊢ʳ A
    data _⊢ᵉ_ : List Formula → Formula → Set where
      hyp : ∀ {Γ A} → (A ∷ Γ) ⊢ᵉ A
      ⊃e : ∀ {Γ A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ʳ A → Γ ⊢ᵉ B
      wkn : ∀ {Γ A B} → Γ ⊢ᵉ A → (B ∷ Γ) ⊢ᵉ A
