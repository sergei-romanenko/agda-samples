module CmdLang where

open import Data.Bool
  renaming (_≟_ to _≟B_)
open import Data.Nat
open import Data.Fin
  renaming (_≤_ to _≤F_; _+_ to _+F_)
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Vec

open import Function

open import Data.Nat.Properties
open import Data.Bool.Properties

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open import Algebra.Structures using (module IsCommutativeSemiringWithoutOne)

open ≡-Reasoning

-- Memory

record Memory : Set₁ where
  field
    Var   : Set
    State : Set

    get    : (σ : State) → (v : Var) → ℕ
    update : (σ : State) → (v : Var) → ℕ → State

-- VecMemory

VecMemory : (n : ℕ) → Memory
VecMemory n = record
  { Var = Fin n
  ; State = Vec ℕ n
  ; get  = λ σ v → lookup v σ
  ; update = λ σ v x → σ [ v ]≔ x
  }

--
-- AbsCmdLang
-- Abstract command language
--

record AbsCmdLang (memory : Memory) : Set₁ where
  open Memory memory
  field
    AExp  : Set
    BExp  : Set
    A⟦_⟧  : (a : AExp) → (σ : State) → ℕ
    B⟦_⟧  : (b : BExp) → (σ : State) → Bool

  data Cmd : Set where
    skip   : Cmd
    assign : (v : Var) → (a : AExp) → Cmd
    seq    : (c₁ c₂ : Cmd) → Cmd
    if     : (b : BExp) → (c₁ c₂ : Cmd) → Cmd
    while  : (b : BExp) → (c : Cmd) → Cmd

  -- Big-step evaluation relation

  data _/_⇩_ : (c : Cmd) (σ σ′ : State) → Set where
    ⇩-skip :
      ∀ {σ} → skip / σ ⇩ σ
    ⇩-assign :
      ∀ {σ v a} → assign v a / σ ⇩ update σ v (A⟦ a ⟧ σ)
    ⇩-seq :
      ∀ {σ σ′ σ′′ c₁ c₂} → c₁ / σ ⇩ σ′ → c₂ / σ′ ⇩ σ′′ → seq c₁ c₂ / σ ⇩ σ′′
    ⇩-if-true :
      ∀ {σ σ′ b c₁ c₂} → (b≡t : B⟦ b ⟧ σ ≡ true) →
        c₁ / σ ⇩ σ′ → if b c₁ c₂ / σ ⇩ σ′
    ⇩-if-false :
      ∀ {σ σ′ b c₁ c₂} → (b≡f : B⟦ b ⟧ σ ≡ false) →
        c₂ / σ ⇩ σ′ → if b c₁ c₂ / σ ⇩ σ′
    ⇩-while-true :
      ∀ {σ σ′ σ′′ b c} → (b≡t : B⟦ b ⟧ σ ≡ true) →
        c / σ ⇩ σ′ → while b c / σ′ ⇩ σ′′ → while b c / σ ⇩ σ′′
    ⇩-while-false :
      ∀ {σ b c} → B⟦ b ⟧ σ ≡ false →
        while b c / σ ⇩ σ

  --
  -- Big-step evaluation relation is deterministic
  --

  ⇩-det⟦_⟧ : (c : Cmd) → {σ σ′ σ′′ : State} →
    c / σ ⇩ σ′ → c / σ ⇩ σ′′ → σ′ ≡ σ′′

  ⇩-det⟦ skip ⟧ ⇩-skip ⇩-skip = refl

  ⇩-det⟦ assign v a ⟧ ⇩-assign ⇩-assign = refl

  ⇩-det⟦ seq c₁ c₂ ⟧ (⇩-seq h₁ h₂) (⇩-seq g₁ g₂)
    rewrite ⇩-det⟦ c₁ ⟧ h₁ g₁
    = ⇩-det⟦ c₂ ⟧ h₂ g₂

  ⇩-det⟦ if b c₁ c₂ ⟧ (⇩-if-true b≡t h₁) (⇩-if-true b≡t' g₁) =
    ⇩-det⟦ c₁ ⟧ h₁ g₁
  ⇩-det⟦ if b c₁ c₂ ⟧ (⇩-if-true b≡t h₁) (⇩-if-false b≡f g₂) =
    ⊥-elim (not-¬ b≡t b≡f)
  ⇩-det⟦ if b c₁ c₂ ⟧ (⇩-if-false b≡f h₂) (⇩-if-true b≡t g₁) =
    ⊥-elim (not-¬ b≡f b≡t)
  ⇩-det⟦ if b c₁ c₂ ⟧ (⇩-if-false b≡f h₂) (⇩-if-false b≡f' g₂) =
    ⇩-det⟦ c₂ ⟧ h₂ g₂

  ⇩-det⟦ while b c ⟧ (⇩-while-true b≡t h₁ h₂) (⇩-while-true b≡t' g₁ g₂)
    rewrite ⇩-det⟦ c ⟧ h₁ g₁
    = ⇩-det⟦ while b c ⟧ h₂ g₂
  ⇩-det⟦ while b c ⟧ (⇩-while-true b≡t h g) (⇩-while-false b≡f) =
    ⊥-elim (not-¬ b≡t b≡f)
  ⇩-det⟦ while b c ⟧ (⇩-while-false b≡f) (⇩-while-true b≡t g₁ g₂) =
    ⊥-elim (not-¬ b≡f b≡t)
  ⇩-det⟦ while b c ⟧ (⇩-while-false b≡f) (⇩-while-false b≡f′) =
    refl

--
-- ArithCmdLang 
--

ArithCmdLang : (n : ℕ) → AbsCmdLang (VecMemory n)
ArithCmdLang n = record
  { AExp = AExp
  ; BExp = BExp

  ; A⟦_⟧ = A⟦_⟧
  ; B⟦_⟧ = B⟦_⟧
  }
  where
    memory = VecMemory n
    open Memory memory

    data AExp : Set where
      con  : (k : ℕ) → AExp
      var  : (v : Fin n) → AExp
      plus : (e₁ e₂ : AExp) → AExp

    data BExp : Set where
      eq  : (v : Fin n) (k : ℕ) → BExp
    
    A⟦_⟧ : AExp → State → ℕ

    A⟦ con k ⟧ σ = k
    A⟦ var v ⟧ σ = get σ v
    A⟦ plus e₁ e₂ ⟧ σ = A⟦ e₁ ⟧ σ + A⟦ e₂ ⟧ σ

    B⟦_⟧ : BExp → State → Bool

    B⟦ eq v k ⟧ σ with (get σ v) ≟ k
    ... | yes _ = true
    ... | no  _ = false

--
