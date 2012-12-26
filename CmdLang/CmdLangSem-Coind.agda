module CmdLangSem-Coind where

open import Data.Bool
  renaming (_≟_ to _≟B_)
open import Data.Nat
--open import Data.Fin
--  renaming (_≤_ to _≤F_; _+_ to _+F_)
open import Data.Maybe
open import Data.Product
open import Data.Vec
  hiding (_>>=_)

open import Function

open import Data.Nat.Properties

open import Coinduction
open import Category.Monad
open import Category.Monad.Indexed using()
open import Category.Monad.Partiality

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

--open import Algebra.Structures using (module IsCommutativeSemiringWithoutOne)

open ≡-Reasoning

open import CmdLang

--
-- CmdLangSem-Bad
-- Step-indexed evaluation function
-- (Problems with productivity.)
--

record CmdLangSem-Bad (memory : Memory) (absCmdLang : AbsCmdLang memory) : Set₁
  where
  open Memory memory
  open AbsCmdLang absCmdLang

  private module M{f} = RawMonad (Category.Monad.Partiality.monad {f})
  open M

  -- C⟦_⟧

  C⟦_⟧ : (c : Cmd) (σ : State) → State ⊥
  CIf : (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → State ⊥
  CWhile : (bv : Bool) (b : BExp) (c : Cmd) (σ : State) → State ⊥

  C⟦ skip ⟧ σ =
    return σ
  C⟦ assign v a ⟧ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C⟦ seq c₁ c₂ ⟧ σ =
    C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧
  C⟦ if b c₁ c₂ ⟧ σ =
    CIf (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧ σ =
    CWhile (B⟦ b ⟧ σ) b c σ

  CIf true c₁ c₂ σ =
    C⟦ c₁ ⟧ σ
  CIf false c₁ c₂ σ =
    C⟦ c₂ ⟧ σ

  CWhile true b c σ =
    C⟦ c ⟧ σ >>= C⟦ while b c ⟧
  CWhile false b c σ =
    return σ

--
-- CmdLangSem
-- Step-indexed evaluation function
--

record CmdLangSem (memory : Memory) (absCmdLang : AbsCmdLang memory) : Set₁
  where
  open Memory memory
  open AbsCmdLang absCmdLang

  open Workaround

  return : State → State ⊥P
  return σ = now σ

  -- C⟦_⟧

  C⟦_⟧′ : (c : Cmd) (σ : State) → State ⊥P
  CIf : (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → State ⊥P
  CWhile : (bv : Bool) (b : BExp) (c : Cmd) (σ : State) → State ⊥P

  C⟦ skip ⟧′ σ =
    return σ
  C⟦ assign v a ⟧′ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C⟦ seq c₁ c₂ ⟧′ σ =
    C⟦ c₁ ⟧′ σ >>= C⟦ c₂ ⟧′
  C⟦ if b c₁ c₂ ⟧′ σ =
    CIf (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧′ σ =
    CWhile (B⟦ b ⟧ σ) b c σ

  CIf true c₁ c₂ σ =
    C⟦ c₁ ⟧′ σ
  CIf false c₁ c₂ σ =
    C⟦ c₂ ⟧′ σ

  CWhile true b c σ =
    C⟦ c ⟧′ σ >>= (λ σ′ → later (♯ C⟦ while b c ⟧′ σ′))
  CWhile false b c σ =
    return σ

  C⟦_⟧ : (c : Cmd) → (σ : State) → State ⊥
  C⟦ t ⟧ σ = ⟦ C⟦ t ⟧′ σ ⟧P

--
