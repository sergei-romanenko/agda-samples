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
open import Category.Monad.Partiality as Partiality

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

--open import Algebra.Structures using (module IsCommutativeSemiringWithoutOne)

--open ≡-Reasoning

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

  private module M{f} = RawMonad (Partiality.monad {f})
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

  open Workaround renaming (_>>=_ to _>>=′_)

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
    C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′
  C⟦ if b c₁ c₂ ⟧′ σ =
    CIf (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧′ σ =
    CWhile (B⟦ b ⟧ σ) b c σ

  CIf true c₁ c₂ σ =
    C⟦ c₁ ⟧′ σ
  CIf false c₁ c₂ σ =
    C⟦ c₂ ⟧′ σ

  CWhile true b c σ =
    C⟦ c ⟧′ σ >>=′ (λ σ′ → later (♯ C⟦ while b c ⟧′ σ′))
  CWhile false b c σ =
    return σ

  C⟦_⟧ : (c : Cmd) → (σ : State) → State ⊥
  C⟦ c ⟧ σ = ⟦ C⟦ c ⟧′ σ ⟧P

  open module M {f} = RawMonad (Partiality.monad {f})

  private
    open module PE {A : Set} = Partiality.Equality (_≡_ {A = A})

    open module PR {A : Set} =
      Partiality.Reasoning (P.isEquivalence {A = A})
      renaming (_∎ to _□)

 -- C⇒⇩

  C⇒⇩ : (c : Cmd) (σ σ′ : State) → C⟦ c ⟧ σ ≈ now σ′ → c / σ ⇩ σ′
  -- C⇒⇩ i c σ σ′ h = {!c!}
  C⇒⇩ skip σ σ′ (now eq)
    rewrite P.sym eq = ⇩-skip
  C⇒⇩ (assign v a) σ σ′ (now eq)
    rewrite P.sym eq = ⇩-assign
  C⇒⇩ (seq c₁ c₂) σ σ′ h with C⟦ c₁ ⟧ σ
  C⇒⇩ (seq c₁ c₂) σ σ′ h | now σ′′ = {!!}
  C⇒⇩ (seq c₁ c₂) σ σ′ h | later x = {!!}
  C⇒⇩ (if b c₁ c₂) σ σ′ h = {!!}
  C⇒⇩ (while b c) σ σ′ h = {!!}

{-
  C⇒⇩ i skip .σ′ σ′ refl =
    ⇩-skip
  C⇒⇩ i (assign v a) σ .(update σ v (A⟦ a ⟧ σ)) refl =
    ⇩-assign
  C⇒⇩ i (seq c₁ c₂) σ σ′ h with C⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  ... | r | [ g₁ ]ⁱ = ?
  C⇒⇩ i (if b c₁ c₂) σ σ′ h = {!h!}
  C⇒⇩ i (while b c) σ σ′ h = {!h!}
-}

  -- ⇩⇒C

  infix 5 _⟦seq⟧_

  _⟦seq⟧_ : State ⊥ → (State → State ⊥) → State ⊥
  v ⟦seq⟧ f = v >>= λ σ → f σ

  ⟦seq⟧-cong : ∀ {k v₁ v₂ f} →
    Rel k v₁ v₂ → Rel k (v₁ ⟦seq⟧ f) (v₂ ⟦seq⟧ f)
  ⟦seq⟧-cong {f = f} v₁≈v₂ =
    v₁≈v₂ ≡->>=-cong (λ σ → f σ □)

  seq-comp : ∀ c₁ c₂ σ → C⟦ seq c₁ c₂ ⟧ σ ≅ C⟦ c₁ ⟧ σ ⟦seq⟧ C⟦ c₂ ⟧
  seq-comp c₁ c₂ σ =
    C⟦ seq c₁ c₂ ⟧ σ
      ≅⟨ _ □ ⟩
    ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
      ≅⟨ Correct.>>=-hom (C⟦ c₁ ⟧′ σ) C⟦ c₂ ⟧′ ⟩
    (C⟦ c₁ ⟧ σ >>= (λ σ′ → C⟦ c₂ ⟧ σ′))
      ≅⟨ _ □ ⟩
    C⟦ c₁ ⟧ σ ⟦seq⟧ C⟦ c₂ ⟧
    □

  ⇩⇒C : (c : Cmd) (σ σ′ : State) →
      c / σ ⇩ σ′ → C⟦ c ⟧ σ ≈ now σ′

  ⇩⇒C skip .σ′ σ′ ⇩-skip =
    now refl
  ⇩⇒C (assign v a) σ .(update σ v (A⟦ a ⟧ σ)) ⇩-assign =
    now refl
  ⇩⇒C (seq c₁ c₂) σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂) =
    C⟦ seq c₁ c₂ ⟧ σ
      ≅⟨ seq-comp c₁ c₂ σ ⟩
    C⟦ c₁ ⟧ σ ⟦seq⟧ C⟦ c₂ ⟧
      ≈⟨ ⟦seq⟧-cong (⇩⇒C c₁ σ σ′ h₁) ⟩
    C⟦ c₂ ⟧ σ′
      ≈⟨ ⇩⇒C c₂ σ′ σ′′ h₂ ⟩
    now σ′′ □
  ⇩⇒C (if b c₁ c₂) σ σ′ h = {!!}
  ⇩⇒C (while b c) σ σ′ h = {!!}

--
