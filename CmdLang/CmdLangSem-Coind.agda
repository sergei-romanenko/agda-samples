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

open import Induction.WellFounded
open import Induction.Nat

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
  C⟦If⟧ : (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → State ⊥
  C⟦While⟧ : (bv : Bool) (b : BExp) (c : Cmd) (σ : State) → State ⊥

  C⟦ skip ⟧ σ =
    return σ
  C⟦ assign v a ⟧ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C⟦ seq c₁ c₂ ⟧ σ =
    C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧
  C⟦ if b c₁ c₂ ⟧ σ =
    C⟦If⟧ (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧ σ =
    C⟦While⟧ (B⟦ b ⟧ σ) b c σ

  C⟦If⟧ true c₁ c₂ σ =
    C⟦ c₁ ⟧ σ
  C⟦If⟧ false c₁ c₂ σ =
    C⟦ c₂ ⟧ σ

  C⟦While⟧ true b c σ =
    C⟦ c ⟧ σ >>= C⟦ while b c ⟧
  C⟦While⟧ false b c σ =
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
  C⟦If⟧′ : (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → State ⊥P
  C⟦While⟧′ : (bv : Bool) (b : BExp) (c : Cmd) (σ : State) → State ⊥P

  C⟦ skip ⟧′ σ =
    return σ
  C⟦ assign v a ⟧′ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C⟦ seq c₁ c₂ ⟧′ σ =
    C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′
  C⟦ if b c₁ c₂ ⟧′ σ =
    C⟦If⟧′ (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧′ σ =
    C⟦While⟧′ (B⟦ b ⟧ σ) b c σ

  C⟦If⟧′ true c₁ c₂ σ =
    C⟦ c₁ ⟧′ σ
  C⟦If⟧′ false c₁ c₂ σ =
    C⟦ c₂ ⟧′ σ

  C⟦While⟧′ true b c σ =
    later (♯ C⟦ seq c (while b c) ⟧′ σ)
  C⟦While⟧′ false b c σ =
    return σ

  C⟦_⟧ : (c : Cmd) → (σ : State) → State ⊥
  C⟦ c ⟧ σ = ⟦ C⟦ c ⟧′ σ ⟧P

  --
  -- Correctness
  --

  open module M {f} = RawMonad (Partiality.monad {f})

  private
    open module PE {A : Set} = Partiality.Equality (_≡_ {A = A})

    open module PR {A : Set} =
      Partiality.Reasoning (P.isEquivalence {A = A})
      renaming (_∎ to _□)

  --
  -- C⇒⇩
  --

  C⇒⇩ : (c : Cmd) (σ σ′ : State) → C⟦ c ⟧ σ ≈ now σ′ → c / σ ⇩ σ′

  C⇒⇩′ : ∀ s (c : Cmd) (σ σ′ : State) (h : C⟦ c ⟧ σ ≈ now σ′) →
               steps h ≡ s → Acc _<′_ s → c / σ ⇩ σ′

  -- C⇒⇩ = ... 

  C⇒⇩ c σ σ′′ h = C⇒⇩′ (steps h) c σ σ′′ h refl (<-well-founded (steps h))

  -- C⇒⇩′ = ...

  C⇒⇩′ s skip σ σ′′ (now eq) q a rewrite P.sym eq =
    ⇩-skip

  C⇒⇩′ s (assign v e) σ σ′′ (now eq) q a rewrite P.sym eq =
    ⇩-assign

  C⇒⇩′ s (seq c₁ c₂) σ σ′′ h q (acc p) =
    helper seq-inv
    where
      seq-comp : (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧) ≈ now σ′′
      seq-comp =
        (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧)
          ≅⟨ PR.sym (Correct.>>=-hom (C⟦ c₁ ⟧′ σ) C⟦ c₂ ⟧′) ⟩
        ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
          ≈⟨ _ □ ⟩
        C⟦ seq c₁ c₂ ⟧ σ
          ≈⟨ h ⟩
        now σ′′
        □

      seq-inv : ∃ λ σ′ →
        ∃₂ λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
          steps h₁ + steps h₂ ≡ steps seq-comp
      seq-inv = >>=-inversion-⇓ refl (C⟦ c₁ ⟧ σ) seq-comp

      helper : ∃ (λ σ′ →
        ∃₂ (λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
                  steps h₁ + steps h₂ ≡ steps seq-comp)) →
           seq c₁ c₂ / σ ⇩ σ′′
      helper (σ′ , h₁ , h₂ , s+s≡s) =
        ⇩-seq (C⇒⇩′ (steps h₁) c₁ σ σ′ h₁ P.refl (p (steps h₁) prop₁))
              (C⇒⇩′ (steps h₂) c₂ σ′ σ′′ h₂ P.refl (p (steps h₂) prop₂))
        where
          prop₁ : steps h₁ <′ s
          prop₁ = {!!}
          prop₂ : steps h₂ <′ s
          prop₂ = {!!}

  C⇒⇩′ s (if b c₁ c₂) σ σ′′ h q a with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  ... | true | [ b≡t ]ⁱ =
    ⇩-if-true b≡t (C⇒⇩′ s c₁ σ σ′′ h q a)
  ... | false | [ b≡f ]ⁱ =
    ⇩-if-false b≡f (C⇒⇩′ s c₂ σ σ′′ h q a)

  C⇒⇩′ s (while b c) σ σ′′ h q (acc p) with  B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ

  C⇒⇩′ s (while b c) σ σ′′ (laterˡ h) q (acc p) | true | [ b≡t ]ⁱ =
    helper seq-inv
    where
      seq-comp : (C⟦ c ⟧ σ >>= C⟦ while b c ⟧) ≈ now σ′′
      seq-comp =
        (C⟦ c ⟧ σ >>= C⟦ while b c ⟧)
          ≅⟨ PR.sym (Correct.>>=-hom (C⟦ c ⟧′ σ) C⟦ while b c ⟧′) ⟩
        ⟦ C⟦ c ⟧′ σ >>=′ C⟦ while b c ⟧′ ⟧P
          ≈⟨ _ □ ⟩
        C⟦ seq c (while b c) ⟧ σ
          ≈⟨ h ⟩
        now σ′′
        □

      seq-inv : ∃ λ σ′ →
        ∃₂ λ (h₁ : C⟦ c ⟧ σ ≈ now σ′) (h₂ : C⟦ while b c ⟧ σ′ ≈ now σ′′) →
          steps h₁ + steps h₂ ≡ steps seq-comp
      seq-inv = >>=-inversion-⇓ refl (C⟦ c ⟧ σ) seq-comp
      
      helper : ∃ (λ σ′ →
        ∃₂ (λ (h₁ : C⟦ c ⟧ σ ≈ now σ′) (h₂ : C⟦ while b c ⟧ σ′ ≈ now σ′′) →
                  steps h₁ + steps h₂ ≡ steps seq-comp)) →
           while b c / σ ⇩ σ′′ --seq c (while b c) / σ ⇩ σ′′
      helper (σ′ , h₁ , h₂ , s+s≡s) =
        ⇩-while-true b≡t
          (C⇒⇩′ (steps h₁) c σ σ′ h₁ P.refl (p (steps h₁) prop₁))
          (C⇒⇩′ (steps h₂) (while b c) σ′ σ′′ h₂ P.refl (p (steps h₂) prop₂))
        where
          prop₁ : steps h₁ <′ s
          prop₁ = {!!}
          prop₂ : steps h₂ <′ s
          prop₂ = {!!}
      
  C⇒⇩′ s (while b c) σ σ′′ (now eq) q (acc p) | false | [ b≡f ]ⁱ rewrite eq =
    ⇩-while-false b≡f

  --
  -- ⇩⇒C
  --

  ⇩⇒C : (c : Cmd) (σ σ′ : State) →
      c / σ ⇩ σ′ → C⟦ c ⟧ σ ≈ now σ′

  ⇩⇒C⟦seq⟧ : (c₁ c₂ : Cmd) (σ σ′ σ′′ : State) →
      (h₁ : c₁ / σ ⇩ σ′) → (h₂ : c₂ / σ′ ⇩ σ′′) →
        C⟦ seq c₁ c₂ ⟧ σ ≈ now σ′′

  ⇩⇒C skip .σ′ σ′ ⇩-skip =
    now refl

  ⇩⇒C (assign v a) σ .(update σ v (A⟦ a ⟧ σ)) ⇩-assign =
    now refl

  ⇩⇒C (seq c₁ c₂) σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂) =
    ⇩⇒C⟦seq⟧ c₁ c₂ σ σ′ σ′′ h₁ h₂

  ⇩⇒C (if b c₁ c₂) σ σ′ (⇩-if-true b≡t h₁) rewrite b≡t =
    ⇩⇒C c₁ σ σ′ h₁
  ⇩⇒C (if b c₁ c₂) σ σ′ (⇩-if-false b≡f h₂) rewrite b≡f =
    ⇩⇒C c₂ σ σ′ h₂

  ⇩⇒C (while b c) σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂) rewrite b≡t =
    laterˡ (⇩⇒C⟦seq⟧ c (while b c) σ σ′ σ′′ h₁ h₂)

  ⇩⇒C (while b c) .σ σ (⇩-while-false b≡f) rewrite b≡f =
    now refl

  -- ⇩⇒C⟦seq⟧

  ⟦seq⟧-cong : ∀ {k} {v₁ v₂ : State ⊥} {f : State → State ⊥} →
    Rel k v₁ v₂ → Rel k (v₁ >>= f) (v₂ >>= f)
  ⟦seq⟧-cong {f = f} v₁≈v₂ =
    v₁≈v₂ ≡->>=-cong (λ σ → f σ □)

  ⇩⇒C⟦seq⟧ c₁ c₂ σ σ′ σ′′ h₁ h₂ =
    C⟦ seq c₁ c₂ ⟧ σ
      ≅⟨ _ □ ⟩
    ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
      ≅⟨ Correct.>>=-hom (C⟦ c₁ ⟧′ σ) C⟦ c₂ ⟧′ ⟩
    (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧)
      ≈⟨ ⟦seq⟧-cong (⇩⇒C c₁ σ σ′ h₁) ⟩
    (now σ′ >>= C⟦ c₂ ⟧)
      ≈⟨ _ □ ⟩
    C⟦ c₂ ⟧ σ′
      ≈⟨ ⇩⇒C c₂ σ′ σ′′ h₂ ⟩
    now σ′′
    □

--
