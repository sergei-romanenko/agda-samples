module CmdLangSem-StepIndexed where

open import Data.Bool
  renaming (_≟_ to _≟B_)
open import Data.Nat
open import Data.Fin
  renaming (_≤_ to _≤F_; _+_ to _+F_)
open import Data.Maybe
open import Data.Product
open import Data.Vec

open import Function

open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open import Algebra.Structures using (module IsCommutativeSemiringWithoutOne)

open ≡-Reasoning

open import CmdLang

--
-- CmdLangSem
-- Step-indexed evaluation function

record CmdLangSem (memory : Memory) (absCmdLang : AbsCmdLang memory) : Set₁
  where
  open Memory memory
  open AbsCmdLang absCmdLang

  -- C_⟦_⟧

  C_⟦_⟧ : (i : ℕ) (c : Cmd) (σ : State) → Maybe State
  CWhile : (i : ℕ) (bv : Bool) (b : BExp) (c : Cmd) (σ : State) → Maybe State
  CIf : (i : ℕ) (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → Maybe State

  C zero ⟦ c ⟧ σ =
    nothing
  C suc i ⟦ skip ⟧ σ =
    return σ
  C suc i ⟦ assign v a ⟧ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C suc i ⟦ seq c₁ c₂ ⟧ σ =
    σ′ ← C i ⟦ c₁ ⟧ σ , C i ⟦ c₂ ⟧ σ′
  C suc i ⟦ if b c₁ c₂ ⟧ σ =
    CIf i (B⟦ b ⟧ σ) c₁ c₂ σ
  C suc i ⟦ while b c ⟧ σ =
    CWhile i (B⟦ b ⟧ σ) b c σ

  CIf i true c₁ c₂ σ =
    C i ⟦ c₁ ⟧ σ
  CIf i false c₁ c₂ σ =
    C i ⟦ c₂ ⟧ σ

  CWhile i true b c σ =
    σ′ ← C i ⟦ c ⟧ σ , C i ⟦ while b c ⟧ σ′
  CWhile i false b c σ =
    return σ

  -- Auxiliaries

  <′⇨≤′ : {i j : ℕ} → i <′ j → i ≤′ j
  <′⇨≤′ ≤′-refl = ≤′-step ≤′-refl
  <′⇨≤′ (≤′-step m≤′n) = ≤′-step (<′⇨≤′ m≤′n)

  n≤m⊔n : ∀ m n → n ≤ m ⊔ n
  n≤m⊔n m n = subst (_≤_ n) (+-comm _ m) (m≤m⊔n _ _)
    where
    open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne

  -- C-mono

  C-mono : (i j : ℕ) → i ≤′ j → (c : Cmd) (σ σ′ : State) →
    C i ⟦ c ⟧ σ ≡ just σ′ → C j ⟦ c ⟧ σ ≡ just σ′

  C-mono zero j i≤′j c σ σ′ ()

  C-mono (suc i) zero () c σ σ′ h

  C-mono (suc .j) (suc j) ≤′-refl c σ σ′ h = h

  C-mono (suc i) (suc j) (≤′-step i<′j) c σ σ′′ h = helper c h
    where
    helper : (c : Cmd) →
             C suc i ⟦ c ⟧ σ ≡ just σ′′ → C suc j ⟦ c ⟧ σ ≡ just σ′′

    helper skip h′ = h′

    helper (assign v a) h′ = h′

    helper (seq c₁ c₂) h′
      with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
    helper (seq c₁ c₂) h′
      | just σ′ | [ g₁ ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c₁ σ σ′ g₁
      = C-mono i j (<′⇨≤′ i<′j) c₂ σ′ σ′′ h′
    helper (seq c₁ c₂) ()
      | nothing | [ g ]ⁱ

    helper (if b c₁ c₂) h′ with B⟦ b ⟧ σ
    helper (if b c₁ c₂) h′ | true
      with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
    helper (if b c₁ c₂) h′ | true
      | just σ′ | [ g₁ ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c₁ σ σ′ g₁ = h′
    helper (if b c₁ c₂) () | true
      | nothing | [ g₁ ]ⁱ
    helper (if b c₁ c₂) h′ | false
      with C i ⟦ c₂ ⟧ σ | inspect (C i ⟦ c₂ ⟧) σ
    helper (if b c₁ c₂) h′ | false
      | just σ′ | [ g₂ ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c₂ σ σ′ g₂ = h′
    helper (if b c₁ c₂) () | false
      | nothing | [ g₂ ]ⁱ

    helper (while b c) h′ with B⟦ b ⟧ σ
    helper (while b c) h′ | true
      with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
    helper (while b c) h′ | true
      | just σ′ | [ g ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c σ σ′ g
      = C-mono i j (<′⇨≤′ i<′j) (while b c) σ′ σ′′ h′
    helper (while b c') () | true
      | nothing | [ g ]ⁱ
    helper (while b c) h′ | false = h′

  -- C⇒⇩

  C⇒⇩ : (i : ℕ) (c : Cmd) (σ σ′ : State) →
    C i ⟦ c ⟧ σ ≡ just σ′ → c / σ ⇩ σ′

  C⇒⇩ zero c σ σ′ ()

  C⇒⇩ (suc i) skip .σ′ σ′ refl = ⇩-skip

  C⇒⇩ (suc i) (assign v a) σ .(update σ v (A⟦ a ⟧ σ )) refl = ⇩-assign

  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ h
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ h
    | just σ′ | [ g ]ⁱ
    = ⇩-seq (C⇒⇩ i c₁ σ σ′ g) (C⇒⇩ i c₂ σ′ σ′′ h)
  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ () | nothing | [ g ]ⁱ

  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ h
    with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ 
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ h | true | [ f ]ⁱ
    | just σ′ | [ g₁ ]ⁱ
    = ⇩-if-true f (C⇒⇩ i c₁ σ σ′′ (trans g₁ h))
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ () | true | [ f ]ⁱ
    | nothing | [ g₁ ]ⁱ
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ h | false | [ f ]ⁱ
    with C i ⟦ c₂ ⟧ σ | inspect (C i ⟦ c₂ ⟧) σ
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ h | false | [ f ]ⁱ
    | just σ′ | [ g₂ ]ⁱ
    = ⇩-if-false f (C⇒⇩ i c₂ σ σ′′ (trans g₂ h))
  C⇒⇩ (suc i) (if b c₁ c₂) σ σ′′ () | false | [ f ]ⁱ
    | nothing | [ g₂ ]ⁱ

  C⇒⇩ (suc i) (while b c) σ σ′′ h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
  C⇒⇩ (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
    | just σ′ | [ g ]ⁱ
    = ⇩-while-true f (C⇒⇩ i c σ σ′ g) (C⇒⇩ i (while b c) σ′ σ′′ h)
  C⇒⇩ (suc i) (while b c) σ σ′′ () | true | [ f ]ⁱ
    | nothing | [ g ]ⁱ
  C⇒⇩ (suc i) (while b c) .σ′′ σ′′ refl | false | [ f ]ⁱ =
    ⇩-while-false f

  -- ⇩⇒C

  ⇩⇒C : (c : Cmd) (σ σ′ : State) →
      c / σ ⇩ σ′ → ∃ λ i → C i ⟦ c ⟧ σ ≡ just σ′

  ⇩⇒C skip .σ′ σ′ ⇩-skip =
    suc zero , refl

  ⇩⇒C (assign v a) σ .(update σ v (A⟦ a ⟧ σ)) ⇩-assign =
    suc zero , refl

  ⇩⇒C (seq c₁ c₂) σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂)
    with ⇩⇒C c₁ σ σ′ h₁ | ⇩⇒C c₂ _ σ′′ h₂
  ⇩⇒C (seq c₁ c₂) σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂)
    | i₁ , g₁ | i₂ , g₂
    = suc (i₁ ⊔ i₂) , (
      begin
        bind (C i₁ ⊔ i₂ ⟦ c₁ ⟧ σ) (C i₁ ⊔ i₂ ⟦ c₂ ⟧)
          ≡⟨ cong (λ e → bind e C i₁ ⊔ i₂ ⟦ c₂ ⟧)
                  (C-mono i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) c₁ σ σ′ g₁) ⟩
        C i₁ ⊔ i₂ ⟦ c₂ ⟧ σ′
          ≡⟨ C-mono i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) c₂ σ′ σ′′ g₂ ⟩
        just σ′′
      ∎)

  ⇩⇒C (if b c₁ c₂) σ σ′′ (⇩-if-true b≡t h) with ⇩⇒C c₁ σ σ′′ h
  ... | i₁ , g₁ = (suc i₁) , trans (cong (λ e → CIf i₁ e c₁ c₂ σ) b≡t) g₁
  ⇩⇒C (if b c₁ c₂) σ σ′′ (⇩-if-false b≡f h) with ⇩⇒C c₂ σ σ′′ h
  ... | i₂ , g₂ = (suc i₂) , trans (cong (λ e → CIf i₂ e c₁ c₂ σ) b≡f) g₂

  ⇩⇒C (while b c) σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂)
    with ⇩⇒C c σ σ′ h₁ | ⇩⇒C (while b c) σ′ σ′′ h₂
  ⇩⇒C (while b c) σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂)
    | i₁ , g₁ | i₂ , g₂
    = (suc (i₁ ⊔ i₂)) , (
      begin
        CWhile (i₁ ⊔ i₂) (B⟦ b ⟧ σ) b c σ
          ≡⟨ cong (λ e → CWhile (i₁ ⊔ i₂) e b c σ) b≡t ⟩
        bind (C i₁ ⊔ i₂ ⟦ c ⟧ σ) C i₁ ⊔ i₂ ⟦ while b c ⟧
          ≡⟨ cong (λ e → bind e C i₁ ⊔ i₂ ⟦ while b c ⟧)
                  (C-mono i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) c σ σ′ g₁) ⟩
        C i₁ ⊔ i₂ ⟦ while b c ⟧ σ′
          ≡⟨ C-mono i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) (while b c) σ′ σ′′ g₂ ⟩
        just σ′′
      ∎)
  ⇩⇒C (while b c) .σ′′ σ′′ (⇩-while-false b≡f) =
    suc zero , (cong (λ e → CWhile zero e b c σ′′) b≡f)

--
