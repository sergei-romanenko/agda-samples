module CmdLangSem-StepIndexed where

open import Data.Bool
  renaming (_≟_ to _≟B_)
open import Data.Nat
open import Data.Fin
  renaming (_≤_ to _≤F_; _+_ to _+F_)
open import Data.Maybe
open import Data.Product
open import Data.Vec
  hiding (_>>=_)

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

  infixl 1 _>>=_

  return : State → Maybe State
  return σ = just σ

  _>>=_ : (σ? : Maybe State) → (f : State → Maybe State) → Maybe State
  just σ  >>= f = f σ
  nothing >>= f = nothing

  -- C_⟦_⟧

  C_⟦_⟧ : (i : ℕ) (c : Cmd) (σ : State) → Maybe State
  C_⟦If⟧ : (i : ℕ) (bv : Bool) (c₁ c₂ : Cmd) (σ : State) → Maybe State
  C_⟦While⟧ : (i : ℕ) (bv : Bool) (b : BExp) (c : Cmd) (σ : State)
    → Maybe State

  C zero ⟦ c ⟧ σ =
    nothing
  C suc i ⟦ skip ⟧ σ =
    return σ
  C suc i ⟦ assign v a ⟧ σ =
    return (update σ v (A⟦ a ⟧ σ))
  C suc i ⟦ seq c₁ c₂ ⟧ σ =
    C i ⟦ c₁ ⟧ σ >>= (C i ⟦ c₂ ⟧)
  C suc i ⟦ if b c₁ c₂ ⟧ σ =
    C i ⟦If⟧ (B⟦ b ⟧ σ) c₁ c₂ σ
  C suc i ⟦ while b c ⟧ σ =
    C i ⟦While⟧ (B⟦ b ⟧ σ) b c σ

  C i ⟦If⟧ true c₁ c₂ σ =
    C i ⟦ c₁ ⟧ σ
  C i ⟦If⟧ false c₁ c₂ σ =
    C i ⟦ c₂ ⟧ σ

  C i ⟦While⟧ true b c σ =
    C i ⟦ c ⟧ σ >>= C i ⟦ while b c ⟧
  C i ⟦While⟧ false b c σ =
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

  C-mono⟦_⟧ : (c : Cmd) (i j : ℕ) → i ≤′ j → (σ σ′ : State) →
    C i ⟦ c ⟧ σ ≡ just σ′ → C j ⟦ c ⟧ σ ≡ just σ′

  C-mono⟦ c ⟧ zero j i≤′j σ σ′ ()

  C-mono⟦ c ⟧ (suc i) zero () σ σ′ h

  C-mono⟦ c ⟧ (suc .j) (suc j) ≤′-refl σ σ′ h = h

  C-mono⟦ c ⟧ (suc i) (suc j) (≤′-step i<′j) σ σ′′ h = helper⟦ c ⟧ h
    where
    helper⟦_⟧ : (c : Cmd) →
             C suc i ⟦ c ⟧ σ ≡ just σ′′ → C suc j ⟦ c ⟧ σ ≡ just σ′′

    helper⟦ skip ⟧ h′ = h′

    helper⟦ assign v a ⟧ h′ = h′

    helper⟦ seq c₁ c₂ ⟧ h′
      with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
    helper⟦ seq c₁ c₂ ⟧ h′
      | just σ′ | [ g₁ ]ⁱ rewrite C-mono⟦ c₁ ⟧ i j (<′⇨≤′ i<′j) σ σ′ g₁
      = C-mono⟦ c₂ ⟧ i j (<′⇨≤′ i<′j) σ′ σ′′ h′
    helper⟦ seq c₁ c₂ ⟧ ()
      | nothing | [ g ]ⁱ

    helper⟦ if b c₁ c₂ ⟧ h′ with B⟦ b ⟧ σ
    helper⟦ if b c₁ c₂ ⟧ h′ | true
      with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
    helper⟦ if b c₁ c₂ ⟧ h′ | true
      | just σ′ | [ g₁ ]ⁱ rewrite C-mono⟦ c₁ ⟧ i j (<′⇨≤′ i<′j) σ σ′ g₁ = h′
    helper⟦ if b c₁ c₂ ⟧ () | true
      | nothing | [ g₁ ]ⁱ
    helper⟦ if b c₁ c₂ ⟧ h′ | false
      with C i ⟦ c₂ ⟧ σ | inspect (C i ⟦ c₂ ⟧) σ
    helper⟦ if b c₁ c₂ ⟧ h′ | false
      | just σ′ | [ g₂ ]ⁱ rewrite C-mono⟦ c₂ ⟧ i j (<′⇨≤′ i<′j) σ σ′ g₂ = h′
    helper⟦ if b c₁ c₂ ⟧ () | false
      | nothing | [ g₂ ]ⁱ

    helper⟦ while b c ⟧ h′ with B⟦ b ⟧ σ
    helper⟦ while b c ⟧ h′ | true
      with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
    helper⟦ while b c ⟧ h′ | true
      | just σ′ | [ g ]ⁱ rewrite C-mono⟦ c ⟧ i j (<′⇨≤′ i<′j) σ σ′ g
      = C-mono⟦ while b c ⟧ i j (<′⇨≤′ i<′j) σ′ σ′′ h′
    helper⟦ while b c' ⟧ () | true
      | nothing | [ g ]ⁱ
    helper⟦ while b c ⟧ h′ | false = h′

  -- C⇒⇩

  C⇒⇩_⟦_⟧ : (i : ℕ) (c : Cmd) (σ σ′ : State) →
    C i ⟦ c ⟧ σ ≡ just σ′ → c / σ ⇩ σ′

  C⇒⇩ zero ⟦ c ⟧ σ σ′ ()

  C⇒⇩ suc i ⟦ skip ⟧ .σ′ σ′ refl = ⇩-skip

  C⇒⇩ suc i ⟦ assign v a ⟧ σ .(update σ v (A⟦ a ⟧ σ )) refl = ⇩-assign

  C⇒⇩ suc i ⟦ seq c₁ c₂ ⟧ σ σ′′ h
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C⇒⇩ suc i ⟦ seq c₁ c₂ ⟧ σ σ′′ h
    | just σ′ | [ g ]ⁱ
    = ⇩-seq (C⇒⇩ i ⟦ c₁ ⟧ σ σ′ g) (C⇒⇩ i ⟦ c₂ ⟧ σ′ σ′′ h)
  C⇒⇩ suc i ⟦ seq c₁ c₂ ⟧ σ σ′′ () | nothing | [ g ]ⁱ

  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ h
    with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ 
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ h | true | [ f ]ⁱ
    | just σ′ | [ g₁ ]ⁱ
    = ⇩-if-true f (C⇒⇩ i ⟦ c₁ ⟧ σ σ′′ (trans g₁ h))
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ () | true | [ f ]ⁱ
    | nothing | [ g₁ ]ⁱ
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ h | false | [ f ]ⁱ
    with C i ⟦ c₂ ⟧ σ | inspect (C i ⟦ c₂ ⟧) σ
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ h | false | [ f ]ⁱ
    | just σ′ | [ g₂ ]ⁱ
    = ⇩-if-false f (C⇒⇩ i ⟦ c₂ ⟧ σ σ′′ (trans g₂ h))
  C⇒⇩ suc i ⟦ if b c₁ c₂ ⟧ σ σ′′ () | false | [ f ]ⁱ
    | nothing | [ g₂ ]ⁱ

  C⇒⇩ suc i ⟦ while b c ⟧ σ σ′′ h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ suc i ⟦ while b c ⟧ σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
  C⇒⇩ suc i ⟦ while b c ⟧ σ σ′′ h | true | [ f ]ⁱ
    | just σ′ | [ g ]ⁱ
    = ⇩-while-true f (C⇒⇩ i ⟦ c ⟧ σ σ′ g) (C⇒⇩ i ⟦ while b c ⟧ σ′ σ′′ h)
  C⇒⇩ suc i ⟦ while b c ⟧ σ σ′′ () | true | [ f ]ⁱ
    | nothing | [ g ]ⁱ
  C⇒⇩ suc i ⟦ while b c ⟧ .σ′′ σ′′ refl | false | [ f ]ⁱ =
    ⇩-while-false f

  -- ⇩⇒C

  ⇩⇒C⟦_⟧ : (c : Cmd) (σ σ′ : State) →
      c / σ ⇩ σ′ → ∃ λ i → C i ⟦ c ⟧ σ ≡ just σ′

  ⇩⇒C⟦ skip ⟧ .σ′ σ′ ⇩-skip =
    suc zero , refl

  ⇩⇒C⟦ assign v a ⟧ σ .(update σ v (A⟦ a ⟧ σ)) ⇩-assign =
    suc zero , refl

  ⇩⇒C⟦ seq c₁ c₂ ⟧ σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂)
    with ⇩⇒C⟦ c₁ ⟧ σ σ′ h₁ | ⇩⇒C⟦ c₂ ⟧ σ′ σ′′ h₂
  ⇩⇒C⟦ seq c₁ c₂ ⟧ σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂)
    | i₁ , g₁ | i₂ , g₂
    = suc (i₁ ⊔ i₂) , (
      begin
        (C i₁ ⊔ i₂ ⟦ c₁ ⟧ σ >>= C i₁ ⊔ i₂ ⟦ c₂ ⟧)
          ≡⟨ cong (λ e → e >>= C i₁ ⊔ i₂ ⟦ c₂ ⟧)
                  (C-mono⟦ c₁ ⟧ i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) σ σ′ g₁) ⟩
        C i₁ ⊔ i₂ ⟦ c₂ ⟧ σ′
          ≡⟨ C-mono⟦ c₂ ⟧ i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) σ′ σ′′ g₂ ⟩
        just σ′′
      ∎)

  ⇩⇒C⟦ if b c₁ c₂ ⟧ σ σ′′ (⇩-if-true b≡t h) with ⇩⇒C⟦ c₁ ⟧ σ σ′′ h
  ... | i₁ , g₁ = suc i₁ , trans (cong (λ e → C i₁ ⟦If⟧ e c₁ c₂ σ) b≡t) g₁
  ⇩⇒C⟦ if b c₁ c₂ ⟧ σ σ′′ (⇩-if-false b≡f h) with ⇩⇒C⟦ c₂ ⟧ σ σ′′ h
  ... | i₂ , g₂ = suc i₂ , trans (cong (λ e → C i₂ ⟦If⟧ e c₁ c₂ σ) b≡f) g₂

  ⇩⇒C⟦ while b c ⟧ σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂)
    with ⇩⇒C⟦ c ⟧ σ σ′ h₁ | ⇩⇒C⟦ while b c ⟧ σ′ σ′′ h₂
  ⇩⇒C⟦ while b c ⟧ σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂)
    | i₁ , g₁ | i₂ , g₂
    = (suc (i₁ ⊔ i₂)) , (
      begin
        C i₁ ⊔ i₂ ⟦While⟧ (B⟦ b ⟧ σ) b c σ
          ≡⟨ cong (λ e → C i₁ ⊔ i₂ ⟦While⟧ e b c σ) b≡t ⟩
        (C i₁ ⊔ i₂ ⟦ c ⟧ σ >>= C i₁ ⊔ i₂ ⟦ while b c ⟧)
          ≡⟨ cong (λ e → e >>= C i₁ ⊔ i₂ ⟦ while b c ⟧)
                  (C-mono⟦ c ⟧ i₁ (i₁ ⊔ i₂) (≤⇒≤′ (m≤m⊔n i₁ i₂)) σ σ′ g₁) ⟩
        C i₁ ⊔ i₂ ⟦ while b c ⟧ σ′
          ≡⟨ C-mono⟦ while b c ⟧ i₂ (i₁ ⊔ i₂) (≤⇒≤′ (n≤m⊔n i₁ i₂)) σ′ σ′′ g₂ ⟩
        just σ′′
      ∎)
  ⇩⇒C⟦ while b c ⟧ .σ′′ σ′′ (⇩-while-false b≡f) =
    suc zero , (cong (λ e → C zero ⟦While⟧ e b c σ′′) b≡f)

--
