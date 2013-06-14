module CmdLangSem-Coind where

open import Data.Bool
open import Data.Nat
open import Data.Product

open import Function

open import Data.Nat.Properties

open import Induction.WellFounded
open import Induction.Nat

open import Coinduction
open import Category.Monad
open import Category.Monad.Partiality as Partiality

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to [_]ⁱ)

open import CmdLang

--
-- CmdLangSem-Bad
-- Coinductive evaluation function
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
    later (♯ (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧))
  C⟦ if b c₁ c₂ ⟧ σ =
    C⟦If⟧ (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧ σ =
    C⟦While⟧ (B⟦ b ⟧ σ) b c σ

  C⟦If⟧ true c₁ c₂ σ =
    C⟦ c₁ ⟧ σ
  C⟦If⟧ false c₁ c₂ σ =
    C⟦ c₂ ⟧ σ

  C⟦While⟧ true b c σ =
    later (♯ (C⟦ c ⟧ σ >>= C⟦ while b c ⟧))
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
    later (♯ (C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′))
  C⟦ if b c₁ c₂ ⟧′ σ =
    C⟦If⟧′ (B⟦ b ⟧ σ) c₁ c₂ σ
  C⟦ while b c ⟧′ σ =
    C⟦While⟧′ (B⟦ b ⟧ σ) b c σ

  C⟦If⟧′ true c₁ c₂ σ =
    C⟦ c₁ ⟧′ σ
  C⟦If⟧′ false c₁ c₂ σ =
    C⟦ c₂ ⟧′ σ

  C⟦While⟧′ true b c σ =
    later (♯ (C⟦ c ⟧′ σ >>=′ C⟦ while b c ⟧′))
  C⟦While⟧′ false b c σ =
    return σ

  C⟦_⟧ : (c : Cmd) → (σ : State) → State ⊥
  C⟦ c ⟧ σ = ⟦ C⟦ c ⟧′ σ ⟧P

  --
  -- Correctness
  --

  private

    open module M{f} = RawMonad (Partiality.monad {f})

    open module PE {A : Set} = Partiality.Equality (_≡_ {A = A})

    open module PR {A : Set} =
      Partiality.Reasoning (P.isEquivalence {A = A})
      renaming (_∎ to _□)

    open Equivalence

  --
  -- C⇒⇩
  --

  C⇒⇩ : (c : Cmd) (σ σ′ : State) → C⟦ c ⟧ σ ≈ now σ′ → c / σ ⇩ σ′

  C⇒⇩′ : ∀ (c : Cmd) (σ σ′ : State) (h : C⟦ c ⟧ σ ≈ now σ′) →
              Acc _<′_ (steps h) → c / σ ⇩ σ′

  C⇒⇩′-seq : (c₁ c₂ : Cmd) → (σ σ′′ : State) →
             (h : C⟦ seq c₁ c₂ ⟧ σ ≈ now σ′′) →
             Acc _<′_ (steps h) →
             ∃ λ σ′ →
             ∃₂ λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
               steps h₁ <′ steps h × steps h₂ <′ steps h

  -- C⇒⇩ = ... 

  C⇒⇩ c σ σ′′ h = C⇒⇩′ c σ σ′′ h (<-well-founded (steps h))

  -- C⇒⇩′ = ...

  C⇒⇩′ skip σ σ′′ (now eq) a rewrite P.sym eq =
    ⇩-skip

  C⇒⇩′ (assign v e) σ σ′′ (now eq) a rewrite P.sym eq =
    ⇩-assign

  C⇒⇩′ (seq c₁ c₂) σ σ′′ (laterˡ h) (acc p)
    with C⇒⇩′-seq c₁ c₂ σ σ′′ (laterˡ h) (acc p)
  ... | σ′ , h₁ , h₂ , s₁<′ , s₂<′ =
    ⇩-seq (C⇒⇩′ c₁ σ σ′ h₁ (p (steps h₁) s₁<′))
          (C⇒⇩′ c₂ σ′ σ′′ h₂ (p (steps h₂) s₂<′))

  C⇒⇩′ (if b c₁ c₂) σ σ′′ h a with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  ... | true | [ b≡t ]ⁱ =
    ⇩-if-true b≡t (C⇒⇩′ c₁ σ σ′′ h a)
  ... | false | [ b≡f ]ⁱ =
    ⇩-if-false b≡f (C⇒⇩′ c₂ σ σ′′ h a)

  C⇒⇩′ (while b c) σ σ′′ h (acc p) with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ

  C⇒⇩′ (while b c) σ σ′′ (laterˡ h) (acc p) | true | [ b≡t ]ⁱ rewrite b≡t
    with C⇒⇩′-seq c (while b c) σ σ′′ (laterˡ h) (acc p)
  ... | σ′ , h₁ , h₂ , <′₁ , <′₂ =
    ⇩-while-true b≡t
      (C⇒⇩′ c σ σ′ h₁ (p (steps h₁) <′₁))
      (C⇒⇩′ (while b c) σ′ σ′′ h₂ (p (steps h₂) <′₂))
    
  C⇒⇩′ (while b c) σ σ′′ (now eq) (acc p) | false | [ b≡f ]ⁱ rewrite eq =
    ⇩-while-false b≡f

  -- C⇒⇩′-seq

  C⇒⇩′-seq c₁ c₂ σ σ′′ (laterˡ h) (acc p) =
    helper seq-inv
    where
      bind-hom : (C⟦ c₁ ⟧ σ >>= (λ σ′ → C⟦ c₂ ⟧ σ′)) ≅
                     ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
      bind-hom = PR.sym (Correct.>>=-hom (C⟦ c₁ ⟧′ σ) C⟦ c₂ ⟧′)

      seq-comp : (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧) ≈ now σ′′
      seq-comp = Equivalence.trans P.trans (≅⇒ bind-hom) h
      -- For some mysterious reason this "piece of reasoning" doesn't work!
      {-
      seq-comp =
        (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧)
          ≅⟨ bind-hom ⟩
        ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
          ≈⟨ h ⟩
        now σ′′
        □
      -}

      seq-inv : ∃ λ σ′ →
        ∃₂ λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
          steps h₁ + steps h₂ ≡ steps seq-comp
      seq-inv = >>=-inversion-⇓ P.refl (C⟦ c₁ ⟧ σ) seq-comp

      helper : ∃ (λ σ′ →
        ∃₂ (λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
                  steps h₁ + steps h₂ ≡ steps seq-comp)) →
             ∃ λ σ′ →
             ∃₂ λ (h₁ : C⟦ c₁ ⟧ σ ≈ now σ′) (h₂ : C⟦ c₂ ⟧ σ′ ≈ now σ′′) →
               steps h₁ <′ suc (steps h) × steps h₂ <′ suc (steps h)
      helper (σ′ , h₁ , h₂ , s+s≡s) = σ′ , h₁ , h₂ , s₁<′ , s₂<′
        where
          prop₀ : steps seq-comp ≡ steps h
          prop₀ = Steps.left-identity bind-hom h
          hhh : steps h₁ + steps h₂ ≡ steps h
          hhh = P.trans s+s≡s prop₀
          s₁<′ : steps h₁ <′ suc (steps h)
          s₁<′ = s≤′s (subst (λ e → steps h₁ ≤′ e) hhh
                             (m≤′m+n (steps h₁) (steps h₂)))
          s₂<′ : steps h₂ <′ suc (steps h)
          s₂<′ = s≤′s (subst (λ e → steps h₂ ≤′ e) hhh
                             (n≤′m+n (steps h₁) (steps h₂)))


  --
  -- ⇩⇒C
  --

  ⇩⇒C : (c : Cmd) (σ σ′ : State) →
      c / σ ⇩ σ′ → C⟦ c ⟧ σ ≈ now σ′

  ⇩⇒C⟦seq⟧ : (c₁ c₂ : Cmd) (σ σ′ σ′′ : State) →
      (h₁ : c₁ / σ ⇩ σ′) → (h₂ : c₂ / σ′ ⇩ σ′′) →
        C⟦ seq c₁ c₂ ⟧ σ ≈ now σ′′

  ⇩⇒C skip .σ′ σ′ ⇩-skip =
    now P.refl

  ⇩⇒C (assign v a) σ .(update σ v (A⟦ a ⟧ σ)) ⇩-assign =
    now P.refl

  ⇩⇒C (seq c₁ c₂) σ σ′′ (⇩-seq {σ′ = σ′} h₁ h₂) =
    ⇩⇒C⟦seq⟧ c₁ c₂ σ σ′ σ′′ h₁ h₂

  ⇩⇒C (if b c₁ c₂) σ σ′ (⇩-if-true b≡t h₁) rewrite b≡t =
    ⇩⇒C c₁ σ σ′ h₁
  ⇩⇒C (if b c₁ c₂) σ σ′ (⇩-if-false b≡f h₂) rewrite b≡f =
    ⇩⇒C c₂ σ σ′ h₂

  ⇩⇒C (while b c) σ σ′′ (⇩-while-true {σ′ = σ′} b≡t h₁ h₂) rewrite b≡t =
    ⇩⇒C⟦seq⟧ c (while b c) σ σ′ σ′′ h₁ h₂

  ⇩⇒C (while b c) .σ σ (⇩-while-false b≡f) rewrite b≡f =
    now P.refl

  -- ⇩⇒C⟦seq⟧

  ⟦seq⟧-cong : ∀ {k} {v₁ v₂ : State ⊥} {f : State → State ⊥} →
    Rel k v₁ v₂ → Rel k (v₁ >>= f) (v₂ >>= f)
  ⟦seq⟧-cong {f = f} v₁≈v₂ =
    v₁≈v₂ ≡->>=-cong (λ σ → f σ □)

  ⇩⇒C⟦seq⟧ c₁ c₂ σ σ′ σ′′ h₁ h₂ =
    C⟦ seq c₁ c₂ ⟧ σ
      ≅⟨ _ □ ⟩
    ⟦ later (♯ (C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′)) ⟧P
      ≅⟨ later (♯ (_ □)) ⟩
    later (♯ ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P )
      ≳⟨ laterˡ (_ □) ⟩
    ⟦ C⟦ c₁ ⟧′ σ >>=′ C⟦ c₂ ⟧′ ⟧P
      ≅⟨ Correct.>>=-hom (C⟦ c₁ ⟧′ σ) C⟦ c₂ ⟧′ ⟩
    (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧)
      ≈⟨ ⟦seq⟧-cong (⇩⇒C c₁ σ σ′ h₁) ⟩
    (now σ′ >>= C⟦ c₂ ⟧)
      ≅⟨ _ □ ⟩
    C⟦ c₂ ⟧ σ′
      ≈⟨ ⇩⇒C c₂ σ′ σ′′ h₂ ⟩
    now σ′′
    □

--
