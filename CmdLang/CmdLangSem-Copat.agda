{-# OPTIONS --copatterns #-}

{-
This solution (based on sized types and copatterns) is inspired by the paper

* Andreas Abel and James Chapman. 2014.
  Normalization by Evaluation in the Delay Monad:
  A Case Study for Coinduction via Copatterns and Sized Types.
  (MSFP 2014). http://arxiv.org/abs/1406.2059

and is drastically simpler than the stuff in CmdLangSem-Coind.
-}

module CmdLangSem-Copat where

open import Size

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Empty

open import Function

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

import Function.Related as Related

open import CmdLang
open import CmdLang-PartMonad

record CmdLangSem (memory : Memory) (absCmdLang : AbsCmdLang memory) : Set₁
  where
  open Memory memory
  open AbsCmdLang absCmdLang

  -- C⟦_⟧

  mutual

    C⟦_⟧ : ∀ {i} (c : Cmd) (σ : State) → Delay i State

    C⟦ skip ⟧ σ =
      return σ

    C⟦ assign v a ⟧ σ =
      return (update σ v (A⟦ a ⟧ σ))

    C⟦ seq c₁ c₂ ⟧ σ =
      C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧

    {-
    C⟦ if b c₁ c₂ ⟧ σ with B⟦ b ⟧ σ
    ... | true =  C⟦ c₁ ⟧ σ
    ... | false = C⟦ c₂ ⟧ σ
    -}
    C⟦ if b c₁ c₂ ⟧ σ =
      C⟦if⟧ (B⟦ b ⟧ σ) c₁ c₂ σ

    C⟦ while b c ⟧ σ with B⟦ b ⟧ σ
    ... | true  = later (∞seq c (while b c) σ)
    ... | false = return σ

    C⟦if⟧ : ∀ {i} (b : Bool ) (c₁ c₂ : Cmd) (σ : State) → Delay i State
    C⟦if⟧ true c₁ c₂ σ = C⟦ c₁ ⟧ σ
    C⟦if⟧ false c₁ c₂ σ = C⟦ c₂ ⟧ σ

    ∞seq : ∀ {i} (c₁ c₂ : Cmd) (σ : State) → ∞Delay i State
    force (∞seq c₁ c₂ σ) =
      C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧

  --
  -- Correctness
  --

  --
  -- C⇒⇩
  --

  C⇒⇩ : (i : Size) (c : Cmd) {σ σ′ : State} →
    C⟦ c ⟧ σ ⇓⟨ i ⟩ σ′ → c / σ ⇩ σ′

  C⇒⇩ i skip now⇓ =
    ⇩-skip

  C⇒⇩ i (assign v a) now⇓ =
    ⇩-assign

  C⇒⇩ i (seq c₁ c₂) h =
    let σ′ , h₁ , h₂ = bind⇓-inv i C⟦ c₂ ⟧ h
    in ⇩-seq (C⇒⇩ i c₁ h₁) (C⇒⇩ i c₂ h₂)

  C⇒⇩ i (if b c₁ c₂) {σ} h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ i (if b c₁ c₂) h | true  | ≡[ b≡t ] =
    ⇩-if-true b≡t (C⇒⇩ i c₁ h)
  C⇒⇩ i (if b c₁ c₂) h | false | ≡[ b≡f ] =
    ⇩-if-false b≡f (C⇒⇩ i c₂ h)

  C⇒⇩ i (while b c) {σ} h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ i (while b c) (later⇓ {j} h) | true | ≡[ b≡t ] =
    let σ′ , h₁ , h₂ = bind⇓-inv j C⟦ while b c ⟧ h
    in ⇩-while-true b≡t (C⇒⇩ i c h₁) (C⇒⇩ j (while b c) h₂)
  C⇒⇩ i (while b c) now⇓ | false | ≡[ b≡f ] =
    ⇩-while-false b≡f

  --
  -- ⇩⇒C
  --

  ⇩⇒C : {c : Cmd} {σ σ′ : State} →
      c / σ ⇩ σ′ → C⟦ c ⟧ σ ⇓ σ′

  ⇩⇒C ⇩-skip =
    now⇓

  ⇩⇒C ⇩-assign =
    now⇓

  ⇩⇒C {seq c₁ c₂} (⇩-seq {σ} {σ′} {σ′′} h₁ h₂) =
    --bind⇓ C⟦ c₂ ⟧ (⇩⇒C h₁) (⇩⇒C h₂)
    c₂ / σ′ ⇩ σ′′
      ∼⟨ ⇩⇒C ⟩
    C⟦ c₂ ⟧ σ′ ⇓ σ′′
      ∼⟨ bind⇓ _ {-C⟦ c₂ ⟧-} (⇩⇒C h₁) ⟩
    (C⟦ c₁ ⟧ σ >>= C⟦ c₂ ⟧) ⇓ σ′′
    ∎ $ h₂
    where open Related.EquationalReasoning

  {-
  ⇩⇒C (⇩-if-true b≡t h) rewrite b≡t =
    ⇩⇒C h
  -}
  ⇩⇒C (⇩-if-true {σ} {σ′} {b} {c₁} {c₂} b≡t h) =
    C⟦ c₁ ⟧ σ ⇓ σ′
      ≡⟨ refl ⟩
    C⟦if⟧ true c₁ c₂ σ ⇓ σ′
      ≡⟨ cong (λ b → C⟦if⟧ b c₁ c₂ σ ⇓ σ′) (P.sym $ b≡t) ⟩
    C⟦if⟧ (B⟦ b ⟧ σ) c₁ c₂ σ ⇓ σ′
      ≡⟨ refl ⟩
    C⟦ if b c₁ c₂ ⟧ σ ⇓ σ′
    ∎ $ ⇩⇒C h
    where open Related.EquationalReasoning

  ⇩⇒C (⇩-if-false b≡f h) rewrite b≡f =
    ⇩⇒C h

  ⇩⇒C {while b c} (⇩-while-true b≡t h₁ h₂) rewrite b≡t =
    later⇓ (bind⇓ C⟦ while b c ⟧ (⇩⇒C h₁) (⇩⇒C h₂))

  ⇩⇒C (⇩-while-false b≡f) rewrite b≡f =
    now⇓


  --
  -- Divergence
  --

  steps : {A : Set} {a? : Delay ∞ A} {a : A} → a? ⇓ a → ℕ
  steps now⇓ = zero
  steps (later⇓ a⇓) = suc (steps a⇓)

  steps⇩ : {c : Cmd} {σ σ′ : State} → c / σ ⇩ σ′ → ℕ
  steps⇩ ⇩-skip = zero
  steps⇩ ⇩-assign = zero
  steps⇩ (⇩-seq ⇩σ′′ ⇩σ′) = steps⇩ ⇩σ′′ + steps⇩ ⇩σ′
  steps⇩ (⇩-if-true b≡t ⇩σ′) = steps⇩ ⇩σ′
  steps⇩ (⇩-if-false b≡f ⇩σ′) = steps⇩ ⇩σ′
  steps⇩ (⇩-while-true b≡t ⇩σ′′ ⇩σ′) = suc (steps⇩ ⇩σ′′ + steps⇩ ⇩σ′)
  steps⇩ (⇩-while-false b≡f) = zero

  steps⇩≡steps :{c : Cmd} {σ σ′ : State} (h⇩ : c / σ ⇩ σ′) →
    steps⇩ h⇩ ≡ steps (⇩⇒C h⇩)
  steps⇩≡steps ⇩-skip = refl
  steps⇩≡steps ⇩-assign = refl
  steps⇩≡steps (⇩-seq h⇩₁ h⇩₂) = {!!}
  steps⇩≡steps (⇩-if-true {σ} {σ′} {b} {c₁} {c₂} b≡t h⇩) rewrite b≡t =
    {!refl!}
  {-
  ... | true = {!!}
  ... | false = ?
  -}
  steps⇩≡steps (⇩-if-false b≡f h⇩) = {!!}
  steps⇩≡steps (⇩-while-true b≡t h⇩ h⇩₁) = {!!}
  steps⇩≡steps (⇩-while-false b≡f) = {!!}

  _+ˢ_ : ℕ → Size → Size
  zero +ˢ s = s
  suc n +ˢ s = ↑ (n +ˢ s)

  

  mutual

    {-
    data _/_⇧ {i : Size} : (c : Cmd) (σ : State) → Set where
      ⇧-seq₁ :
        ∀ {σ c₁ c₂} → c₁ / σ ⇧ → seq c₁ c₂ / σ ⇧
      ⇧-seq₂ :
        ∀ {σ σ′ c₁ c₂} → c₁ / σ ⇩ σ′ → c₂ / σ′ ⇧ → seq c₁ c₂ / σ ⇧
      ⇧-if-true :
        ∀ {σ b c₁ c₂} → (b≡t : B⟦ b ⟧ σ ≡ true) →
          c₁ / σ ⇧⟨ i ⟩ → if b c₁ c₂ / σ ⇧
      ⇧-if-false :
        ∀ {σ b c₁ c₂} → (b≡f : B⟦ b ⟧ σ ≡ false) →
          c₂ / σ ⇧⟨ i ⟩ → if b c₁ c₂ / σ ⇧
      ⇧-while-true₁ :
        ∀ {σ b c} → (b≡t : B⟦ b ⟧ σ ≡ true) →
          c / σ ⇧⟨ i ⟩ → while b c / σ ⇧
      ⇧-while-true₂ :
        ∀ {σ σ′ b c} → (b≡t : B⟦ b ⟧ σ ≡ true) →
          c / σ ⇩ σ′ → while b c ∞/ σ′ ⇧ → while b c / σ ⇧
      -}
    data ⟨_⟩_/_⇧ : (i : Size) (c : Cmd) (σ : State) → Set where
      ⇧-seq₁ :
        ∀ {σ c₁ c₂} i → ⟨ i ⟩ c₁ / σ ⇧ → ⟨ i ⟩ seq c₁ c₂ / σ ⇧
      ⇧-seq₂ :
        ∀ {σ σ′ c₁ c₂} i → (c₁⇩ : c₁ / σ ⇩ σ′) → ⟨ i ⟩ c₂ / σ′ ⇧ →
          ⟨ i ⟩ seq c₁ c₂ / σ ⇧

--     record _∞/_⇧ {i : Size} (c : Cmd) (σ : State) : Set where
--       coinductive
--       field
--         ⇧force : {j : Size< i} → _/_⇧ {j} c σ

--     _/_⇧⟨_⟩ = λ c σ i  → _/_⇧ {i} c σ

--     _∞/_⇧⟨_⟩ = λ c σ i → _∞/_⇧ {i} c σ

--   open _∞/_⇧ public

--   --
--   -- ⇧⇒C
--   --

--   mutual

--     ⇧⇒C : {i : Size} {c : Cmd} {σ : State} →
--       c / σ ⇧⟨ i ⟩ → C⟦ c ⟧ σ ⇑⟨ i ⟩

--     ⇧⇒C {i} {seq c₁ c₂} (⇧-seq₁ h⇧) =
--       bind⇑₁ C⟦ c₂ ⟧ (⇧⇒C h⇧)

--     ⇧⇒C  {i} {seq c₁ c₂} (⇧-seq₂ h⇩ h⇧) =
--       bind⇑₂ C⟦ c₂ ⟧ (⇩⇒C h⇩) (⇧⇒C h⇧)

--     ⇧⇒C (⇧-if-true b≡t h⇧) rewrite b≡t =
--       ⇧⇒C h⇧

--     ⇧⇒C (⇧-if-false b≡f h⇧) rewrite b≡f =
--       ⇧⇒C h⇧

--     ⇧⇒C (⇧-while-true₁ b≡t h⇧) rewrite b≡t =
--       later⇑ (⇧⇒seq₁ h⇧)

--     ⇧⇒C (⇧-while-true₂ b≡t h⇩ h⇧) rewrite b≡t =
--       later⇑ (∞⇧⇒seq₂ h⇩ h⇧)

--     -- ⇧⇒seq₁

--     ⇧⇒seq₁ : {i : Size} {c₁ c₂ : Cmd} {σ : State} →
--       c₁ / σ ⇧⟨ i ⟩ → ∞seq c₁ c₂ σ ∞⇑⟨ i ⟩

--     ⇑force (⇧⇒seq₁ {c₂ = c₂} h⇧) =
--       bind⇑₁ C⟦ c₂ ⟧ (⇧⇒C h⇧)

--     -- ∞⇧⇒seq₂

--     ∞⇧⇒seq₂ : {i : Size} {c₁ c₂ : Cmd} {σ σ′ : State} →
--       c₁ / σ ⇩ σ′ → c₂ ∞/ σ′ ⇧⟨ i ⟩ → ∞seq c₁ c₂ σ ∞⇑⟨ i ⟩

--     ⇑force (∞⇧⇒seq₂ {c₂ = c₂} h⇩ h⇧) =
--       bind⇑₂ C⟦ c₂ ⟧ (⇩⇒C h⇩) (⇧⇒C (⇧force h⇧))


--   --
--   -- C⇒⇧
--   --

--   -- This is not a "fair", finished proof, as it contains a `postulate`.
--   -- There is a problem with sizes... Presently, there is no addition
--   -- for sizes, but we need to express the fact that
--   --     c / σ ⇩ σ′⟨ i ⟩  → while b c ∞/ σ′ ⇧⟨ j ⟩ → while b c / σ ⇧⟨ i + j ⟩

--   module C⇒⇧-em
--       (⇑⊎⇓ : ∀ {i : Size} {A} (a? : Delay ∞ A) → a? ⇑⟨ i ⟩ ⊎ ∃ λ a → a? ⇓ a)
--     where 

--     mutual

--       C⇒⇧ : (c : Cmd) (σ : State) →
--         C⟦ c ⟧ σ ⇑ → c / σ ⇧

--       C⇒⇧ skip σ ()

--       C⇒⇧ (assign v a) σ ()

--       C⇒⇧ (seq c₁ c₂) σ h with ⇑⊎⇓ (C⟦ c₁ ⟧ σ)
--       ... | inj₁ c₁⇑ =
--         ⇧-seq₁ (C⇒⇧ c₁ σ c₁⇑)
--       ... | inj₂ (σ′ , c₁⇓σ′) =
--         ⇧-seq₂ (C⇒⇩ ∞ c₁ c₁⇓σ′) (C⇒⇧ c₂ σ′ (⇑bind₂ C⟦ c₂ ⟧ c₁⇓σ′ h))

--       C⇒⇧ (if b c₁ c₂) σ h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
--       C⇒⇧ (if b c₁ c₂) σ h | true  | ≡[ b≡t ] =
--         ⇧-if-true b≡t (C⇒⇧ c₁ σ h)
--       C⇒⇧ (if b c₁ c₂) σ h | false | ≡[ b≡f ] =
--         ⇧-if-false b≡f (C⇒⇧ c₂ σ h)

--       C⇒⇧ (while b c) σ h  with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
--       C⇒⇧ (while b c) σ (later⇑ ∞seq∞⇑) | true | ≡[ b≡t ]
--         with ⇑⊎⇓ (C⟦ c ⟧ σ)
--       ... | inj₁ c⇑ =
--         ⇧-while-true₁ b≡t (C⇒⇧ c σ c⇑)
--       ... | inj₂ (σ′ , c⇓σ′) =
--         ⇧-while-true₂ b≡t
--           (C⇒⇩ ∞ c c⇓σ′)
--           (C⇒∞⇧ (while b c) σ′ (⇑bind₂ C⟦ while b c ⟧ c⇓σ′ (⇑force ∞seq∞⇑)))
--       C⇒⇧ (while b c) σ () | false | ≡[ b≡f ]

--       postulate
--         C⇒∞⇧ : {i : Size} (c : Cmd) (σ : State) →
--           C⟦ c ⟧ σ ⇑⟨ i ⟩ → c ∞/ σ ⇧⟨ i ⟩
--       --⇧force (C⇒∞⇧ c σ h⇑) {j} = C⇒⇧ c σ h⇑

-- --
