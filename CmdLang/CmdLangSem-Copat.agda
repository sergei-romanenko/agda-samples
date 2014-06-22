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

open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Product

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import CmdLang
open import CmdLang-PartMonad

record CmdLangSem (memory : Memory) (absCmdLang : AbsCmdLang memory) : Set₁
  where
  open Memory memory
  open AbsCmdLang absCmdLang

  -- C⟦_⟧

  C⟦_⟧ : ∀ {i} (c : Cmd) (σ : State) → Delay i State
  ♯cmd : ∀ {i} (c : Cmd) (σ : State) → ∞Delay i State
  ♯seq : ∀ {i} (c₁ c₂ : Cmd) (σ : State) → ∞Delay i State

  C⟦ skip ⟧ σ =
    return σ

  C⟦ assign v a ⟧ σ =
    return (update σ v (A⟦ a ⟧ σ))

  C⟦ seq c₁ c₂ ⟧ σ =
    later (♯seq c₁ c₂ σ)

  C⟦ if b c₁ c₂ ⟧ σ with B⟦ b ⟧ σ
  ... | true = later (♯cmd c₁ σ)
  ... | false = later (♯cmd c₂ σ)

  C⟦ while b c ⟧ σ with B⟦ b ⟧ σ
  ... | true = later (♯seq c (while b c) σ)
  ... | false = return σ

  force (♯cmd c σ) =
    C⟦ c ⟧ σ

  force (♯seq c₁ c₂ σ) =
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

  C⇒⇩ i (seq c₁ c₂) (later⇓ {j} h) =
    let σ′ , h₁ , h₂ = bind⇓-inv j C⟦ c₂ ⟧ h
    in ⇩-seq (C⇒⇩ j c₁ h₁) (C⇒⇩ j c₂ h₂)

  C⇒⇩ i (if b c₁ c₂) {σ} h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ i (if b c₁ c₂) (later⇓ {j} h) | true  | ≡[ b≡t ] =
    ⇩-if-true b≡t (C⇒⇩ j c₁ h)
  C⇒⇩ i (if b c₁ c₂) (later⇓ {j} h) | false | ≡[ b≡f ] =
    ⇩-if-false b≡f (C⇒⇩ j c₂ h)

  C⇒⇩ i (while b c) {σ} h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ i (while b c) (later⇓ {j} h) | true | ≡[ b≡t ] =
    let σ′ , h₁ , h₂ = bind⇓-inv j C⟦ while b c ⟧ h
    in ⇩-while-true b≡t (C⇒⇩ j c h₁) (C⇒⇩ j (while b c) h₂)
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

  ⇩⇒C {seq c₁ c₂} (⇩-seq h₁ h₂) =
    later⇓ (bind⇓ C⟦ c₂ ⟧ (⇩⇒C h₁) (⇩⇒C h₂))

  ⇩⇒C (⇩-if-true b≡t h) rewrite b≡t =
    later⇓ (⇩⇒C h)

  ⇩⇒C (⇩-if-false b≡f h) rewrite b≡f =
    later⇓ (⇩⇒C h)

  ⇩⇒C {while b c} (⇩-while-true b≡t h₁ h₂) rewrite b≡t =
    later⇓ (bind⇓ C⟦ while b c ⟧ (⇩⇒C h₁) (⇩⇒C h₂))

  ⇩⇒C (⇩-while-false b≡f) rewrite b≡f =
    now⇓

--
