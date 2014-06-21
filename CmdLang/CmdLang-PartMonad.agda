{-# OPTIONS --copatterns #-}

{-
See the paper

* Andreas Abel and James Chapman. 2014.
  Normalization by Evaluation in the Delay Monad:
  A Case Study for Coinduction via Copatterns and Sized Types.
  (MSFP 2014). http://arxiv.org/abs/1406.2059
-}

module CmdLang-PartMonad where

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Size public

open import Category.Monad public
  using (RawMonad; module RawMonad)

open import Data.Product public
  using (∃; ∃₂; _×_; _,_; proj₁; proj₂)

-- Delay & ∞Delay

mutual
  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

-- never

never : ∀{i A} → ∞Delay i A
force (never {i}) {j} = later (never {j})

-- Bind

module Bind where
  mutual
    _>>=_ :  ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   a  >>= f = f a
    later a♯ >>= f = later (a♯ ∞>>= f)

    _∞>>=_ : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a♯ ∞>>= f)  =  force a♯ >>= f

-- delayMonad

delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return  =  now
  ; _>>=_   =  _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

-- _⇓_

data _⇓_ {i : Size} {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} →
    now a ⇓ a
  later⇓ : ∀ {j : Size< i} {a} {♯a : ∞Delay ∞ A} → _⇓_ {j} {A} (force ♯a) a →
    later ♯a ⇓ a

_⇓⟨_⟩_ = λ {A} a? i a → _⇓_ {i} {A} a? a 

_⇓   :  {A : Set} (x : Delay ∞ A) → Set
x ⇓  =  ∃ λ a → x ⇓ a

-- map⇓

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A} (f : A → B) →
  a? ⇓ a → (f <$> a?) ⇓ f a

map⇓ f now⇓ = now⇓
map⇓ f (later⇓ h) = later⇓ (map⇓ f h)

-- bind⇓

bind⇓ : ∀ {A B} (f : A → Delay ∞ B) {?a : Delay ∞ A} {a : A} {b : B} →
  ?a ⇓ a → f a ⇓ b → (?a >>= f) ⇓ b

bind⇓ f now⇓ h₂ = h₂
bind⇓ f (later⇓ h₁) h₂ = later⇓ (bind⇓ f h₁ h₂)

-- bind⇓-inv

bind⇓-inv : ∀ {A B} (i : Size) (f : A → Delay ∞ B)
  {?a : Delay ∞ A} {b : B} →
  (?a >>= f) ⇓⟨ i ⟩ b →
  ∃ λ (a : A) → ?a ⇓⟨ i ⟩ a × f a ⇓⟨ i ⟩ b

bind⇓-inv i f {now a} h = a , now⇓ , h
bind⇓-inv i f {later ?a} (later⇓ {j} h) =
  let a , ⇓a , ⇓b =  bind⇓-inv j f {force ?a} h
  in a , later⇓ ⇓a , ⇓b

--
