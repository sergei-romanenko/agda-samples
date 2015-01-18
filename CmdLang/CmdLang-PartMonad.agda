{-# OPTIONS --copatterns #-}

{-
See the paper

* Andreas Abel and James Chapman. 2014.
  Normalization by Evaluation in the Delay Monad:
  A Case Study for Coinduction via Copatterns and Sized Types.
  (MSFP 2014). http://arxiv.org/abs/1406.2059
-}

module CmdLang-PartMonad where

open import Level
  using (Level) renaming (zero to lzero; suc to lsuc)

open import Size

open import Category.Monad
  using (RawMonad; module RawMonad)

open import Data.Product
  using (∃; ∃₂; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty

open import Relation.Nullary
open import Relation.Nullary.Negation
  using (¬¬-Monad; excluded-middle)

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
    later a∞ >>= f = later (a∞ ∞>>= f)

    _∞>>=_ : ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a∞ ∞>>= f)  =  force a∞ >>= f

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
    _⇓_ {i} (now a) a
  later⇓ : ∀ {j : Size< i} {a} {a∞ : ∞Delay ∞ A} → _⇓_ {j} {A} (force a∞) a →
    later a∞ ⇓ a

_⇓⟨_⟩_ = λ {A} a? i a → _⇓_ {i} {A} a? a 

_⇓⟨_⟩ = λ {A} a? i → ∃ λ a → _⇓_ {i} {A} a? a

_⇓ =  λ {A} a? → ∃ λ a → _⇓_ {∞} {A} a? a


-- map⇓

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A} (f : A → B) →
  a? ⇓ a → (f <$> a?) ⇓ f a

map⇓ f now⇓ = now⇓
map⇓ f (later⇓ h) = later⇓ (map⇓ f h)

-- bind⇓

bind⇓ : ∀ {i} {A B} (f : A → Delay ∞ B) {a? : Delay ∞ A} {a : A} {b : B} →
  a? ⇓⟨ i ⟩ a →  f a ⇓ b → (a? >>= f) ⇓ b

bind⇓ {i} f now⇓ h₂ = h₂
bind⇓ {i} f (later⇓ {j} h₁) h₂ =
  later⇓ (bind⇓ {j} f h₁ h₂)

-- bind⇓-inv

bind⇓-inv : ∀ {A B} (i : Size) (f : A → Delay ∞ B)
  {a? : Delay ∞ A} {b : B} →
  (a? >>= f) ⇓⟨ i ⟩ b →
  ∃ λ (a : A) → a? ⇓⟨ i ⟩ a × f a ⇓⟨ i ⟩ b

bind⇓-inv i f {now a} h = a , now⇓ , h
bind⇓-inv i f {later a?} (later⇓ {j} h) =
  let a , ⇓a , ⇓b =  bind⇓-inv j f {force a?} h
  in a , later⇓ ⇓a , ⇓b

-- ⇓bind

⇓bind : ∀ {A B} (f : A → Delay ∞ B)
  {?a : Delay ∞ A} {a : A} → ?a ⇓ a →
  {b : B} → (?a >>= f) ⇓ b → f a ⇓ b
⇓bind f now⇓ q = q
⇓bind f (later⇓ p) (later⇓ q) = ⇓bind f p q


-- _⇑_

mutual

  data _⇑ {i : Size} {A : Set} : (a? : Delay ∞ A) → Set where
    later⇑ : ∀ {a∞ : ∞Delay ∞ A} → _∞⇑ {i} {A} a∞ →
      _⇑ {i} (later a∞)

  record _∞⇑ {i : Size} {A : Set} (a∞ : ∞Delay ∞ A) : Set where
    coinductive
    field
      ⇑force : {j : Size< i} → _⇑ {j} {A} (force a∞)

open _∞⇑ public

_⇑⟨_⟩ = λ {A} a? i → _⇑ {i} {A} a? 

_∞⇑⟨_⟩ = λ {A} a∞ i → _∞⇑ {i} {A} a∞ 

-- never∞⇑

never∞⇑ : {A : Set} → never {∞} {A} ∞⇑

⇑force never∞⇑ {j} = later⇑ never∞⇑


-- map⇑

mutual

  map⇑ : ∀ {A B} (f : A → B) {a? : Delay ∞ A} →
    a? ⇑ → (f <$> a?) ⇑

  map⇑ f (later⇑ {a∞} h) = later⇑ (∞map⇑ f h)

  ∞map⇑ : ∀ {A B} (f : A → B) {a∞ : ∞Delay ∞ A} →
    a∞ ∞⇑ → (a∞ ∞>>= (λ a → return (f a)) ) ∞⇑

  ⇑force (∞map⇑ f h) = map⇑ f (⇑force h)

-- bind⇑₁

mutual

  bind⇑₁ : ∀ {i : Size} {A B} (f : A → Delay ∞ B) {a? : Delay ∞ A} →
    a? ⇑⟨ i ⟩ → (a? >>= f) ⇑⟨ i ⟩

  bind⇑₁ f (later⇑ h) = later⇑ (∞bind⇑₁ f h)

  ∞bind⇑₁ : ∀ {i : Size} {A B} (f : A → Delay ∞ B) {a∞ : ∞Delay ∞ A} →
    a∞ ∞⇑⟨ i ⟩ → (a∞ ∞>>= f) ∞⇑⟨ i ⟩

  ⇑force (∞bind⇑₁ f h) = bind⇑₁ f (⇑force h)


-- bind⇑₂

mutual

  bind⇑₂ : ∀ {i : Size} {A B} (f : A → Delay ∞ B) {a? : Delay ∞ A} {a : A} →
    a? ⇓ a → f a ⇑⟨ i ⟩ → (a? >>= f) ⇑⟨ i ⟩

  bind⇑₂ f (now⇓ {a}) h⇧ = h⇧
  bind⇑₂ f (later⇓ h⇩) h⇧ = later⇑ (∞bind⇑₂ f h⇩ h⇧)

  ∞bind⇑₂ : ∀ {i : Size} {A B} (f : A → Delay ∞ B) {a∞ : ∞Delay ∞ A} {a : A} →
    force a∞ ⇓ a → f a ⇑⟨ i ⟩ → (a∞ ∞>>= f) ∞⇑⟨ i ⟩

  ⇑force (∞bind⇑₂ f h⇩ h⇧) = bind⇑₂ f h⇩ h⇧

⇑bind₂ : ∀ {A B}
  (f : A → Delay ∞ B) {a? : Delay ∞ A} {a : A} →
  a? ⇓ a → (a? >>= f) ⇑ → f a ⇑
⇑bind₂ f {now a} now⇓ h⇑ = h⇑
⇑bind₂ f {later a∞} (later⇓ ⇓a) (later⇑ h∞⇑) =
  ⇑bind₂ f {force a∞} ⇓a (⇑force h∞⇑)

mutual

  not-⇓-implies-⇑ : ∀ {A} {a? : Delay ∞ A} →
    ¬ a? ⇓ → a? ⇑
  not-⇓-implies-⇑ {a? = a?} ¬h⇓ with a?
  not-⇓-implies-⇑ ¬h⇓ | now a = ⊥-elim (¬h⇓ (a , now⇓))
  not-⇓-implies-⇑ ¬h⇓ | later a∞ =
    later⇑ (∞not-⇓-implies-⇑ ¬h⇓)

  ∞not-⇓-implies-⇑ : ∀ {A} {a∞ : ∞Delay ∞ A} →
    ¬ later a∞ ⇓⟨ ∞ ⟩ → a∞ ∞⇑
  ⇑force (∞not-⇓-implies-⇑ ¬h⇓) {j} =
    not-⇓-implies-⇑ (λ { (a , h⇓) → ¬h⇓ (a , later⇓ h⇓)} )

-- ⇓ or ⇑ (classically).

mutual

  ⇓-or-⇑ :
    ∀ {A} {a? : Delay ∞ A} → ¬ ¬ (a? ⇓ ⊎ a? ⇑)
  ⇓-or-⇑ {A} {a?} =
    helper |$| excluded-middle
    where
    open RawMonad ¬¬-Monad using () renaming (_<$>_ to _|$|_)
     -- _|$|_ : (A → B) → ¬ ¬ A → ¬ ¬ B

    helper : Dec (a? ⇓) → a? ⇓ ⊎ a? ⇑
    helper (yes h⇓) = inj₁ h⇓
    helper (no ¬h⇓) = inj₂ (not-⇓-implies-⇑ ¬h⇓)

--
