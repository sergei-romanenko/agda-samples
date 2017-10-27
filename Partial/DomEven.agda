module Partial.DomEven where

open import Data.Nat.Base

open import Function
  using (_∘_)

open import Relation.Binary.PropositionalEquality

{-# NON_TERMINATING #-}
ω : ℕ
ω = ω

module f-bad where

  {-# NON_TERMINATING #-}
  f : ℕ → ℕ
  f zero = zero
  f (suc zero) = ω
  f (suc (suc n)) = suc (suc (f n))

module f-good where

  -- Now we specify the domain of `f` following Bove & Capretta's technique.
  -- The left-hand sides of the function definition go to the right, while
  -- the function calls go to the left.
  -- Note that this is a formal procedure, so that no inventiveness
  -- is required.

  data F : ℕ → Set where
    d0 : F zero
    d2 : ∀ {n} → F n → F (suc (suc n))

  f : (n : ℕ) (h : F n) → ℕ
  f zero d0 = zero
  f (suc zero) ()
  f (suc (suc n)) (d2 h) = suc (suc (f n h))

  hf4 : F 4
  hf4 = d2 (d2 d0)

  f4≡4 : f 4 hf4 ≡ 4
  f4≡4 = refl

  -- We can prove theorems about partial functions.

  f-id : (n : ℕ) (h : F n) → f n h ≡ n
  f-id zero d0 = refl
  f-id (suc zero) ()
  f-id (suc (suc n)) (d2 h) =
    cong (suc ∘ suc) (f-id n h)

module fg-bad where

  {-# NON_TERMINATING #-}
  mutual

    f : ℕ → ℕ
    f zero = zero
    f (suc n) = suc (g n)

    g : ℕ → ℕ
    g zero = ω
    g (suc n) = suc (f n)

module fg-good where

  -- Here, using Bove & Capretta's technique, we have to specify
  -- the domains of two mutually recursive functions, by using
  -- two mutually recursive data type definitions.

  mutual

    data F : ℕ → Set where
      f0 : F zero
      f1 : ∀ {n} (h : G n) → F (suc n)

    data G : ℕ → Set where
      g1 : ∀ {n} (h : F n) → G (suc n)

  mutual

    f : (n : ℕ) (h : F n) → ℕ
    f zero f0 = zero
    f (suc n) (f1 h) = suc (g n h)

    g : (n : ℕ) (h : G n) → ℕ
    g zero ()
    g (suc n) (g1 h) = suc (f n h)

    hf4 : F 4
    hf4 = f1 (g1 (f1 (g1 f0)))

    f4≡4 : f 4 hf4 ≡ 4
    f4≡4 = refl

  mutual

    f-id : (n : ℕ) (h : F n) → f n h ≡ n
    f-id zero f0 = refl
    f-id (suc n) (f1 h) = cong suc (g-id n h)

    g-id : (n : ℕ) (h : G n) → g n h ≡ n
    g-id zero ()
    g-id (suc n) (g1 h) = cong suc (f-id n h)
