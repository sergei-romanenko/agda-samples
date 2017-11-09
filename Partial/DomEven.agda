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

  -- No calls to `f` are unfolded. Hence, `f 2` won't reduce to 2.

  f2≡f2 : f 2 ≡ f 2
  f2≡f2 = refl

  -- The following theorem is "true", in a sense.
  -- But what is the sense? :-)

  f1≡f1 : f 1 ≡ f 1
  f1≡f1 = refl

module f-bad2 where

  {-# TERMINATING #-}
  f : ℕ → ℕ
  f zero = zero
  f (suc zero) = ω
  f (suc (suc n)) = suc (suc (f n))

  -- Now calls to `f` are unfolded. Hence, `f 2` reduces to 2.

  f2≡f2 : f 2 ≡ 2
  f2≡f2 = refl

  -- However, if we try to normalize f 1, the Agda compiler will go
  -- into an infinite loop!
  -- Because we make Agda belive that the function is total, while it is not!

  -- f1≡f1 : f 1 ≡ f 1
  -- f1≡f1 = refl

module f-good where

  -- Now we specify the domain of `f` following Bove & Capretta's technique.
  -- The left-hand sides of the function definition go to the right, while
  -- the function calls go to the left.
  -- Note that this is a formal procedure, so that no inventiveness
  -- is required.

  data F : ℕ → Set where
    a0 : F zero
    a2 : ∀ {n} (fn⇓ : F n) → F (suc (suc n))

  f : (n : ℕ) (fn⇓ : F n) → ℕ
  f zero a0 = zero
  f (suc zero) ()
  f (suc (suc n)) (a2 fn⇓) = suc (suc (f n fn⇓))

  f4⇓ : F 4
  f4⇓ = a2 (a2 a0)

  f4≡4 : f 4 f4⇓ ≡ 4
  f4≡4 = refl

  -- We can prove theorems about partial functions.

  fn≡n : (n : ℕ) (fn⇓ : F n) → f n fn⇓ ≡ n
  fn≡n zero a0 = refl
  fn≡n (suc zero) ()
  fn≡n (suc (suc n)) (a2 fn⇓) =
    cong (suc ∘ suc) (fn≡n n fn⇓)

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
      a0 : F zero
      a1 : ∀ {n} (gn⇓ : G n) → F (suc n)

    data G : ℕ → Set where
      b1 : ∀ {n} (fn⇓ : F n) → G (suc n)

  mutual

    f : (n : ℕ) (fn⇓ : F n) → ℕ
    f zero a0 = zero
    f (suc n) (a1 gn⇓) = suc (g n gn⇓)

    g : (n : ℕ) (gn⇓ : G n) → ℕ
    g zero ()
    g (suc n) (b1 fn⇓) = suc (f n fn⇓)

    f4⇓ : F 4
    f4⇓ = a1 (b1 (a1 (b1 a0)))

    f4≡4 : f 4 f4⇓ ≡ 4
    f4≡4 = refl

  mutual

    fn≡n : (n : ℕ) (fn⇓ : F n) → f n fn⇓ ≡ n
    fn≡n zero a0 = refl
    fn≡n (suc n) (a1 gn⇓) = cong suc (gn≡n n gn⇓)

    gn≡n : (n : ℕ) (gn⇓ : G n) → g n gn⇓ ≡ n
    gn≡n zero ()
    gn≡n (suc n) (b1 fn⇓) = cong suc (fn≡n n fn⇓)
