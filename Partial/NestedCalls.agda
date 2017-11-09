module Partial.NestedCalls where

open import Data.Nat

open import Function
  using (_∘_)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module ff-bad where

  -- Here the function `f` is total, but Agda is unable to prove it.
  -- So we just postulate the totality by means of a pragma.

  {-# TERMINATING #-}

  f : ℕ → ℕ
  f zero = zero
  f (suc zero) = suc zero
  f (suc (suc n)) = suc (suc (f (f n)))

  f5≡5 : f 5 ≡ 5
  f5≡5 = refl

  -- This proof is not completely formal, since it uses the totality of `f` that
  -- has been just postulated.

  fn≡n : ∀ n → f n ≡ n
  fn≡n zero = refl
  fn≡n (suc zero) = refl
  fn≡n (suc (suc n)) = cong (suc ∘ suc) (
    f (f n)
      ≡⟨ cong f (fn≡n n) ⟩
    f n
      ≡⟨ fn≡n n ⟩
    n ∎)

mutual

  -- Now we specify the domain of `f` by using Bove & Capretta's technique.
  -- Note that we have to define `F` and `f` simultaneously,
  -- because the definition of `f` contains a nested function call: f(f n).

  data F : (n : ℕ) → Set where
    a0 : F zero
    a1 : F (suc zero)
    a2 : ∀ {n} (fn⇓ : F n) (ffn⇓ : F (f n fn⇓)) →
      F (suc (suc n))

  f : (n : ℕ) (fn⇓ : F n) → ℕ
  f zero a0 = zero
  f (suc zero) a1 = suc zero
  f (suc (suc n)) (a2 fn⇓ ffn⇓) =
    suc (suc (f (f n fn⇓) ffn⇓))

-- OK. Now we can prove some theorems about `f` without postulating its totality.
-- The trick is that the theorems say "the statement is true on condition
-- that the argument belongs to the function's domain.

f5⇓ : F 5
f5⇓ = a2 (a2 a1 a1) (a2 a1 a1)

f5≡5 : f 5 f5⇓ ≡ 5
f5≡5 = refl

fn≡n : ∀ n → (fn⇓ : F n) → f n fn⇓ ≡ n
fn≡n zero a0 = refl
fn≡n (suc zero) a1 = refl
fn≡n (suc (suc n)) (a2 fn⇓ ffn⇓) = cong (suc ∘ suc) (
  f (f n fn⇓) ffn⇓
    ≡⟨ fn≡n (f n fn⇓) ffn⇓ ⟩
  f n fn⇓
    ≡⟨ fn≡n n fn⇓ ⟩
  n ∎)

-- However, we can (formally) prove that the function is total!

all-f : ∀ n → F n
all-f zero = a0
all-f (suc zero) = a1
all-f (suc (suc n)) = a2 fn⇓ ffn⇓ where
  fn⇓ : F n
  fn⇓ = all-f n
  ffn⇓ : F (f n fn⇓)
  ffn⇓ rewrite fn≡n n fn⇓ = fn⇓

-- And now we can wright down a "normal" definition of `f` that
-- does not take an additional argument.

total-f : ℕ → ℕ
total-f n = f n (all-f n)

-- And we can prove some theorems about `total-f`.
-- (Without specifying the domain of `f`.)

tf5≡0 : total-f 5 ≡ 5
tf5≡0 = refl

tfn≡0 : ∀ n → total-f n ≡ n
tfn≡0 n = fn≡n n (all-f n)
