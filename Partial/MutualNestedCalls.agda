module Partial.MutualNestedCalls where

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module fg-bad where

  -- Here the functions `f` and `g` are total, but Agda is unable to prove it.
  -- So we just postulate the totality by means of a pragma.

  mutual

    {-# TERMINATING #-}

    f : ℕ → ℕ
    f zero = zero
    f (suc n) = suc (f (g n))

    g : ℕ → ℕ
    g zero = zero
    g (suc n) = suc (g (f n))

    f5≡0 : f 5 ≡ 5
    f5≡0 = refl

  -- This proof is not completely formal, since it uses the totality of `f` that
  -- has been just postulated.

  mutual

    fn≡n : ∀ n → f n ≡ n
    fn≡n zero = refl
    fn≡n (suc n) = cong suc (
      f (g n)
        ≡⟨ cong f (gn≡n n) ⟩
      f n
        ≡⟨ fn≡n n ⟩
      n ∎)

    gn≡n : ∀ n → g n ≡ n
    gn≡n zero = refl
    gn≡n (suc n) rewrite fn≡n n | gn≡n n =
      refl

mutual

  -- Now we specify the domains of `f` and `g` by using
  -- Bove & Capretta's technique.
  -- Note that we have to define `F`, `G`, `f` and `g` simultaneously,
  -- because the definitions of `f` and `g` contain nested function calls.

  data F : (n : ℕ) → Set where
    a0 : F zero
    a1 : ∀ {n} (gn⇓ : G n) (fgn⇓ : F (g n gn⇓)) → F (suc n)

  f : (n : ℕ) → F n → ℕ
  f zero a0 = zero
  f (suc n) (a1 gn⇓ fgn⇓) = suc (f (g n gn⇓) fgn⇓)

  data G : (n : ℕ) → Set where
    b0 : G zero
    b1 : ∀ {n} (fn⇓ : F n) (gfn⇓ : G (f n fn⇓)) → G (suc n)

  g : (n : ℕ) → G n → ℕ
  g zero b0 = zero
  g (suc n) (b1 fn⇓ gfn⇓) = suc (g (f n fn⇓) gfn⇓)

-- OK. Now we can prove some theorems about `f` and `g`
-- without postulating their totality.
-- The trick is that the theorems say "the statement is true on condition
-- that the argument belongs to the function's domain.

f3⇓ : F 3
f3⇓ = a1 (b1 (a1 b0 a0) (b1 a0 b0)) (a1 (b1 a0 b0) (a1 b0 a0))

f3≡3 : f 3 f3⇓ ≡ 3
f3≡3 = refl

mutual

  fn≡n : ∀ n → (fn⇓ : F n) → f n fn⇓ ≡ n
  fn≡n zero a0 = refl
  fn≡n (suc n) (a1 gn⇓ fgn⇓) = cong suc (
    f (g n gn⇓) fgn⇓
      ≡⟨ fn≡n (g n gn⇓) fgn⇓ ⟩
    (g n gn⇓)
      ≡⟨ gn≡n n gn⇓ ⟩
    n ∎)

  gn≡n : ∀ n → (gn⇓ : G n) → g n gn⇓ ≡ n
  gn≡n zero b0 = refl
  gn≡n (suc n) (b1 fn⇓ gfn⇓) = cong suc (
    g (f n fn⇓) gfn⇓
      ≡⟨ gn≡n (f n fn⇓) gfn⇓ ⟩
    f n fn⇓
      ≡⟨ fn≡n n fn⇓ ⟩
    n ∎)

-- However, we can (formally) prove that `f` and `g` are total!

mutual

  all-f : ∀ n → F n
  all-f zero = a0
  all-f (suc n) = a1 gn⇓ fgn⇓ where
    gn⇓ : G n
    gn⇓ = all-g n
    fgn⇓ : F (g n gn⇓)
    fgn⇓ rewrite gn≡n n gn⇓ = all-f n

  all-g : ∀ n → G n
  all-g zero = b0
  all-g (suc n) = b1 fn⇓ gfn⇓ where
    fn⇓ : F n
    fn⇓ = all-f n
    gfn⇓ : G (f n fn⇓)
    gfn⇓ rewrite fn≡n n fn⇓ = all-g n

-- And now we can write down "normal" definition of `f` and `g` that
-- do not take additional arguments.

total-f : ℕ → ℕ
total-f n = f n (all-f n)

total-g : ℕ → ℕ
total-g n = g n (all-g n)

-- And we can prove some theorems about `total-f` and `total-g`.
-- (Without specifying the domains of `f` and `g`.)

tf5≡0 : total-f 5 ≡ 5
tf5≡0 = refl

tfn≡n : ∀ n → total-f n ≡ n
tfn≡n n = fn≡n n (all-f n)
