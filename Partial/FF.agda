module Partial.FF where

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module ff-bad where

  {-# TERMINATING #-}

  f : ℕ → ℕ
  f zero = zero
  f (suc zero) = zero
  f (suc (suc n)) = f (f n)

  f5≡0 : f 5 ≡ 0
  f5≡0 = refl

  fn≡0 : ∀ n → f n ≡ 0
  fn≡0 zero = refl
  fn≡0 (suc zero) = refl
  fn≡0 (suc (suc n)) =
    f (f n) ≡⟨ cong f (fn≡0 n) ⟩ f 0 ≡⟨⟩ 0 ∎

mutual

  data F : (n : ℕ) → Set where
    d0 : F zero
    d1 : F (suc zero)
    d2 : ∀ {n} →
      (hn : F n) →
      F (f n hn) →
      F (suc (suc n))

  f : (n : ℕ) → F n → ℕ
  f zero d0 = zero
  f (suc zero) d1 = zero
  f (suc (suc n)) (d2 hn hfn) =
    f (f n hn) hfn

h5 : F 5
h5 = d2 (d2 d1 d0) d0

f5h≡0 : f 5 h5 ≡ 0
f5h≡0 = refl

fnh≡0 : ∀ n → (hn : F n) → f n hn ≡ 0
fnh≡0 zero d0 = refl
fnh≡0 (suc zero) d1 = refl
fnh≡0 (suc (suc n)) (d2 hn hfn) =
  f (f n hn) hfn
    ≡⟨ fnh≡0 (f n hn) hfn ⟩
  0 ∎

all-f : ∀ n → F n
all-f zero = d0
all-f (suc zero) = d1
all-f (suc (suc n)) =
  d2 hn hfn
  where
  hn : F n
  hn = all-f n
  fn≡0 : f n hn ≡ 0
  fn≡0 = fnh≡0 n hn
  hfn : F (f n hn)
  hfn = subst F (sym fn≡0) d0
  
total-f : ℕ → ℕ
total-f n = f n (all-f n)

tf5≡0 : total-f 5 ≡ 0
tf5≡0 = refl

tfn≡0 : ∀ n → total-f n ≡ 0
tfn≡0 n = fnh≡0 n (all-f n)
