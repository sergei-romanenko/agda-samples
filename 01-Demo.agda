module 01-Demo where

-- Emacs Agda-mode cheat sheet:
-- C-C C-L (load file)
-- C-C C-N (evaluate an expression)
-- C-C C-D (type of an expression)
-- C-C C-F (forward to next goal)
-- C-C C-B (back to previous goal)
-- C-C C-T (type of the current goal)
-- C-C C-R (refine the current goal)
-- C-C C-C (case split the current goal)
-- C-C C-A (auto-filling the current goal
--           -l list possible variants
--           -c try case-split
--           -m use constants in scope defined in the module)
-- Unicode entered in pseudo-\LaTeX

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
x + y = {!!}

-- Magic to write 3 rather than suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

module Samples-1 where
  x : ℕ
  x = 2 + 1

  2+1 : ℕ
  2+1 = 2 + 1

-- Polymorphism

infixr 5 _∷_ _++_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

_++_ : {A : Set} → (xs ys : List A) → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Equality

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

--Theorem proving

theorem1 : 2 + 1 ≡ 3
theorem1 = {!!}

theorem2 : (n : ℕ) → 0 + n ≡ n
theorem2 n = {!!}

-- n+0 : ∀ n → n + 0 ≡ n
-- n+0 n = ?

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

n+0 : ∀ n → n + 0 ≡ n
n+0 n = {!!}

n+sm : ∀ n m → n + suc m ≡ suc (n + m)
n+sm n m = {!!}

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym xy = {!!}

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans xy yz = {!!}

+-comm : ∀ n m → n + m ≡ m + n
+-comm n m = {!!}
