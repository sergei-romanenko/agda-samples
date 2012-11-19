module 01-DemoSol where

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
zero + y = y
suc x + y = suc (x + y)

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

{-
infixr 4 _,_
infixr 2 _×_

data _×_ (A B : Set) : Set where
  _,_ : (a : A) (b : B) → A × B

div-list : {A : Set} → (zs : List A) → List A × List A
div-list [] = [] , []
div-list (x ∷ []) = x ∷ [] , []
div-list (x ∷ y ∷ zs) with div-list zs
div-list (x ∷ y ∷ zs) | xs , ys = (x ∷ xs) , (y ∷ ys)
-}

-- Equality

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

--Theorem proving

theorem1 : 2 + 1 ≡ 3
theorem1 = refl

theorem2 : (n : ℕ) → 0 + n ≡ n
theorem2 n = refl

-- n+0 : ∀ n → n + 0 ≡ n
-- n+0 n = ?

cong : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

n+0 : ∀ n → n + 0 ≡ n
n+0 zero = refl
n+0 (suc n) = cong suc (n+0 n)

n+sm : ∀ n m → n + suc m ≡ suc (n + m)
n+sm zero m = refl
n+sm (suc n) m = cong suc (n+sm n m)

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero m =
  sym (n+0 m)
+-comm (suc n) m = trans p q
  where
    p : suc (n + m) ≡ suc (m + n)
    p = cong suc (+-comm n m)
    q : suc (m + n) ≡ m + suc n
    q = sym (n+sm m n)
