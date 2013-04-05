module Expr where

open import Data.Nat
open import Data.Fin
  using (Fin; zero; suc)
open import Data.Product
  using (_×_; _,_)
open import Data.Vec
open import Data.Vec.N-ary

open import Function
  using (_∘_)

--
-- Expressions
--

infixr 40 _⊕_
infixr 60 _⊗_

data Expr n : Set where
  var : (i : Fin n) → Expr n
  _⊕_ : (a b : Expr n) → Expr n
  ◇   : Expr n

-- A variant of _,_ which is intended to make equalities
-- look a bit nicer.

infix 4 _⊜_

_⊜_ : ∀ {n} → Expr n → Expr n → Expr n × Expr n
_⊜_ = _,_

-- All possible variables.

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var

-- `close n f` applies a curried function f to n possible variables
--     var 0 , var 1 , ... , var (n - 1) .
-- Thus equalities can be written in a more human-friendly form:
--     close 3 λ a b c → a ⊕ (b ⊕ a)
-- instead of
--     var zero ⊕ (var (suc zero) ⊕ var zero) .

close : ∀ {a} {A : Set a} (n : ℕ) → N-ary n (Expr n) A → A
close n f = f $ⁿ vars {n}

--
-- "Normal representations" (which are not expressions)
--

NR : ℕ → Set
NR n = Vec ℕ n

--
-- Evaluating an expression to produce its "normal representation"
--

1-at : ∀ {n} → Fin n → NR n
1-at zero    = 1 ∷ replicate 0
1-at (suc i) = 0 ∷ 1-at i

nr : ∀ {n} → Expr n → NR n
nr (var i) = 1-at i
nr (a ⊕ b) = zipWith _+_ (nr a) (nr b)
nr ◇ = replicate 0

--
-- Reifying a "normal representation" to an expression
--

_⊗_ : ∀ {n} → ℕ → Expr n → Expr n
zero  ⊗ a = ◇
suc k ⊗ a = a ⊕ (k ⊗ a)

eval-nr : ∀ {n m} → Vec ℕ m → Vec (Expr n) m → Expr n
eval-nr ks es = foldr _ _⊕_ ◇ (zipWith _⊗_ ks es)

reify : ∀ {n} → NR n → Expr n
reify nr = eval-nr nr vars

--
-- Normalization (to an expression)
--

norm : ∀ {n} → Expr n → Expr n
norm = reify ∘ nr

--
