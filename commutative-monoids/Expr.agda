
module Expr where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec as Vec
open import Data.Vec.N-ary

open import Function using (_∘_; const)

infix  20 _==_
infixr 40 _⊕_
infixr 60 _⊗_

data Expr n : Set where
  var : (i : Fin n) → Expr n
  _⊕_ : (a b : Expr n) → Expr n
  nil   : Expr n

data Eqn n : Set where
  _==_ : (a b : Expr n) → Eqn n

NF : ℕ → Set
NF n = Vec ℕ n

1-at : ∀ {n} → Fin n → NF n
1-at zero    = 1 ∷ replicate 0
1-at (suc i) = 0 ∷ 1-at i

eval : ∀ {n} → Expr n → NF n
eval (var i) = 1-at i
eval (a ⊕ b) = zipWith _+_ (eval a) (eval b)
eval nil     = replicate 0

_⊗_ : ∀ {n} → ℕ → Expr n → Expr n
zero  ⊗ a = nil
suc n ⊗ a = a ⊕ (n ⊗ a)

fold-zip : ∀ {n m} → Vec ℕ m → Vec (Expr n) m → Expr n
fold-zip ks as = Vec.foldr _ _⊕_ nil (zipWith _⊗_ ks as)

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var

reify : ∀ {n} → NF n → Expr n
reify nf = fold-zip nf vars

norm : ∀ {n} → Expr n → Expr n
norm = reify ∘ eval

normEqn : ∀ {n} → Eqn n → Eqn n
normEqn (a == b) = norm a == norm b

build : ∀ {a} {A : Set a} (n : ℕ) → N-ary n (Expr n) A → A
build n f = f $ⁿ vars {n}

private
  module Examples where

    expr₁ : Expr 3
    expr₁ = var zero ⊕ (var (suc zero) ⊕ var zero)

    expr₂ = build 3 λ a b c → a ⊕ (b ⊕ a)

    eqn₁ = build 4 λ a b c d →
             (a ⊕ b) ⊕ (c ⊕ d) == (a ⊕ c) ⊕ (b ⊕ d)

