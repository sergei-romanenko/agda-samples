module Expr where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec as Vec
open import Data.Vec.N-ary

open import Function using (_∘_; const)

-- Expressions

infixr 40 _⊕_
infixr 60 _⊗_

data Expr n : Set where
  var : (i : Fin n) → Expr n
  _⊕_ : (a b : Expr n) → Expr n
  ◇   : Expr n

-- "Normalized representations" (which are not expressions)

NR : ℕ → Set
NR n = Vec ℕ n

-- Evaluating an expression to produce its "normalized representation"

1-at : ∀ {n} → Fin n → NR n
1-at zero    = 1 ∷ replicate 0
1-at (suc i) = 0 ∷ 1-at i

nr : ∀ {n} → Expr n → NR n
nr (var i) = 1-at i
nr (a ⊕ b) = zipWith _+_ (nr a) (nr b)
nr nil     = replicate 0

-- Reifying a "normal forms" to an expression

_⊗_ : ∀ {n} → ℕ → Expr n → Expr n
zero  ⊗ a = ◇
suc n ⊗ a = a ⊕ (n ⊗ a)

fold-zip : ∀ {n m} → Vec ℕ m → Vec (Expr n) m → Expr n
fold-zip ks as = Vec.foldr _ _⊕_ ◇ (zipWith _⊗_ ks as)

vars : ∀ {n} → Vec (Expr n) n
vars = tabulate var

reify : ∀ {n} → NR n → Expr n
reify nf = fold-zip nf vars

-- Normalization (to an expression)

norm : ∀ {n} → Expr n → Expr n
norm = reify ∘ nr

-- Applies the function to all possible "variables".

close : ∀ {a} {A : Set a} (n : ℕ) → N-ary n (Expr n) A → A
close n f = f $ⁿ vars {n}

private
  module Examples where
    open import Relation.Binary.PropositionalEquality

    expr₁ : Expr 3
    expr₁ = var zero ⊕ (var (suc zero) ⊕ var zero)

    expr₂ = close 3 λ a b c → a ⊕ (b ⊕ a)

    expr₁≡expr₂ : expr₁ ≡ expr₂
    expr₁≡expr₂ = refl

    nr₁ : nr expr₁ ≡
      suc (suc zero) ∷ suc zero ∷ zero ∷ []
    nr₁ = refl

    norm₁ : norm expr₁ ≡
      (var zero ⊕ var zero ⊕ ◇) ⊕ (var (suc zero) ⊕ ◇) ⊕ ◇ ⊕ ◇
    norm₁ = refl

--
