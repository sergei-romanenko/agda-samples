module 08-WellFounded where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
  hiding (partition)

open import Data.Product
  renaming (map to map×)

open import Function

open import Relation.Unary
open import Relation.Binary

import Induction.WellFounded
import Induction.Nat

open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

-- The termination checker of Agda is basicly the same as that of Foetus:
--
--   Andreas Abel. 1998. foetus -- Termination Checker for Simple
--   Functional Programs. Programming Lab Report.
--   http://www2.tcs.ifi.lmu.de/~abel/foetus/

-- The termination checker of Agda inspects the parameters of recursive call.
-- In the third line, (x′ < suc x′ & y = y).

add : (x y : ℕ) → ℕ
add zero y = y
add (suc x′) y = suc (add x′ y)

-- The dependency relation is defined as follows:
--
--  * Constructor elimination: if cons is a constructor,
--      x < cons a1 ... an x b1 ... bn
--  * Application: if y < x then
--       y a1 ... an < x

data Bin : Set where
  ε  : Bin
  c0 : Bin → Bin
  c1 : Bin → Bin

-- Here c0 x < c0 (c1 x) .

foo1 : Bin → ℕ
foo1 ε = zero
foo1 (c0 ε) = zero
foo1 (c0 (c1 x)) = suc (foo1 (c0 x))
foo1 (c0 (c0 x)) = suc (foo1 (c0 x))
foo1 (c1 x)      = suc (foo1 x)

module ConsElim-Bad where

  -- Here c1 x < c0 (c0 x) doesn't hold!

  foo2 : Bin → ℕ
  foo2 ε = zero
  foo2 (c0 ε) = zero
  foo2 (c0 (c1 x)) = suc (foo2 (c0 x))
  foo2 (c0 (c0 x)) = suc (foo2 (c1 x))
  foo2 (c1 x)      = suc (foo2 x)


-- Agda can find termination orders across mutually recursive functions.
-- Agda can find lexicographic termination orders.

-- There is a lexicographic order on parameters with respect
-- to the dependency order:
--   (x , y) << (x’, y’) ⇔ (x < x’ or (x ≤ x’ & y < y’))

ack : ℕ → ℕ → ℕ
ack 0 n = 1
ack (suc m) 0 = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

-- And what about the application rule:
--  y < x ⇒ y a1 ... an < x ?

--
-- Transfinite addition of ordinal numbers
--

data Ordℕ : Set where
  zero : Ordℕ
  suc  : (n : Ordℕ) → Ordℕ
  lim  : (f : ℕ → Ordℕ) → Ordℕ

addOrd : (n m : Ordℕ) → Ordℕ
addOrd zero m = m
addOrd (suc n) m = suc (addOrd n m)
addOrd (lim f) m = lim (λ u → addOrd (f u) m)

lim₀ : Ordℕ
lim₀ = lim (λ u → zero)

lim₀+0 : addOrd lim₀ zero ≡ lim (λ _ → zero)
lim₀+0 = refl

lim₀+m≡ : ∀ m → addOrd lim₀ m ≡ lim (λ _ → m)
lim₀+m≡ m = refl

ℕtoOrdℕ : (n : ℕ) → Ordℕ
ℕtoOrdℕ zero = zero
ℕtoOrdℕ (suc n) = suc (ℕtoOrdℕ n)

branch : Ordℕ
branch = lim (λ u → ℕtoOrdℕ u)

branch+branch : addOrd branch branch ≡
  lim (λ u → addOrd (ℕtoOrdℕ u) (lim ℕtoOrdℕ))
branch+branch = refl

--
-- But in some cases all the above is not sufficient.
--

module log2-bad where

  -- Division by 2, rounded downwards.
  -- ⌊_/2⌋ : ℕ → ℕ

  -- ⌊n/2⌋≤′n : ∀ n → ⌊ n /2⌋ ≤′ n

  log2 : ℕ → ℕ

  log2 zero = zero
  log2 (suc zero) = zero
  log2 (suc (suc n)) = suc (log2 (suc ⌊ n /2⌋))

  log2-test : map log2 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
  log2-test = refl

module log2-good-wf-ind where

  -- The accessibility predicate: x is accessible if everything which is
  -- smaller than x is also accessible (inductively).

  data Acc {a} {A : Set a} (_<_ : Rel A a) (x : A) : Set a where
    acc : (rs : ∀ y → y < x → Acc _<_ y) → Acc _<_ x

  -- The accessibility predicate encodes what it means to be
  -- well-founded; if all elements are accessible, then _<_ is
  -- well-founded.

  Well-founded : ∀ {a} {A : Set a} → Rel A a → Set a
  Well-founded _<_ = ∀ x → Acc _<_ x
  
  wf-induction : ∀ {ℓ} {A : Set ℓ} (_<_ : Rel A ℓ) → Well-founded _<_ →
    (P : A → Set ℓ) →
    (step : ∀ x → (∀ y → y < x → P y) → P x) →
    ∀ x → P x
  wf-induction _<_ wf P step x = helper x (wf x)
    where
      helper : ∀ x → Acc _<_ x → P x
      helper x (acc rs) = step x (λ y y<x → helper y (rs y y<x))

  <-well-founded : Well-founded _<′_
  <-well-founded′ : ∀ n y →  y <′ n → Acc _<′_ y

  <-well-founded n = acc (<-well-founded′ n)

  --<-well-founded′ n y y<′n = {!!}
  <-well-founded′ .(suc y) y ≤′-refl = <-well-founded y
  <-well-founded′ .(suc n) y (≤′-step {n} y<′n) = <-well-founded′ n y y<′n

  log2 : ℕ → ℕ
  log2′ : (n : ℕ) → Acc _<′_ n → ℕ

  log2 n = log2′ n (<-well-founded n)

  log2′ zero a = zero
  log2′ (suc zero) a = zero
  log2′ (suc (suc n)) (acc rs) =
    suc (log2′ (suc n′) (rs (suc n′) (s≤′s (s≤′s (⌊n/2⌋≤′n n)))))
    where n′ = ⌊ n /2⌋

  log2-test : map log2 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
  log2-test = refl

module log2-good-lib where

  open Induction.WellFounded
  open Induction.Nat

  log2 : ℕ → ℕ
  log2′ : (n : ℕ) → Acc _<′_ n → ℕ

  log2 n = log2′ n (<-well-founded n)

  log2′ zero a = zero
  log2′ (suc zero) a = zero
  log2′ (suc (suc n)) (acc rs) =
    suc (log2′ (suc n′) (rs (suc n′) (s≤′s (s≤′s (⌊n/2⌋≤′n n)))))
    where n′ = ⌊ n /2⌋

  log2-test : map log2 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ []
  log2-test = refl

module log2-good-<-Rec where

  open Induction.WellFounded
  open Induction.Nat

  log2 : ℕ → ℕ
  log2 = <-rec (λ _ → ℕ) log2′
    where
      log2′ : (n : ℕ) → ((m : ℕ) → m <′ n → ℕ) → ℕ
      log2′ zero rec = zero
      log2′ (suc zero) rec = zero
      log2′ (suc (suc n)) rec =
        suc (rec (suc n′) (s≤′s (s≤′s (⌊n/2⌋≤′n n))))
        where n′ = ⌊ n /2⌋

--
-- Quicksort
--

partition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
partition p [] = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

module Quicksort-bad where

  quicksort : {A : Set} (p : A → A → Bool) → List A → List A
  quicksort p [] = []
  quicksort p (x ∷ xs) with partition (p x) xs
  ... | (small , big) = small′ ++ [ x ] ++ big′
    where
      small′ = quicksort p small
      big′   = quicksort p big

module Quicksort-good where

  open Induction.WellFounded
  open Induction.Nat

  _≼_ : ∀ {a} {A : Set a} → Rel (List A) _
  xs ≼ ys = length xs <′ suc (length ys)

  partition-size : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) →
    proj₁ (partition p xs) ≼ xs × proj₂ (partition p xs) ≼ xs

  partition-size p [] = ≤′-refl , ≤′-refl
  partition-size p (x ∷ xs)
    with p x | partition p xs | partition-size p xs
  ... | true  | as , bs | as-size , bs-size = s≤′s as-size , ≤′-step bs-size
  ... | false | as , bs | as-size , bs-size = ≤′-step as-size , s≤′s bs-size

  quicksort′ : {A : Set} (p : A → A → Bool) → (xs : List A) →
                 Acc _<′_ (length xs) → List A
  quicksort′ p [] _ = []
  quicksort′ p (x ∷ xs) (acc g)
    with partition (p x) xs | partition-size (p x) xs
  ... | small , big | small-size , big-size = small′ ++ [ x ] ++ big′
    where
      small′ = quicksort′ p small (g (length small) small-size)
      big′   = quicksort′ p big   (g (length big) big-size)

  quicksort : {A : Set} (p : A → A → Bool) → (xs : List A) → List A
  quicksort p xs = quicksort′ p xs (<-well-founded (length xs))

--
