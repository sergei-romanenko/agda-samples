module 08-WellFounded where

open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
  hiding (partition)

open import Data.Product

open import Function

open import Relation.Unary
open import Relation.Binary

-- Agda can find termination orders across mutually recursive functions.
-- Agda can find lexicographic termination orders.

ack : ℕ → ℕ → ℕ
ack 0 n = 1
ack (suc m) 0 = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

-- But in some cases it is not sufficient

partition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
partition p [] = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

module NaiveQuicksort where

  quicksort : {A : Set} (p : A → A → Bool) → List A → List A
  quicksort p [] = []
  quicksort p (x ∷ xs) with partition (p x) xs
  ... | (small , big) = small′ ++ [ x ] ++ big′
    where
      small′ = quicksort p small
      big′   = quicksort p big


{- open import Induction.WellFounded -}

-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

data Acc {a} {A : Set a} (_<_ : Rel A a) (x : A) : Set a where
  --acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x
  acc : (rs : ∀ y → y < x → Acc _<_ y) → Acc _<_ x

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.

Well-founded : ∀ {a} {A : Set a} → Rel A a → Set a
Well-founded _<_ = ∀ x → Acc _<_ x

<′-ℕ-wf : Well-founded _<′_
<′-ℕ-wf x = acc (helper x)
  where
    helper : ∀ (x y : ℕ) (y<′x : y <′ x) → Acc _<′_ y
    helper .(suc y) y ≤′-refl = <′-ℕ-wf y
    helper .(suc x) y (≤′-step {x} y<′x) = helper x y y<′x

module Inverse-image {ℓ} {A B : Set ℓ} {_<_ : Rel B ℓ}
                     (f : A → B) where

  accessible : ∀ {x} → Acc _<_ (f x) → Acc (_<_ on f) x
  accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  well-founded : Well-founded _<_ → Well-founded (_<_ on f)
  well-founded wf = λ x → accessible (wf (f x))


_≺_ : ∀ {a} {A : Set a} (xs ys : List A) → Set
_≺_ = _<′_ on length  -- λ xs yx → length xs <′ length ys

_≼_ : ∀ {a} {A : Set a} → Rel (List A) _
xs ≼ ys = length xs <′ suc (length ys)

open module Lenth-wf {A : Set} = Inverse-image {_} {List A} {ℕ} {_<′_} length
  renaming(accessible to <′-on-length-acc→; well-founded to <′-on-length-wf→)

<′-on-length-wf : ∀ {A : Set} → Well-founded (_<′_ on length{_}{A})
<′-on-length-wf = <′-on-length-wf→ <′-ℕ-wf

<′-on-length-acc : ∀ {A : Set} → (xs : List A) →
                     Acc (_<′_ on length {_} {A}) xs
<′-on-length-acc xs = <′-on-length-acc→ (<′-ℕ-wf (length xs)) 

partition-size : ∀ {a} {A : Set a} (p : A → Bool) (xs : List A) →
  proj₁ (partition p xs) ≼ xs × proj₂ (partition p xs) ≼ xs

partition-size p [] = ≤′-refl , ≤′-refl
partition-size p (x ∷ xs)
  with p x | partition p xs | partition-size p xs
... | true  | as , bs | as-size , bs-size = s≤′s as-size , ≤′-step bs-size
... | false | as , bs | as-size , bs-size = ≤′-step as-size , s≤′s bs-size

quicksort′ : {A : Set} (p : A → A → Bool) → (xs : List A) →
               Acc _≺_ xs → List A
quicksort′ p [] _ = []
quicksort′ p (x ∷ xs) (acc g)
  with partition (p x) xs | partition-size (p x) xs
... | small , big | small-size , big-size = small′ ++ [ x ] ++ big′
  where
    small′ = quicksort′ p small (g small small-size)
    big′   = quicksort′ p big   (g big big-size)

quicksort : {A : Set} (p : A → A → Bool) → (xs : List A) → List A
quicksort p xs = quicksort′ p xs (<′-on-length-acc xs)
