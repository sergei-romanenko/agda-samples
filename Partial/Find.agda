module Partial.Find where

open import Data.Nat.Base
open import Data.Bool.Base
  using (Bool; true; false; not; T)
open import Data.Empty
open import Data.Product

open import Function
  using(_$_; const; id)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

ge3 : ℕ → Bool
ge3 (suc (suc (suc k))) = true
ge3 n = false

ge3? : (n : ℕ) → Dec (3 ≤ n)
ge3? n = 3 ≤? n

module Find-bad where

  -- We say to the Agda compiler that `find` is total
  -- but it is not true!

  {-# TERMINATING #-}
  find : (p : ℕ → Bool) → ℕ → ℕ
  find p n with p n
  ... | true = n
  ... | false = find p (suc n)

  -- If we are lucky, `find` terminates (here - at compile time).

  find-ge3≡3 : find ge3 0 ≡ 3
  find-ge3≡3 = refl

  -- An attempt to prove the following "theorem" makes the Agda compiler go
  -- into an infinite loop. :-(

  {-
  non-terminating : find (const false) 0 ≡ 2
  non-terminating = refl
  -}

  -- The following "proof by induction" is rather silly, because
  -- no argument is decreasing ...

  {-# TERMINATING #-}
  correct : ∀ (p : ℕ → Bool) (n : ℕ) → p (find p n) ≡ true
  correct p n with p n | inspect p n
  ... | true | [ pn≡true ] = pn≡true
  ... | false | [ pn≡false ] = correct p (suc n)

module Find-good where

  -- Applying Bove & Capretta's technique in a straightforward way,
  -- we get the following solution.

  module _ (p : ℕ → Bool) where
  
    mutual

      data Find : ℕ → Set where
        a0 : ∀ {n} → Find′ n (p n) → Find n

      data Find′ : ℕ → Bool → Set where
        b0 : ∀ {n} → Find′ n true
        b1 : ∀ {n} → Find (suc n) → Find′ n false

    mutual

      find : (n : ℕ) (h : Find n) → ℕ
      find n (a0 h) = find′ n (p n) h

      find′ : (n : ℕ) (b : Bool) (h : Find′ n b) → ℕ
      find′ n true b0 = n
      find′ n false (b1 h) = find (suc n) h

  ge3! : Find ge3 0
  ge3! = a0 (b1 (a0 (b1 (a0 (b1 (a0 b0))))))

  find-ge3≡3 : ℕ
  find-ge3≡3 = find ge3 0 ge3!

  correct : ∀ p n → (h : Find p n) → p (find p n h) ≡ true
  correct p n (a0 h) with p n | inspect p n
  correct p n (a0 b0) | true | [ pn≡true ] =
    pn≡true
  correct p n (a0 (b1 h)) | false | [ pn≡false ] =
    correct p (suc n) h

module Find-dec-bad where

  -- We say to the Agda compiler that `find` is total
  -- but it is not true!

  module _ {P : ℕ → Set} (p? : (k : ℕ) → Dec (P k)) where

    mutual

      {-# TERMINATING #-}
      find : (n : ℕ) → ∃ λ m → P m
      find n = find′ n (p? n)

      find′ : (n : ℕ) (pn : Dec (P n)) → (∃ λ m → P m)
      find′ n (yes pn) = n , pn
      find′ n (no ¬pn) = find (suc n)

  -- If we are lucky, `find` terminates (here - at compile time).

  find-ge3?≡3 : find ge3? 0 ≡ (3 , s≤s (s≤s (s≤s z≤n)))
  find-ge3?≡3 = refl

  -- An attempt to prove this following "theorem" makes the Agda compiler go
  -- into an infinite loop. :-(

  {-
  non-terminating : find (const (no id)) 0 ≡ 2
  non-terminating = refl
  -}

  -- The following "proof by induction" is rather silly, because
  -- no argument is decreasing ...

  {-# TERMINATING #-}
  correct : {P : ℕ → Set} (p? : (n : ℕ) → Dec (P n)) (n : ℕ) →
                ∃ λ q → p? (proj₁ (find p? n)) ≡ yes q
  correct p? n with p? n | inspect p? n
  ... | yes pn | [ p?n≡yes-pn ] = pn , p?n≡yes-pn
  ... | no ¬pn | [ p?n≡no-¬pn ] = correct p? (suc n)
  
module Find-dec-good where

  module _ {P : ℕ → Set} (p? : (k : ℕ) → Dec (P k)) where

    mutual

      data Find : (n : ℕ) → Set where
        a0 : ∀ {n} → Find′ n (p? n) → Find n

      data Find′ : (n : ℕ) (pn : Dec (P n)) → Set where
        b0 : ∀ {n pn} → Find′ n (yes pn)
        b1 : ∀ {n ¬pn} → Find (suc n) → Find′ n (no ¬pn)

      find : (n : ℕ) (h : Find n) → ∃ λ m → P m
      find n (a0 h) = find′ n (p? n) h

      find′ : (n : ℕ) (pn : Dec (P n)) (h : Find′ n pn) → (∃ λ m → P m)
      find′ n (yes pn) b0 = n , pn
      find′ n (no ¬pn) (b1 h) = find (suc n) h

  ge3! : Find ge3? 0
  ge3! = a0 (b1 (a0 (b1 (a0 (b1 (a0 b0))))))

  find-ge3?≡ : find ge3? 0 ge3! ≡ (3 , s≤s (s≤s (s≤s z≤n)))
  find-ge3?≡ = refl
