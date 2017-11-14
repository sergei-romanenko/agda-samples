module Partial.Until where

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
ge3 zero = false
ge3 (suc zero) = false
ge3 (suc (suc zero)) = false
ge3 (suc (suc (suc n))) = true

ge3? : (n : ℕ) → Dec (3 ≤ n)
ge3? n = 3 ≤? n

module Until-bad where

  -- We say to the Agda compiler that `until` is total
  -- but it is not true!

  {-# TERMINATING #-}
  until : {A : Set} (p : A → Bool) (f : A → A) (x : A) → A
  until p f x with p x
  until p f x | true = x
  until p f x | false = until p f (f x)

  -- If we are lucky, `until` terminates (here - at compile time).

  until-ge3≡3 : until ge3 suc 0 ≡ 3
  until-ge3≡3 = refl

  -- An attempt to prove the following "theorem" makes the Agda compiler go
  -- into an infinite loop. :-(

  {-
  non-terminating : until (const false) suc 0 ≡ 2
  non-terminating = refl
  -}

  -- The following "proof by induction" is rather silly, because
  -- no argument is decreasing ...

  {-# TERMINATING #-}
  correct : {A : Set} (p : A → Bool) (f : A → A) (x : A) →
    p (until p f x) ≡ true
  correct p f x with p x | inspect p x
  correct p f x | true  | [ px≡true ] = px≡true
  correct p f x | false | [ px≡false ] = correct p f (f x)

module Find-good where

  -- Applying Bove & Capretta's technique in a straightforward way,
  -- we get the following solution.

  module _ {A : Set} (p : A → Bool) (f : A → A) where
  
    mutual

      data Until : A → Set where
        a0 : ∀ {x} → Until′ x (p x) → Until x

      data Until′ : A → Bool → Set where
        b0 : ∀ {x} → Until′ x true
        b1 : ∀ {x} → Until (f x) → Until′ x false

    mutual

      until : (x : A) (h : Until x) → A
      until x (a0 h) = until′ x (p x) h

      until′ : (x : A) (b : Bool) (h : Until′ x b) → A
      until′ x true b0 = x
      until′ x false (b1 h) = until (f x) h


    correct : ∀ x → (h : Until x) → p (until x h) ≡ true
    correct x (a0 h) with p x | inspect p x
    correct x (a0 b0) | true | [ px≡true ] =
      px≡true
    correct x (a0 (b1 h)) | false | [ px≡false ] =
      correct (f x) h

  ge3! : Until ge3 suc 0
  ge3! = a0 (b1 (a0 (b1 (a0 (b1 (a0 b0))))))

  until-ge3≡3 : until ge3 suc 0 ge3! ≡ 3
  until-ge3≡3 = refl

module Until-dec-bad where

  -- We say to the Agda compiler that `until` is total
  -- but it is not true!

  module _ {A : Set} {P : A → Set} (p? : (x : A) → Dec (P x)) (f : A → A) where

    mutual

      {-# TERMINATING #-}
      until : (x : A) → ∃ λ z → P z
      until x = until′ x (p? x)

      until′ : (x : A) (px : Dec (P x)) → (∃ λ z → P z)
      until′ x (yes px) = x , px
      until′ x (no ¬px) = until (f x)


    -- The following "proof by induction" is rather silly, because
    -- no argument is decreasing ...

    {-# TERMINATING #-}
    correct : (x : A) → ∃ λ q → p? (proj₁ (until x)) ≡ yes q
    correct x with p? x | inspect p? x
    ... | yes px | [ p?x≡yes-px ] = px , p?x≡yes-px
    ... | no ¬px | [ p?x≡no-¬px ] = correct (f x)

  -- If we are lucky, `until` terminates (here - at compile time).

  until-ge3?≡3 : until ge3? suc 0 ≡ (3 , s≤s (s≤s (s≤s z≤n)))
  until-ge3?≡3 = refl

  -- An attempt to prove this following "theorem" makes the Agda compiler go
  -- into an infinite loop. :-(

  {-
  non-terminating : until (const (no id)) suc 0 ≡ 2
  non-terminating = refl
  -}

module Until-dec-good where

  module _ {A : Set} {P : A → Set} (p? : (x : A) → Dec (P x)) (f : A → A) where

    mutual

      data Until : (x : A) → Set where
        a0 : ∀ {x} → Until′ x (p? x) → Until x

      data Until′ : (x : A) (px : Dec (P x)) → Set where
        b0 : ∀ {x px} → Until′ x (yes px)
        b1 : ∀ {x ¬px} → Until (f x) → Until′ x (no ¬px)

    mutual

      until : (x : A) (h : Until x) → ∃ λ z → P z
      until x (a0 h) = until′ x (p? x) h

      until′ : (x : A) (px : Dec (P x)) (h : Until′ x px) → (∃ λ z → P z)
      until′ x (yes px) b0 = x , px
      until′ x (no ¬px) (b1 h) = until (f x) h

  ge3! : Until ge3? suc 0
  ge3! = a0 (b1 (a0 (b1 (a0 (b1 (a0 b0))))))

  until-ge3?≡ : until ge3? suc 0 ge3! ≡ (3 , s≤s (s≤s (s≤s z≤n)))
  until-ge3?≡ = refl
