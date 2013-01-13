{-
  Based on "Appendix" in

  Yves Bertot and Pierre Castéran.
  Interactive Theorem Proving and Program Development.
  Coq’Art: The Calculus of Inductive Constructions.  
  Texts in Theoretical Computer Science. An EATCS series. Springer Verlag, 2004.

  http://www.cse.chalmers.se/research/group/logic/TypesSS05/resources/coq/CoqArt/
-}

module 10-InsertionSort where

open import Data.Nat
open import Data.List
open import Data.Empty
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open import Data.Nat.Properties

infix 4 _≤∷_
infix 10000 [∷]_

data _≤∷_ (m : ℕ) : (xs : List ℕ) → Set where
  [] : m ≤∷ []
  [∷]_ : ∀ {x xs} → m ≤ x → m ≤∷ (x ∷ xs)

data Sorted : List ℕ → Set where
  [] : Sorted []
  ⟨_≤∷_⟩ : ∀ {x xs} → (x≤∷s : x ≤∷ xs) →
            (s : Sorted xs) →
            Sorted (x ∷ xs)

sort-2357 : Sorted (2 ∷ 3 ∷ 5 ∷ 7 ∷ [])
sort-2357 =
  ⟨ ([∷] s≤s (s≤s z≤n)) ≤∷
  ⟨ ([∷] s≤s (s≤s (s≤s z≤n))) ≤∷
  ⟨ ([∷] s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ≤∷
  ⟨ [] ≤∷ [] ⟩ ⟩ ⟩ ⟩

sorted-inv : ∀ {x xs} → Sorted (x ∷ xs) → Sorted xs
sorted-inv ⟨ x≤∷s ≤∷ s ⟩ = s

-- The number of occurrences of x in xs

nb-occ : (n : ℕ) (xs : List ℕ) → ℕ

nb-occ n [] = zero
nb-occ n (x ∷ xs) with n ≟ x
... | yes _ = suc (nb-occ n xs)
... | no  _ = nb-occ n xs

nb-occ-3-373 : nb-occ 3 (3 ∷ 7 ∷ 3 ∷ []) ≡ 2
nb-occ-3-373 = refl

nb-occ-5-373 : nb-occ 5 (3 ∷ 7 ∷ 3 ∷ []) ≡ zero
nb-occ-5-373 = refl

--
-- ≋
--

infix 4 _≋_

_≋_ : (xs ys : List ℕ) → Set
xs ≋ ys = ∀ n → nb-occ n xs ≡ nb-occ n ys

≋-refl : ∀ xs → xs ≋ xs
≋-refl xs n = refl

≋-sym : ∀ {xs ys} → xs ≋ ys → ys ≋ xs
≋-sym xs≋ys n = sym (xs≋ys n)

≋-trans : ∀ {xs ys zs} → xs ≋ ys → ys ≋ zs → xs ≋ zs
≋-trans xs≋ys ys≋zs n = trans (xs≋ys n) (ys≋zs n)

≋-∷ : ∀ x {xs ys} → xs ≋ ys → x ∷ xs ≋ x ∷ ys
≋-∷ x xs≋ys n with n ≟ x
... | yes n≡x = cong suc (xs≋ys n)
... | no  n≢x = xs≋ys n

--
-- Auxiliaries
--

nb-occ-≡ : ∀ {n x xs} → n ≡ x → nb-occ n (x ∷ xs) ≡ suc (nb-occ n xs)
nb-occ-≡ {n} {x} n≡x with n ≟ x
nb-occ-≡ n≡x | yes _ = refl
nb-occ-≡ n≡x | no  n≢x = ⊥-elim (n≢x n≡x)

nb-occ-≢ : ∀ {n x xs} → n ≢ x → nb-occ n (x ∷ xs) ≡ nb-occ n xs
nb-occ-≢ {n} {x} n≢x with n ≟ x
nb-occ-≢ n≢x | yes n≡x = ⊥-elim (n≢x n≡x)
nb-occ-≢ n≢x | no  _ = refl


≋-perm : ∀ x y {xs ys} → xs ≋ ys → x ∷ y ∷ xs ≋ y ∷ x ∷ ys
≋-perm x y {xs} {ys} xs≋ys n = helper (n ≟ x) (n ≟ y)
  where
    open ≡-Reasoning
    helper : Dec (n ≡ x) → Dec (n ≡ y) → _
    helper (yes n≡x) (yes n≡y) =
      begin
        nb-occ n (x ∷ y ∷ xs) ≡⟨ nb-occ-≡ n≡x ⟩
        suc (nb-occ n (y ∷ xs)) ≡⟨ cong suc (nb-occ-≡ n≡y) ⟩
        suc (suc (nb-occ n xs)) ≡⟨ cong (suc ∘ suc) (xs≋ys n) ⟩
        suc (suc (nb-occ n ys)) ≡⟨ sym (cong suc (nb-occ-≡ n≡x)) ⟩
        suc (nb-occ n (x ∷ ys)) ≡⟨ sym (nb-occ-≡ n≡y) ⟩
        nb-occ n (y ∷ x ∷ ys)
      ∎
    helper (yes n≡x) (no n≢y) =
      begin
        nb-occ n (x ∷ y ∷ xs) ≡⟨ nb-occ-≡ n≡x ⟩
        suc (nb-occ n (y ∷ xs)) ≡⟨ cong suc (nb-occ-≢ n≢y) ⟩
        suc (nb-occ n xs) ≡⟨ cong suc (xs≋ys n) ⟩
        suc (nb-occ n ys) ≡⟨ sym (nb-occ-≡ n≡x) ⟩
        nb-occ n (x ∷ ys) ≡⟨ sym (nb-occ-≢ n≢y) ⟩
        nb-occ n (y ∷ x ∷ ys)
      ∎
    helper (no n≢x) (yes n≡y) =
      begin
        nb-occ n (x ∷ y ∷ xs) ≡⟨ nb-occ-≢ n≢x ⟩
        nb-occ n (y ∷ xs) ≡⟨ nb-occ-≡ n≡y ⟩
        suc (nb-occ n xs) ≡⟨ cong suc (xs≋ys n) ⟩
        suc (nb-occ n ys) ≡⟨ sym (cong suc (nb-occ-≢ n≢x)) ⟩
        suc (nb-occ n (x ∷ ys)) ≡⟨ sym (nb-occ-≡ n≡y) ⟩
        nb-occ n (y ∷ x ∷ ys)
      ∎
    helper (no n≢x) (no n≢y) =
      begin
        nb-occ n (x ∷ y ∷ xs) ≡⟨ nb-occ-≢ n≢x ⟩
        nb-occ n (y ∷ xs) ≡⟨ nb-occ-≢ n≢y ⟩
        nb-occ n xs ≡⟨ xs≋ys n ⟩
        nb-occ n ys ≡⟨ sym (nb-occ-≢ n≢x) ⟩
        nb-occ n (x ∷ ys) ≡⟨ sym (nb-occ-≢ n≢y) ⟩
        nb-occ n (y ∷ x ∷ ys)
      ∎

--
-- insert
--

-- Insertion of n into xs at the right place
-- (assuming that xs is sorted)

insert : (m : ℕ) (xs : List ℕ) → List ℕ
insert m [] = m ∷ []
insert m (x ∷ xs) with m ≤? x
insert m (x ∷ xs) | yes m≤x =
  m ∷ x ∷ xs
insert m (x ∷ xs) | no  m≰x =
  x ∷ insert m xs

insert-4-25 : insert 4 (2 ∷ 5 ∷ []) ≡ 2 ∷ 4 ∷ 5 ∷ []
insert-4-25 = refl

insert-1-25 : insert 1 (2 ∷ 5 ∷ []) ≡ 1 ∷ 2 ∷ 5 ∷ []
insert-1-25 = refl

insert-6-25 : insert 6 (2 ∷ 5 ∷ []) ≡ 2 ∷ 5 ∷ 6 ∷ []
insert-6-25 = refl

-- The function `insert` seems to be a good tool for sorting...

insert-≋ : ∀ m xs → m ∷ xs ≋ insert m xs
insert-≋ m [] = λ n → refl
insert-≋ m (x ∷ xs) with m ≤? x
... | yes m≤?x = λ n → refl
... | no  m≰?x =
  ≋-trans {m ∷ x ∷ xs}{x ∷ m ∷ xs}{x ∷ insert m xs}
          (≋-perm m x (λ n → refl)
            ∶ m ∷ x ∷ xs ≋ x ∷ m ∷ xs)
          (≋-∷ x (insert-≋ m xs)
            ∶ x ∷ m ∷ xs ≋ x ∷ insert m xs)

--
-- Auxiliaries
--

≰⇒≤ : ∀ {m n} → m ≰ n → n ≤ m
≰⇒≤ m≰n = ≤-pred (≤-steps 1 (≰⇒> m≰n))

insert-< : ∀ {m x xs} → x < m → insert m (x ∷ xs) ≡ x ∷ insert m xs
insert-< {m} {x} {xs} x<m with m ≤? x
... | yes m≤x = ⊥-elim (1+n≰n (begin (x <⟨ x<m ⟩ m ≤⟨ m≤x ⟩ x ∎)))
  where open ≤-Reasoning
... | no  _   = refl

insert-≤∷ : ∀ {m x xs} → x ≤ m → x ≤∷ xs → x ≤∷ insert m xs
insert-≤∷ x≤m [] = [∷] x≤m
insert-≤∷ {m} {x} {n ∷ xs} x≤m ([∷] x≤n) with m ≤? n
... | yes m≤n = [∷] x≤m
... | no  m≰n = [∷] x≤n

insert-sorted : ∀ m xs → Sorted xs → Sorted (insert m xs)
insert-sorted m .[] [] = ⟨ [] ≤∷ [] ⟩
insert-sorted m .(x ∷ xs) (⟨_≤∷_⟩ {x} {xs} x≤∷s s) with m ≤? x
... | yes m≤x = ⟨ [∷] m≤x ≤∷ ⟨ x≤∷s ≤∷ s ⟩ ⟩
... | no  m≰x =
  ⟨  (insert-≤∷ (≰⇒≤ m≰x) x≤∷s  ∶ x ≤∷ insert m xs)
  ≤∷ (insert-sorted m xs s       ∶ Sorted (insert m xs)) ⟩

-- sort

sort : ∀ xs → ∃ λ ys → xs ≋ ys × Sorted ys
sort [] = [] , (λ (x : ℕ) → refl) , []
sort (m ∷ xs) with sort xs
... | ys , xs≋ys , sorted-ys =
  insert m ys ,
  (≋-trans {xs = m ∷ xs} {ys = m ∷ ys} {zs = insert m ys}
           (≋-∷ m xs≋ys) (insert-≋ m ys)
    ∶ m ∷ xs ≋ insert m ys) ,
  (insert-sorted m ys sorted-ys
    ∶ Sorted (insert m ys))

-- insertion-sort

insertion-sort : (xs : List ℕ) → List ℕ
insertion-sort xs = proj₁ (sort xs)

insertion-sort-3251 :
  insertion-sort (3 ∷ 2 ∷ 4 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
insertion-sort-3251 = refl

--
