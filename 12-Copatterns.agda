{-# OPTIONS --copatterns --sized-types #-}

module 12-Copatterns where

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)
open import Size
open import Function
open import Data.Nat
open import Data.List using (List; module List; []; _∷_)
open import Relation.Binary.PropositionalEquality

open import Relation.Binary using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning as Pre

{-
postulate
  Size   : Set
  Size<_ : Size → Set
  ↑_     : Size → Size
  ∞      : Size
-}

data ℕˢ : {i : Size} → Set where
  zero : {i : Size} → ℕˢ {↑ i} 
  suc  : {i : Size} → ℕˢ {i} → ℕˢ {↑ i}

predˢ : {i : Size} → ℕˢ {i} → ℕˢ {i}

predˢ .{↑ i} (zero {i}) = zero {i}
predˢ .{↑ i} (suc {i} n) = n

subˢ : {i : Size} → ℕˢ {i} → ℕˢ {∞} → ℕˢ {i}

subˢ zero n = zero
subˢ (suc m) zero = suc m
subˢ (suc m) (suc n) = suc (subˢ m n)

div : {i : Size} → ℕˢ {i} → ℕˢ → ℕˢ {i}
div zero n = zero
div (suc m) n = suc (div (subˢ m n) n)

data ℕ′ : Size → Set where
  zero : (i : Size) → ℕ′ (↑ i) 
  suc  : (i : Size) → ℕ′ i → ℕ′ (↑ i)

pred′ : (i : Size) → ℕ′ i → ℕ′ i

pred′ .(↑ i) (zero i) = zero i
pred′ .(↑ i) (suc i n) = n

sub′ : (i : Size) → ℕ′ i → ℕ′ ∞ → ℕ′ i

sub′ .(↑ i) (zero i) n = zero i
sub′ .(↑ i) (suc i m) (zero .∞) = suc i m
sub′ .(↑ i) (suc i m) (suc .∞ n) = sub′ i m n

div′ : (i : Size) → ℕ′ i → ℕ′ ∞ → ℕ′ i
div′ .(↑ i) (zero i) n = zero i
div′ .(↑ i) (suc i m) n = suc i (div′ i (sub′ i m n) n)

--
-- Streams
--

infixr 5 _∷_

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : {j : Size< i} → Stream {j} A
open Stream public

map : ∀ {i A B} (f : A → B) (s : Stream {i} A) → Stream {i} B

head (map f s) = f (head s)
tail (map {i} f s) {j} = map {j} f (tail s {j})

zipWith : ∀ {i A B C} (f : A → B → C) → Stream {i} A → Stream {i} B →
            Stream {i} C
head (zipWith f s t) = f (head s) (head t)
tail (zipWith f s t) = zipWith f (tail s) (tail t)

iterate : ∀ {i A} → (f : A → A) → A → Stream A
head (iterate f x) = x
tail (iterate f x) {j} = iterate {j} f (f x)

repeat : ∀ {i A} (a : A) → Stream {i} A

head (repeat a) = a
tail (repeat a) = repeat a

takeˢ : ∀ {A} (n : ℕ) (s : Stream A) → List A
takeˢ zero s = []
takeˢ (suc n) s = (head s) ∷ (takeˢ n (tail s))

zeros : Stream ℕ
head zeros = 0
tail zeros = zeros

nats≥ : ℕ → Stream ℕ
head (nats≥ n) = n
tail (nats≥ n) = nats≥ (suc n)

--
-- Functions on infinite data.
--
-- See map, zipWith, take, repeat, iterate.

5-zeros : takeˢ 5 zeros ≡ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
5-zeros = refl

3-nats≥2 : takeˢ 3 (nats≥ 2) ≡ 2 ∷ 3 ∷ 4 ∷ []
3-nats≥2 = refl

--
-- Bisimilarity
--

infix 4 _∼_

record _∼_ {i : Size} {A : Set} (xs ys : Stream A) : Set where
  coinductive
  constructor _∷_
  field
    ∼head : head xs ≡ head ys
    ∼tail : {j : Size< i} → _∼_ {j} (tail xs) (tail ys)
open _∼_

_∼⟨_⟩∼_ = λ {A} xs i ys → _∼_ {i} {A} xs ys

zeros≡repeat0 : zeros ∼ repeat 0
∼head (zeros≡repeat0) = refl
∼tail (zeros≡repeat0) = zeros≡repeat0

ones : Stream ℕ
head ones = 1
tail ones = ones

5-ones : takeˢ 5 ones ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
5-ones = refl

ones′ : Stream ℕ
ones′ = map suc zeros

5-ones′ : takeˢ 5 ones′ ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
5-ones′ = refl

-- A proof by coinduction (bisimilarity).

{-
 ones ⇒ 1 ∷ ones
 ones′ ⇒ map suc zeros ⇒ map suc (0 ∷ ♯ zeros) ⇒
       ⇒ 1 ∷ ♯ map suc (♭ (♯ zeros)) ⇒ 1 ∷ ♯ map suc zeros
       ⇒ 1 ∷ ♯ ones′
 Hence, ones ∼ ♯ ones′ ⇒ 1 ∷ ones ∼ 1 ∷ ♯ ones′
 and we never obtain differing stream elements. :-)
-}

ones∼ones′ : ones ∼ ones′
∼head ones∼ones′ = refl
∼tail (ones∼ones′) = ones∼ones′

-- More proofs by coinduction

-- map-iterate

map-iterate : {A : Set} (f : A → A) → (x : A) →
              map f (iterate f x) ∼ iterate f (f x)
∼head (map-iterate f x) = refl
∼tail (map-iterate f x) = map-iterate f (f x)

-- map-comp

map-comp : {A B C : Set} (f : A → B) (g : B → C) (xs : Stream A) →
           map g (map f xs) ∼ map (g ∘ f) xs
∼head (map-comp f g xs) = refl
∼tail (map-comp f g xs) = map-comp f g (tail xs)

-- zipWith-cong

zipWith-cong : ∀ {A B C} (_∙_ : A → B → C) {xs xs′ ys ys′} →
  xs ∼ xs′ → ys ∼ ys′ → zipWith _∙_ xs ys ∼ zipWith _∙_ xs′ ys′
∼head (zipWith-cong _∙_ xs∼xs′ ys∼ys′) =
  cong₂ _∙_ (∼head xs∼xs′) (∼head ys∼ys′)
∼tail (zipWith-cong _∙_ xs∼xs′ ys∼ys′) {j} =
  zipWith-cong _∙_ (∼tail xs∼xs′) (∼tail ys∼ys′)

--
-- ∼-reasoning
--
-- ∼ is reflexive, symmetric and transitive
--

∼refl : ∀ {i A} → (xs : Stream A) → xs ∼⟨ i ⟩∼ xs
∼head (∼refl xs) = refl
∼tail (∼refl xs) = ∼refl (tail xs)

∼sym : ∀ {i A} → {xs ys : Stream A} → xs ∼⟨ i ⟩∼ ys → ys ∼⟨ i ⟩∼ xs
∼head (∼sym xs∼ys) = sym (∼head xs∼ys)
∼tail (∼sym xs∼ys) = ∼sym (∼tail xs∼ys)

∼trans : ∀ {i A} → {xs ys zs : Stream A} →
  xs ∼⟨ i ⟩∼ ys → ys ∼⟨ i ⟩∼ zs → xs ∼⟨ i ⟩∼ zs
∼head (∼trans xs∼ys ys∼zs) = trans (∼head xs∼ys) (∼head ys∼zs)
∼tail (∼trans xs∼ys ys∼zs) = ∼trans (∼tail xs∼ys) (∼tail ys∼zs)

--
-- Productivity
--

module fib-bad where

  fib : Stream ℕ
  -- fib = 0 ∷ 1 ∷ zipWith _+_ (tail fib) fib
  head fib = 0
  head (tail fib) = 1
  tail (tail fib) = zipWith _+_ (tail fib) fib

module fib-good where

  fib : {i : Size} → Stream {i} ℕ
  head fib = 0
  head (tail fib) = 1
  tail (tail fib) = zipWith _+_ (tail fib) fib

  5-fib : takeˢ 7 fib ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  5-fib = refl

  fib-correct : fib ∼ 0 ∷ 1 ∷ zipWith _+_ (tail fib) fib
  ∼head fib-correct = refl
  ∼head (∼tail fib-correct {j}) = refl
  ∼tail (∼tail fib-correct {j}) {k} = ∼refl (zipWith _+_ (tail fib) fib)

--
-- ∼-reasoning (a DSL)
--

module ∼-Reasoning′ {A : Set}  where

  infix  2 _□
  infixr 2 _∼⟨_⟩_

  _∼⟨_⟩_ : ∀ xs {ys zs : Stream A} → xs ∼ ys → ys ∼ zs → xs ∼ zs
  _ ∼⟨ xs∼ys ⟩ ys∼zs = ∼trans xs∼ys ys∼zs

  _□ : ∀ (xs : Stream A) → xs ∼ xs
  xs □ = ∼refl xs


ones′∼1∷ones′₁ : ones′ ∼ 1 ∷ ones′
ones′∼1∷ones′₁ =
  ones′
    ∼⟨ ∼refl ones′ ⟩
  map suc zeros
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  map suc (0 ∷ zeros)
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  1 ∷ map suc zeros
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  1 ∷ ones′
  □
  where open ∼-Reasoning′


∼setoid : (i : Size) (A : Set) → Setoid lzero lzero
∼setoid i A = record
  { Carrier       = Stream {∞} A
  ; _≈_           = _∼_ {i}
  ; isEquivalence = record
    { refl  = λ {xs} → ∼refl xs
    ; sym   = ∼sym
    ; trans = ∼trans
    }
  }

module ∼-Reasoning {i : Size} {A : Set} where
  open Pre (Setoid.preorder (∼setoid i A)) public
    renaming (_≈⟨⟩_ to _≡⟨⟩_; _≈⟨_⟩_ to _≡⟨_⟩_; _∼⟨_⟩_ to _∼⟨_⟩_)


ones′∼1∷ones′₂ : ones′ ∼ 1 ∷ ones′
ones′∼1∷ones′₂ = begin
  ones′
    ≡⟨⟩
  map suc zeros
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  map suc (0 ∷ zeros)
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  1 ∷ map suc zeros
    ∼⟨ refl ∷ ∼refl ones′ ⟩
  1 ∷ ones′
  ∎
  where open ∼-Reasoning

--
