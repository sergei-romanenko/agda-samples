{-# OPTIONS --copatterns #-}

{-
See the papers

* Andreas Abel, Brigitte Pientka, David Thibodeau, and Anton Setzer. 2013.
  Copatterns: programming infinite structures by observations.
  In Proceedings of the 40th annual ACM SIGPLAN-SIGACT symposium
  on Principles of programming languages (POPL '13).
  ACM, New York, NY, USA, 27-38. DOI=10.1145/2429069.2429075
  http://doi.acm.org/10.1145/2429069.2429075

* Andreas M. Abel and Brigitte Pientka. 2013.
  Wellfounded recursion with copatterns: a unified approach to termination
  and productivity.
  In Proceedings of the 18th ACM SIGPLAN international conference
  on Functional programming (ICFP '13).
  ACM, New York, NY, USA, 185-196. DOI=10.1145/2500365.2500591
  http://doi.acm.org/10.1145/2500365.2500591
-}

module 12-Copatterns where

open import Level public
  using (Level) renaming (zero to lzero; suc to lsuc)
open import Size
open import Function
open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Data.List as List using (List; module List; []; _∷_)
open import Data.Empty
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality

open import Relation.Binary using (Setoid; module Setoid)

import Relation.Binary.PreorderReasoning as Pre

--
-- "Sizes" and "sized types".
--

{-
postulate
  Size   : Set
  Size<_ : Size → Set
  ↑_     : Size → Size
  ∞      : Size
-}


-- Equality of sizes

s≡s : (s : Size) → s ≡ s
s≡s s = refl

↑≡↑ : (s : Size) → ↑ s ≡ ↑ s
↑≡↑ s = refl

↑∞≡∞ : ↑ ∞ ≡ ∞
↑∞≡∞ = refl

↑≡∞ : (s : Size) → ↑ s ≡ ∞ → s ≡ ∞
↑≡∞ .∞ refl = refl

--
-- "Less then" for sizes
--
-- (i : Size) (j : Size< i) → ...
--
-- i ≤ ↑ i ≤ ∞
-- A constraint solver for a set of inequalities x + n ≤ y, x ≤ y + m .
-- Subtyping: T {i} ≤ T {↑ i} ≤ T {∞}
--

--
-- Values can be instrumented with "sizes".
--

data ℕˢ : {i : Size} → Set where
  zero : {i : Size} → ℕˢ {↑ i} 
  suc  : {i : Size} → ℕˢ {i} → ℕˢ {↑ i}

predˢ : {i : Size} → ℕˢ {i} → ℕˢ {i}

predˢ zero = zero
predˢ (suc n) = n

subˢ : {i : Size} → ℕˢ {i} → ℕˢ {∞} → ℕˢ {i}

subˢ zero n = zero
subˢ (suc m) zero = suc m
subˢ (suc m) (suc n) = suc (subˢ m n)

-- Now the compiler is able to understand
-- that the first argument becomes smaller.
-- `m` is smaller than `suc m`, and
-- the size of `subˢ m n`is the same as than of `m`.

divˢ : {i : Size} → ℕˢ {i} → ℕˢ → ℕˢ {i}
divˢ zero n = zero
divˢ (suc m) n = suc (divˢ (subˢ m n) n)

--
-- Let's make the sizes visible,
-- to see what really happens with them.
--

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
-- A more abstract approach.
-- What really matters for sizes?
-- Just to become "smaller"!
--

data ℕ′′ (i : Size) : Set where
  zero : ℕ′′ i 
  suc  : (j : Size< i) → ℕ′′ j → ℕ′′ i

pred′′ : (i : Size) → ℕ′′ i → ℕ′′ i

pred′′ i zero = zero
pred′′ i (suc j n) = n

sub′′ : (i : Size) → ℕ′′ i → ℕ′′ ∞ → ℕ′′ i

sub′′ i zero n = zero
sub′′ i (suc j m) zero = suc j m
sub′′ i (suc j m) (suc ∞ n) = sub′′ j m n

--
-- Copatterns: a way to implement "virtual functions".
--

record Animal : Set where
  field
    color  : String
    nature : String

  response : String → String
  response name =
    "Hello, " ++ name ++ "! I'm " ++ color ++ " and " ++ nature ++ "!"

open Animal

frog : Animal
color  frog = "green"
nature frog = "good"

askFrog : response frog "human" ≡ "Hello, human! I'm green and good!"
askFrog = refl

dog : Animal
color  dog = "black"
nature dog = "bad"

askDog : response dog "beast" ≡ "Hello, beast! I'm black and bad!"
askDog = refl

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

interleave : ∀ {i A} (xs ys : Stream {i} A) → Stream {i} A
head (interleave xs ys) = head xs
tail (interleave {i} xs ys) {j} = interleave {j} ys (tail xs)

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
 ones′ ⇒ map suc zeros ⇒ map suc (0 ∷ zeros) ⇒
       ⇒ 1 ∷ map suc zeros ⇒ 1 ∷ map suc zeros
       ⇒ 1 ∷ ones′
 Hence, ones ∼ ones′ ⇒ 1 ∷ ones ∼ 1 ∷ ones′
 and we never obtain differing stream elements. :-)
-}

ones∼ones′ : ones ∼ ones′
∼head ones∼ones′ = refl
∼tail (ones∼ones′) = ones∼ones′

-- More proofs by coinduction

-- map-iterate

map-iterate : ∀ {i} {A : Set} (f : A → A) (x : A) →
              map f (iterate f x) ∼⟨ i ⟩∼ iterate f (f x)
∼head (map-iterate f x) = refl
∼tail (map-iterate f x) = map-iterate f (f x)

-- map-comp

map-comp : ∀ {i} {A B C : Set} (f : A → B) (g : B → C) (xs : Stream A) →
           map g (map f xs) ∼⟨ i ⟩∼ map (g ∘ f) xs
∼head (map-comp f g xs) = refl
∼tail (map-comp f g xs) = map-comp f g (tail xs)

--
-- Congruence
--

head-cong : ∀ {i A} {xs ys : Stream A} → xs ∼⟨ i ⟩∼ ys → head xs ≡ head ys
head-cong xs∼ys = ∼head xs∼ys

tail-cong :
  ∀ {i} {j : Size< i} {A} {xs ys : Stream A} →
    xs ∼⟨ i ⟩∼ ys → tail xs ∼⟨ j ⟩∼ tail ys
tail-cong xs∼ys = ∼tail xs∼ys

-- map-cong

map-cong : ∀ {i A B} {xs ys : Stream A} (f : A → B) →
  xs ∼⟨ i ⟩∼ ys → map f xs ∼⟨ i ⟩∼ map f ys
∼head (map-cong f xs∼ys) = cong f (∼head xs∼ys)
∼tail (map-cong f xs∼ys) {j} = map-cong f (∼tail xs∼ys)

-- zipWith-cong

zipWith-cong : ∀ {i A B C} (_∙_ : A → B → C) {xs xs′ ys ys′} →
  xs ∼⟨ i ⟩∼ xs′ → ys ∼⟨ i ⟩∼ ys′ → zipWith _∙_ xs ys ∼⟨ i ⟩∼ zipWith _∙_ xs′ ys′
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
  ∼head (∼tail fib-correct) = refl
  ∼tail (∼tail fib-correct) = ∼refl (zipWith _+_ (tail fib) fib)

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
-- Colists
--

mutual

  data Colist {i : Size} (A : Set) : Set where
    [] : Colist {i} A
    _∷_ : (x : A) (xs : ∞Colist {i} A) → Colist {i} A

  record ∞Colist {i : Size} (A : Set) : Set where
    coinductive
    field
      colist♭ : {j : Size< i} → Colist {j} A

open ∞Colist

mutual

  mapColist : ∀ {i A B} (f : A → B) (xs : Colist {i} A) → Colist {i} B

  mapColist f [] = []
  mapColist f (x ∷ xs) = (f x) ∷ mapColist♯ f xs

  mapColist♯ : ∀ {i A B} (f : A → B) (xs : ∞Colist {i} A) → ∞Colist {i} B

  colist♭ (mapColist♯ f xs) = mapColist f (colist♭ xs)

append : ∀ {i A} → List A → ∞Colist {i} A → ∞Colist {i} A

colist♭ (append [] ys) = colist♭ ys
colist♭ (append (x ∷ xs) ys) = x ∷ append xs ys

-- Trees

module Trees where

  record Tree {i : Size} (A : Set) : Set where
    coinductive
    field
      label : A
      children : {j : Size< i} → List (Tree {j} A)
  open Tree

  -- Breadth-first traversal

  bf : ∀ {i A} → List (Tree {i} A) → ∞Colist {i} A

  colist♭ (bf []) = []
  colist♭ (bf {i} (t ∷ ts)) {j} =
    label t ∷ append (List.map label ts)
                     (bf {j} (List.concatMap (λ t′ → children t′ {j}) (t ∷ ts)))

--
-- Binary trees
--

module BTrees where

  record TreeC (A : Set) : Set where
    coinductive
    field 
      labelC : A
      childL : TreeC A
      childR : TreeC A
  open TreeC

  repeatC : ∀ {A} (a : A) → TreeC A
  labelC (repeatC a) = a
  childL (repeatC a) = repeatC a
  childR (repeatC a) = repeatC a

  collectC : ∀ {A} → List Bool → TreeC A → List A
  collectC []       t = []
  collectC (true  ∷ bs) t = labelC t ∷ collectC bs (childL t)
  collectC (false ∷ bs) t = labelC t ∷ collectC bs (childR t)

  swapC : ∀ {A} → TreeC A → TreeC A
  labelC (swapC t) = labelC t
  childL (swapC t) = swapC (childR t)
  childR (swapC t) = swapC (childL t)
  
  mapC : ∀ {A B} → (f : A → B) → TreeC A → TreeC B
  labelC (mapC f t) = f (labelC t)
  childL (mapC f t) = mapC f (childL t)
  childR (mapC f t) = mapC f (childR t)

  record TreeB (A : Set) : Set where
    coinductive
    field 
      label : A
      child : Bool -> TreeB A
  open TreeB

  collect : ∀ {A} → List Bool → TreeB A → List A
  collect []       t = []
  collect (b ∷ bs) t = label t ∷ collect bs (child t b)

  swap : ∀ {A} → TreeB A → TreeB A
  label (swap t) = label t
  child (swap t) true  = swap (child t false)
  child (swap t) false = swap (child t true)

  alternate : {A : Set} (x y : A) → TreeB A
  label (alternate x y) = x
  child (alternate x y) b = alternate y x

--
