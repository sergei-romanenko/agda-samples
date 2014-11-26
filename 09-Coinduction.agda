module 09-Coinduction where

open import Function
open import Data.Nat
open import Data.Vec
  renaming (take to takeV; map to mapV; zipWith to zipWithV)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Coinduction

{-

    infix 1000 ♯_

    postulate
      ∞  : (A : Set) → Set
      ♯_ : {A : Set} → A → ∞ A
      ♭  : {A : Set} → ∞ A → A

  ♯ f x is parsed as ♯ (f x)

  ♯_ is "delay".
  ♭ is "force".

  Conceptually:

   ♭ (♯ x) = x

  However, #_ can't be pattern-matched on!
-}

--
-- Streams
--

open import Data.Stream

{-
infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A
-}

zeros : Stream ℕ
zeros =  0 ∷ ♯ zeros

nats≥ : ℕ → Stream ℕ
nats≥ n = n ∷ ♯ nats≥ (suc n)

--
-- Functions on infinite data.
--
-- See map, zipWith, take, repeat, iterate.

5-zeros : take 5 zeros ≡ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
5-zeros = refl

3-nats≥2 : take 3 (nats≥ 2) ≡ 2 ∷ 3 ∷ 4 ∷ []
3-nats≥2 = refl

--
-- Bisimilarity
--

{-

infix 4 _≈_

data _≈_ {A} : Stream A → Stream A → Set where
  _∷_ : ∀ {x y xs ys}
        (x≡ : x ≡ y) (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ y ∷ ys

-}

ones : Stream ℕ
ones = 1 ∷ ♯ ones

ones′ : Stream ℕ
ones′ = map suc zeros

-- A proof by coinduction (bisimilarity).

{-
 ones ⇒ 1 ∷ ones
 ones′ ⇒ map suc zeros ⇒ map suc (0 ∷ ♯ zeros) ⇒
       ⇒ 1 ∷ ♯ map suc (♭ (♯ zeros)) ⇒ 1 ∷ ♯ map suc zeros
       ⇒ 1 ∷ ♯ ones′
 Hence, ones ≈ ♯ ones′ ⇒ 1 ∷ ones ≈ 1 ∷ ♯ ones′
 and we never obtain differing stream elements. :-)
-}

ones≈ones′ : ones ≈ ones′
ones≈ones′ = refl ∷ ♯ ones≈ones′

-- More proofs by coinduction

-- map-iterate

map-iterate : {A : Set} (f : A → A) → (x : A) →
              map f (iterate f x) ≈ iterate f (f x)
map-iterate f x = refl ∷ ♯ map-iterate f (f x)

-- map-comp

map-comp : {A B C : Set} (f : A → B) (g : B → C) (xs : Stream A) →
           map g (map f xs) ≈ map (g ∘ f) xs
map-comp f g (x ∷ xs) = refl ∷ ♯ map-comp f g (♭ xs)

--
-- ≈-reasoning
--
-- ≈ is reflexive, symmetric and transitive
--

≈-refl : ∀ {A} → (xs : Stream A) → xs ≈ xs
≈-refl {A} (x ∷ xs) = refl ∷ ♯ ≈-refl (♭ xs)

≈-sym : ∀ {A} → {xs ys : Stream A} → xs ≈ ys → ys ≈ xs
≈-sym (x≡y ∷ xs≈ys) = sym x≡y ∷ ♯ ≈-sym (♭ xs≈ys)

≈-trans : ∀ {A} → {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans (x≡y ∷ xs≈ys) (y≡z ∷ ys≈zs) =
  trans x≡y y≡z ∷ ♯ (≈-trans (♭ xs≈ys) (♭ ys≈zs))

--
-- Problems with productivity
--

module fib-bad where

  {-# TERMINATING #-}
  fib : Stream ℕ
  fib = 0 ∷ ♯ zipWith _+_ fib (1 ∷ ♯ fib)

module fib-good where

  data StreamP : Set → Set₁ where
    _∷P_ : ∀ {A} (x : A) (xs : ∞ (StreamP A)) → StreamP A
    zipWithP : ∀{A B C} → (f : A → B → C) →
      (xs : StreamP A) (ys : StreamP B) → StreamP C

  data StreamW : Set → Set₁ where
    _∷W_ : ∀ {A} (x : A) (xs : StreamP A) → StreamW A

  zipWithW : ∀ {A B C} → (f : A → B → C) →
    (xs : StreamW A) (ys : StreamW B) → StreamW C
  zipWithW f (x ∷W xs) (y ∷W ys) = (f x y) ∷W zipWithP f xs ys

  whnf : ∀ {A} → StreamP A → StreamW A
  whnf (x ∷P xs) = x ∷W ♭ xs
  whnf (zipWithP f xs ys) = zipWithW f (whnf xs) (whnf ys)

  ⟦_⟧W : ∀ {A} → StreamW A → Stream A
  ⟦_⟧P : ∀ {A} → StreamP A → Stream A

  ⟦ x ∷W xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

  -- fib

  fibP : StreamP ℕ
  fibP = 0 ∷P ♯ zipWithP _+_ fibP (1 ∷P ♯ fibP)

  fib : Stream ℕ
  fib = ⟦ fibP ⟧P

  5-fib : take 7 fib ≡ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  5-fib = refl

  -- zipWith-hom

  zipWith-hom : ∀ {A B C} → (f : A → B → C) →
                  (xs : StreamP A) (ys : StreamP B) →
                  ⟦ zipWithP f xs ys ⟧P ≈ zipWith f ⟦ xs ⟧P ⟦ ys ⟧P
  zipWith-hom f xs ys with whnf xs | whnf ys
  ... | x ∷W xs' | y ∷W ys' =
    refl ∷ ♯ (zipWith-hom f xs' ys')

{-
  zipWith-cong : ∀ {A B C} (_∙_ : A → B → C) {xs xs′ ys ys′} →
    xs ≈ xs′ → ys ≈ ys′ → zipWith _∙_ xs ys ≈ zipWith _∙_ xs′ ys′
-}

  fib-correct : fib ≈ 0 ∷ ♯ zipWith _+_ fib (1 ∷ ♯ fib)
  fib-correct =
    refl ∷ ♯ ≈-trans (zipWith-hom _+_ fibP (1 ∷P ♯ fibP))
                  (zipWith-cong _+_ (≈-refl fib) (refl ∷ ♯ ≈-refl fib))

--
-- ≈-reasoning (a DSL)
--

module ≈-Reasoning-bad {A : Set}  where

  infix  2 _□
  infixr 2 _≈⟨_⟩_

  _≈⟨_⟩_ : ∀ xs {ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
  _ ≈⟨ xs≈ys ⟩ ys≈zs = ≈-trans xs≈ys ys≈zs

  _□ : ∀ (xs : Stream A) → xs ≈ xs
  xs □ = ≈-refl xs

module ≈-Reasoning-bad-test {A : Set}  where

-- Doesn't work... Here Agda is unable to prove productivity...

  {-# TERMINATING #-}
  ones≈ones′₁ : ones ≈ ones′
  ones≈ones′₁ =
    ones
      ≈⟨ refl ∷ ♯ ≈-refl ones ⟩
    1 ∷ ♯ ones
      ≈⟨ refl ∷ ♯ ones≈ones′₁ ⟩
    1 ∷ ♯ ones′
      ≈⟨ refl ∷ ♯ ≈-refl ones′ ⟩
    1 ∷ ♯ map suc zeros
      ≈⟨ refl ∷ ♯ ≈-refl ones′ ⟩
    map suc (0 ∷ ♯ zeros)
      ≈⟨ refl ∷ ♯ ≈-refl ones′ ⟩
    map suc zeros
      ≈⟨ ≈-refl ones′ ⟩
    ones′ □
    where open ≈-Reasoning-bad

module ≈-Reasoning  where

  infix 4 _≈P_ _≈W_
  infixr 5 _∷_
  infix  3 _□
  infixr 2 _≈⟨_⟩_

  data _≈P_ {A : Set} : Stream A → Stream A → Set where
    _∷_ : ∀ {x y xs ys} (x≡y : x ≡ y) →
      (xs≈ys : ∞ (♭ xs ≈P ♭ ys)) → x ∷ xs ≈P y ∷ ys
    _≈⟨_⟩_ : ∀ (xs : Stream A) {ys zs}
      (xs≈ys : xs ≈P ys) → (ys≈zs : ys ≈P zs) → xs ≈P zs
    _□ : ∀ (xs : Stream A) → xs ≈P xs

  data _≈W_ {A : Set} : Stream A → Stream A → Set where
    _∷_ : ∀ {x y xs ys} (x≡y : x ≡ y)
      (xs≈ys : ♭ xs ≈P ♭ ys) → x ∷ xs ≈W y ∷ ys

  -- Completeness

  completeP : {A : Set} {xs ys : Stream A} → xs ≈ ys → xs ≈P ys
  completeP (x≡y ∷ xs≈ys) = x≡y ∷ ♯ (completeP (♭ xs≈ys))

  -- Weak head normal forms

  transW : {A : Set} {xs ys zs : Stream A} →
              xs ≈W ys → ys ≈W zs → xs ≈W zs
  transW {A} {x ∷ xs} (x≡y ∷ xs≈ys) (y≡z ∷ ys≈zs) =
    trans x≡y y≡z ∷ (♭ xs ≈⟨ xs≈ys ⟩ ys≈zs)

  reflW : {A : Set} (xs : Stream A) → xs ≈W xs
  reflW (x ∷ xs) = refl ∷ (♭ xs □)

  whnf : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈W ys
  whnf {A} {x ∷ xs} {y ∷ ys} (x≡y ∷ xs≈ys) = x≡y ∷ ♭ xs≈ys
  whnf (xs ≈⟨ xs≈ys ⟩ ys≈zs) = transW (whnf xs≈ys) (whnf ys≈zs)
  whnf ((x ∷ xs) □) = refl ∷ (♭ xs □)

  -- Soundness

  soundW : {A : Set} {xs ys : Stream A} → xs ≈W ys → xs ≈ ys
  soundP : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈ ys

  soundW (x≡y ∷ xs≈ys) = x≡y ∷ ♯ (soundP xs≈ys)
  soundP xs≈ys = soundW (whnf xs≈ys)

module ≈-Reasoning-test {A : Set}  where

  open ≈-Reasoning

  ones≈ones′₁ : ones ≈P ones′
  ones≈ones′₁ =
    ones
      ≈⟨ refl ∷ ♯ (ones □) ⟩
    1 ∷ ♯ ones
      ≈⟨ refl ∷ ♯ ones≈ones′₁ ⟩
    1 ∷ ♯ ones′
      ≈⟨ refl ∷ ♯ (ones′ □) ⟩
    1 ∷ ♯ map suc zeros
      ≈⟨ refl ∷ ♯ (ones′ □) ⟩
    map suc (0 ∷ ♯ zeros)
      ≈⟨ refl ∷ ♯ (ones′ □) ⟩
    map suc zeros
      ≈⟨ ones′ □ ⟩
    ones′ □


--
