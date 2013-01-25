--
-- Small-step Operational Semantics
--

{-
  Based on

    Software Foundations
    by Benjamin C. Pierce, ...
    http://www.cis.upenn.edu/~bcpierce/sf/

  and

    Liyang Hu and Graham Hutton.
    Compiling concurrency correctly: cutting out the middle man.
    Trends in Functional Programming volume 10 (Zoltan Horvath and
    Viktoria Zsok, editors), Intellect, September 2010.
    Selected papers from the Tenth Symposium on Trends in Functional
    Programming, Komarno, Slovakia, June 2009. 
-}

module 11-SmallStep where

open import Data.Nat
open import Data.Product
  renaming (map to map×)
open import Data.Sum
  renaming (map to map⊎)
open import Data.Empty

open import Data.Star

open import Function

open import Function.Equivalence
  using (_⇔_; equivalence)

open import Relation.Nullary
open import Relation.Binary
  using (Rel)
open import Relation.Binary.PropositionalEquality

--
-- A Toy Language
--

infixl 6 _⊕_

data Tm : Set where
  val : (n : ℕ) → Tm
  _⊕_  : (t₁ t₂ : Tm) → Tm

module BigStepEvalFn where

  -- Big-step evaluator

  eval : (t : Tm) → ℕ
  eval (val n) = n
  eval (t₁ ⊕ t₂) = eval t₁ + eval t₂

module BigStepEvalRel where

  -- Big-step evaluation relation

  infix 3 _⇓_

  data _⇓_ : Tm → ℕ → Set where
    e-const : ∀ {n} →
      val n ⇓ n
    e-plus : ∀ {t₁ t₂ n₁ n₂} →
      t₁ ⇓ n₁ →
      t₂ ⇓ n₂ →
      t₁ ⊕ t₂ ⇓ n₁ + n₂

module BigStep-FnRel-Equiv where
  open BigStepEvalFn
  open BigStepEvalRel

  -- Equivalence of the two big-step semantics

  fn⇒rel : ∀ {t n} → eval t ≡ n  → t ⇓ n
  fn⇒rel {val n} refl = e-const
  fn⇒rel {t₁ ⊕ t₂} refl =
    e-plus (fn⇒rel refl) (fn⇒rel refl)

  rel⇒eval : ∀ {t n} → t ⇓ n → eval t ≡ n
  rel⇒eval e-const = refl
  rel⇒eval (e-plus h₁ h₂)
    rewrite rel⇒eval h₁ | rel⇒eval h₂
    = refl

  fn⇔rel : ∀ {t n} → (eval t ≡ n) ⇔ (t ⇓ n)
  fn⇔rel {t} = equivalence fn⇒rel rel⇒eval

  -- fn⇒rel without `refl`

  fn⇒rel′ : ∀ t → t ⇓ (eval t)
  fn⇒rel′ (val n) = e-const
  fn⇒rel′ (t₁ ⊕ t₂) = e-plus (fn⇒rel′ t₁) (fn⇒rel′ t₂)

  fn⇒rel′′ : ∀ {t n} → (eval t ≡ n) → (t ⇓ n)
  fn⇒rel′′ {t} {n} = λ et≡n → subst (λ m → t ⇓ m) et≡n (fn⇒rel′ t)

  -- rel⇒eval without `rewrite`

  rel⇒eval′ : ∀ {t n} → t ⇓ n  → eval t ≡ n
  rel⇒eval′ e-const = refl
  rel⇒eval′ (e-plus {t₁} {t₂} {n₁} {n₂} h₁ h₂)
    with rel⇒eval′ h₁ | rel⇒eval′ h₂
  ... | et₁≡n₁ | et₂≡n₂ =
    subst₂ (λ x y → x + y ≡ n₁ + n₂) (sym et₁≡n₁) (sym et₂≡n₂)
           refl

  -- rel⇒eval without `subst₂`

  rel⇒eval′′ : ∀ {t n} → t ⇓ n  → eval t ≡ n
  rel⇒eval′′ e-const = refl
  rel⇒eval′′ (e-plus {t₁} {t₂} {n₁} {n₂} h₁ h₂)
    with eval t₁ | rel⇒eval′′ h₁ | eval t₂ | rel⇒eval′′ h₂
  ...  | .n₁     | refl          | .n₂     | refl
    = refl

module BigStepEvalRel-Val where

  -- Big-step evaluation relation

  infix 3 _⇓_

  data _⇓_ : Tm → Tm → Set where
    e-const : ∀ {n} →
      val n ⇓ val n
    e-plus : ∀ {t₁ t₂ n₁ n₂} →
      (h₂ : t₁ ⇓ val n₁) →
      (h₂ : t₂ ⇓ val n₂) →
      t₁ ⊕ t₂ ⇓ val (n₁ + n₂)

module SimpleArith2 where

  -- Small-step evaluation relation

  infix 3 _⇒_

  data _⇒_ : Tm → Tm → Set where
    n+n : ∀ {n₁ n₂} →
      val n₁ ⊕ val n₂ ⇒ val (n₁ + n₂)
    r+t : ∀ {t₁ t′₁ t₂} →
      (t₁⇒ : t₁ ⇒ t′₁) →
      t₁ ⊕ t₂ ⇒ t′₁ ⊕ t₂
    n+r : ∀ {n₁ t₂ t′₂} →
      (t₂⇒ : t₂ ⇒ t′₂) →
      val n₁ ⊕ t₂ ⇒ val n₁ ⊕ t′₂

  test-step-1 :
    (val 0 ⊕ val 3) ⊕ (val 2 ⊕ val 4)
      ⇒
    val (0 + 3) ⊕ (val 2 ⊕ val 4)

  test-step-1 = r+t n+n

  test-step-2 :
    val 0 ⊕ (val 2 ⊕ (val 0 ⊕ val 3))
      ⇒
    (val 0) ⊕ (val 2 ⊕ val (0 + 3))
  test-step-2 = n+r (n+r n+n)

  -- ⇒ is deterministic

  ⇒-det : ∀ {t t′ t′′} → t ⇒ t′ → t ⇒ t′′ → t′ ≡ t′′
  ⇒-det n+n n+n = refl
  ⇒-det n+n (r+t ())
  ⇒-det n+n (n+r ())
  ⇒-det (r+t ()) n+n
  ⇒-det (r+t t₁⇒) (r+t t₁⇒′) rewrite ⇒-det t₁⇒ t₁⇒′ = refl
  ⇒-det (r+t ()) (n+r t₂⇒)
  ⇒-det (n+r ()) n+n
  ⇒-det (n+r t₂⇒) (r+t ())
  ⇒-det (n+r t₂⇒) (n+r t₂⇒') rewrite ⇒-det t₂⇒ t₂⇒' = refl

--
-- Values
--

data value : Tm → Set where
  v-c : ∀ {n} → value (val n)

infix 3 _⇒_

data _⇒_ : Tm → Tm → Set where
  n+n : ∀ {n₁ n₂} →
    val n₁ ⊕ val n₂ ⇒ val (n₁ + n₂)
  r+t : ∀ {t₁ t′₁ t₂} →
    (t₁⇒ : t₁ ⇒ t′₁) →
    t₁ ⊕ t₂ ⇒ t′₁ ⊕ t₂
  n+r : ∀ {t₁ t₂ t′₂} →
    value t₁ →
    (t₂⇒ : t₂ ⇒ t′₂) →
    t₁ ⊕ t₂ ⇒ t₁ ⊕ t′₂

test-step-2 :
  val 0 ⊕ (val 2 ⊕ (val 0 ⊕ val 3))
    ⇒
  val 0 ⊕ (val 2 ⊕ (val (0 + 3)))
test-step-2 = n+r v-c (n+r v-c n+n)

n-of-value : ∀ {t} → (v : value t) → ∃ λ n → val n ≡ t
n-of-value (v-c {n}) = n , refl

_+V+_ : ∀ {t₁ t₂} → (v₁ : value t₁) → (v₂ : value t₂) →
         ∃ λ t′ → t₁ ⊕ t₂ ⇒ t′
v-c {n₁} +V+ v-c {n₂} = val (n₁ + n₂) , n+n

-- Determinism

⇒-det : ∀ {t t′ t′′} → t ⇒ t′ → t ⇒ t′′ → t′ ≡ t′′
⇒-det n+n n+n = refl
⇒-det n+n (r+t ())
⇒-det n+n (n+r v-c ())
⇒-det (r+t ()) n+n
⇒-det (r+t t₁⇒) (r+t t₁⇒') rewrite ⇒-det t₁⇒ t₁⇒' = refl
⇒-det (r+t ()) (n+r v-c t₂⇒)
⇒-det (n+r v-c ()) n+n
⇒-det (n+r v-c t₂⇒) (r+t ())
⇒-det (n+r _ t₂⇒) (n+r _ t₂⇒') rewrite ⇒-det t₂⇒ t₂⇒' = refl

--
-- Strong Progress and Normal Forms
--

strong-progress : ∀ t → value t ⊎ (∃ λ t' → t ⇒ t')
strong-progress (val n) = inj₁ v-c
strong-progress (t₁ ⊕ t₂) =
  inj₂ (helper (strong-progress t₁) (strong-progress t₂))
  where
    helper : value t₁ ⊎ (∃ λ t' → t₁ ⇒ t') →
             value t₂ ⊎ (∃ λ t' → t₂ ⇒ t') →
             ∃ (λ t′ → t₁ ⊕ t₂ ⇒ t′)
    helper (inj₁ v₁) (inj₁ v₂) = v₁ +V+ v₂
    helper (inj₁ v₁) (inj₂ (t′₂ , t₂⇒t′₂)) = t₁ ⊕ t′₂ , n+r v₁ t₂⇒t′₂
    helper (inj₂ (t′₁ , t₁⇒t′₁)) q = t′₁ ⊕ t₂ , r+t t₁⇒t′₁

normal-form : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) (t : X) → Set ℓ
normal-form R t = ∄ (λ t' → R t t')

value-is-nf : ∀ t → value t → normal-form _⇒_ t
value-is-nf .(val n) (v-c {n}) (t′ , ())

nf-is-value : ∀ t → normal-form _⇒_ t → value t
nf-is-value t ¬t⇒t′ with strong-progress t
... | inj₁ v = v
... | inj₂ (t′ , t⇒t′) = ⊥-elim (¬t⇒t′ (t′ , t⇒t′))

nf-same-as-value : ∀ t → normal-form _⇒_ t ⇔ value t
nf-same-as-value t = equivalence (nf-is-value t) (value-is-nf t)

--
-- Multi-Step Reduction
--

infix 3 _⇒*_

_⇒*_ : (t t′ : Tm) → Set
_⇒*_ = Star _⇒_

test-⇒*-1 :
  (val 0 ⊕ val 3) ⊕ (val 2 ⊕ val 4)
    ⇒*
  val ((0 + 3) + (2 + 4))
test-⇒*-1 = r+t n+n ◅ n+r v-c n+n ◅ n+n ◅ ε

test-⇒*-2 :
  val 3 ⇒* val 3
test-⇒*-2 = ε

test-⇒*-3 :
  val 0 ⊕ val 3
    ⇒*
  val 0 ⊕ val 3
test-⇒*-3 = ε

test-⇒*-4 :
  val 0 ⊕ (val 2 ⊕ (val 0 ⊕ val 3))
    ⇒*
  val 0 ⊕ (val (2 + (0 + 3)))
test-⇒*-4 = n+r v-c (n+r v-c n+n) ◅ n+r v-c n+n ◅ ε

--
-- Normal Forms Again
--

_has-normal-form_ : (t t' : Tm) → Set
t has-normal-form t′ = t ⇒* t′ × normal-form _⇒_ t′

normal-forms-unique : ∀ {t t′ t′′} →
  t has-normal-form t′ → t has-normal-form t′′ →
  t′ ≡ t′′
normal-forms-unique (t⇒*t′ , ¬t′⇒) (t⇒*t′′ , ¬t′′⇒) =
  helper t⇒*t′ ¬t′⇒ t⇒*t′′ ¬t′′⇒
  where
    helper : ∀ {t t′ t′′} →
               t ⇒* t′ → ∄ (λ u → t′ ⇒ u) →
               t ⇒* t′′ → ∄ (λ u → t′′ ⇒ u) →
               t′ ≡ t′′
    helper ε ¬t′⇒ ε ¬t′′⇒ = refl
    helper {t′′ = t′′} ε ¬t′⇒ (t′⇒ ◅ ⇒t′′) ¬t′′⇒ =
      ⊥-elim (¬t′⇒ (_ , t′⇒))
    helper {t′′ = t′′} (t′′⇒ ◅ ⇒*t′) ¬t′⇒ ε ¬t′′⇒ =
      ⊥-elim (¬t′′⇒ (_ , t′′⇒))
    helper (t⇒₁ ◅ ⇒*t′) ¬t′⇒ (t⇒₂ ◅ ⇒*t′′) ¬t′′⇒
      rewrite ⇒-det t⇒₁ t⇒₂
      = helper ⇒*t′ ¬t′⇒ ⇒*t′′ ¬t′′⇒


normalizing : ∀ {ℓ} {X : Set ℓ} (R : Rel X ℓ) → Set ℓ
normalizing {X} R =
  ∀ t → ∃ (λ t' → Star R t t' × normal-form R t')


⇒*-congr-1 : ∀ {t₁ u t₂} →
               t₁ ⇒* u →
               t₁ ⊕ t₂ ⇒* u ⊕ t₂
⇒*-congr-1 ε = ε
⇒*-congr-1 {t₁} {u} {t₂} (t₁⇒ ◅ ⇒*u) = (r+t t₁⇒) ◅ (⇒*-congr-1 ⇒*u)

⇒*-congr-2 : ∀ {t₁ t₂ u} →
               value t₁ →
               t₂ ⇒* u →
               t₁ ⊕ t₂ ⇒* t₁ ⊕ u
⇒*-congr-2 v-c ε = ε
⇒*-congr-2 v-c (t₂⇒ ◅ ⇒*u) = (n+r v-c t₂⇒) ◅ (⇒*-congr-2 v-c ⇒*u)

⇒-normalizing : normalizing _⇒_
-- ∀ t → ∃ λ u → (t ⇒* u) × ∄ (λ u′ → u ⇒ u′)
⇒-normalizing (val n) =
  (val n) , ε , value-is-nf (val n) v-c
⇒-normalizing (t₁ ⊕ t₂) with ⇒-normalizing t₁ | ⇒-normalizing t₂
... | u₁ , t₁⇒*u₁ , ¬u₁⇒ | u₂ , t₂⇒*u₂ , ¬u₂⇒
  with n-of-value (nf-is-value u₁ ¬u₁⇒) | n-of-value (nf-is-value u₂ ¬u₂⇒)
... | n₁ , t-n₁≡u₁ | n₂ , t-n₂≡u₂ =
  u , t⇒*u , value-is-nf u v-c
  where
    u = val (n₁ + n₂)

    t⇒*u₁u₂ : t₁ ⊕ t₂ ⇒* u₁ ⊕ u₂
    t⇒*u₁u₂ =
      (⇒*-congr-1 t₁⇒*u₁) ◅◅
        (⇒*-congr-2 (nf-is-value u₁ ¬u₁⇒) t₂⇒*u₂)

    u₁u₂⇒u : u₁ ⊕ u₂ ⇒ val (n₁ + n₂)
    u₁u₂⇒u = subst₂
      (λ x y → x ⊕ y ⇒ (val (n₁ + n₂)))
      t-n₁≡u₁ t-n₂≡u₂
      n+n

    t⇒*u : t₁ ⊕ t₂ ⇒* val (n₁ + n₂)
    t⇒*u = t⇒*u₁u₂ ◅◅ (u₁u₂⇒u ◅ ε)

--
-- Equivalence of Big-Step and Small-Step Reduction
--

open BigStepEvalRel-Val

big⇒value : ∀ {t₁ t₂} → t₁ ⇓ t₂ → value t₂
big⇒value e-const = v-c
big⇒value (e-plus h₁ h₂) = v-c

big⇒small* : ∀ {t v} → t ⇓ v → t ⇒* v
big⇒small* e-const = ε
big⇒small* (e-plus {t₁} {t₂} {n₁} {n₂} h₁ h₂)
  with big⇒small* h₁ | big⇒small* h₂
... | t₁⇒*v₁ | t₂⇒*v₂ =
  (⇒*-congr-1 t₁⇒*v₁) ◅◅
    (⇒*-congr-2 v-c t₂⇒*v₂) ◅◅
      (n+n ◅ ε)

small⇒big : ∀ {t t' v} → t ⇒ t' → t' ⇓ v → t ⇓ v
small⇒big n+n e-const = e-plus e-const e-const
small⇒big (r+t t₁⇒) (e-plus h₁ h₂) =
  e-plus (small⇒big t₁⇒ h₁) h₂
small⇒big (n+r v-c t₂⇒) (e-plus h₁ h₂) =
  e-plus h₁ (small⇒big t₂⇒ h₂)


nf⇒big′ : ∀ {t v} → t ⇒* v → ∄ (λ u → v ⇒  u) → t ⇓ v
nf⇒big′ {t} {v} t⇒*v h with nf-is-value v h
nf⇒big′ ε h | v-c = e-const
nf⇒big′ (t⇒t′ ◅ t′⇒*v) h | v-c {n} =
  small⇒big t⇒t′ (nf⇒big′ t′⇒*v h)

nf⇒big : ∀ {t v} → t has-normal-form v → t ⇓ v
nf⇒big (t⇒*v , h) = nf⇒big′ t⇒*v h

big⇒nf : ∀ {t v} → t ⇓ v → t has-normal-form v
big⇒nf {t} {v} h =
  big⇒small* h , value-is-nf v (big⇒value h)

nf⇔big : ∀ {t v} → (t has-normal-form v) ⇔ (t ⇓ v)
nf⇔big = equivalence nf⇒big big⇒nf


--
