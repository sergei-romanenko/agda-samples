module 01-Start where

-- Emacs Agda-mode cheat sheet:
-- C-C C-L (load file)
-- C-C C-N (evaluate an expression)
-- C-C C-D (type of an expression)
-- C-C C-F (forward to next goal)
-- C-C C-B (back to previous goal)
-- C-C C-T (type of the current goal)
-- C-C C-R (refine the current goal)
-- C-C C-C (case split the current goal)
-- C-C C-A (auto-filling the current goal
--           -l list possible variants
--           -c try case-split
--           -m use constants in scope defined in the module)
-- Unicode entered in pseudo-\LaTeX

-------------------
-- Inductive types
-------------------

data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc :  ℕ → ℕ

-------------
-- Functions
-------------

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

-- Recursive functions

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

-------------------
-- Dependent types
-------------------

infixr 5 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

inner : {n : ℕ} → (xs ys : Vec ℕ n) → ℕ
inner [] [] = zero
-- inner [] (y ∷ ys) = ?
-- inner (x ∷ xs) [] = ?
inner (x ∷ xs) (y ∷ ys) = x * y + inner xs ys

infixr 5 _++_

_++_ : ∀ {m n} {A : Set} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- In general, a dependent type may look like this:
--  f : (x : A) → (y : B x) → C x y
-- where B and C are functions that take arguments and return types.

return-a-type : Bool → Set
return-a-type true = ℕ
return-a-type false = Bool

return-a-value : (x : Bool) → return-a-type x
return-a-value true = zero
return-a-value false = true

-------------------------
-- Totality of functions
-------------------------

-- Given a function f : A → B ,
-- (1) f is applicable to any x : A .
-- (2) f terminates for any x : A .


-- This is ensured by
-- (1) a coverage checker
-- (2) a termination checker

-- f is rejected by the coverage checker:

-- f : ℕ → ℕ
-- f (suc n) = n

-- g is rejected by the termination checker:

-- g : ℕ → ℕ
-- g x = g x

-- Agda can find termination orders across mutually recursive functions.
-- Agda can find lexicographic termination orders.

ack : ℕ → ℕ → ℕ
ack zero n = suc zero
ack (suc m) zero = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

-------------------------------
-- Curry-Howard correspondence
-------------------------------

-- The idea of "Curry-Howard correspondence":
--
--     type  ~ statement
--     value ~ proof

-- Any theorem has the form
--     value : type
-- (1) `value` inhabits `type`.
-- (2) `value` is a proof of `type`.

-- Agda's type checker is (sometimes) able to automatically check that
--   value : type

data Even : ℕ → Set where
  even0 : Even zero
  even2 : {n : ℕ} → Even n → Even (suc (suc n))

-- A theorem: 4 is even.

4-is-even : Even (suc (suc (suc (suc zero))))
4-is-even = even2 (even2 even0)

-- ⇑ In English.
-- `even0` and `even2` are names of rules (and constructors at the same time).
-- (1) zero is even by the rule `even-0`.
-- (2) suc (suc zero) is even by (1) and the rule `even2`.
-- (3) (suc (suc (suc (suc zero)))) is even by (2) and the rule `even2`.

-- ⇓ The same, formally.

4-is-even′ : Even (suc (suc (suc (suc zero))))
4-is-even′ = e4
  where
  e0 : Even zero
  e0 = even0

  e2 : Even (suc (suc zero))
  e2 = even2 e0

  e4 : Even (suc (suc (suc (suc zero))))
  e4  = even2 e2

------------------------------------------------------------
-- Propositional equality (= by definition = by evaluation)
------------------------------------------------------------

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- All values of the type x ≡ y have the form refl :

1≡1 : suc zero ≡ suc zero
1≡1 = {!!}

-- Or, with implicit arguments:

1≡1′ : suc zero ≡ suc zero
1≡1′ = refl {ℕ} {suc zero}

-- The above declaration+definition of 1≡1 can be read as follows:

-- Theorem 1≡1. 1 ≡ 1.
-- Proof. By reflexivity of equality.

-- A few theorems about 0 + n.

0+0≡0 : zero + zero ≡ zero
0+0≡0 = {!!}

0+1≡1 : zero + suc zero ≡ {!!}
0+1≡1 = refl

0+n≡n : (n : ℕ) → zero + n ≡ n
0+n≡n n = refl {ℕ} {n}

-- Quantification! for any n : ℕ the function 0+n≡n generates
-- a specific proof (0+n≡n n) of the fact zero + n ≡ n .

----------------------------------
-- _≡_ is an equivalence relation
----------------------------------

-- Reflexivity trivially holds "by construction":

--refl′ : {A : Set} {x : A} → x ≡ x
--refl′ = refl

-- Symmetry

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym x≡y = {!-c!}

-- Transitivity

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans x≡y y≡z = {! !}

--
-- Congruence: x ≡ y → f x ≡ f y .
--

cong : {A B : Set} {x y : A} (f : A → B) →
          x ≡ y → f x ≡ f y
cong f refl = refl

--
-- ⇓ Now, using congruence, let us prove that n + zero ≡ n :
--

n+0≡n : (n : ℕ) → n + zero ≡ n
n+0≡n zero = refl
n+0≡n (suc n′) = {!!}

--  ⇑ In English.
-- Let n = zero . Then zero + zero ≡ zero by evaluation + reflexivity.
-- Let n = suc n′ . Then
-- n′ + zero ≡ n′           ⟨ by induction hypothesis ⟩
-- suc (n′ + zero) ≡ suc n′ ⟨ by applying suc to both sides ⟩
-- suc n′ + zero ≡ suc n′   ⟨ since suc n′ + zero evaluates to suc (n′ + zero) ⟩

-- Note that (1) the proof of n′ + zero ≡ n′ is returned by (n+0≡n n′),
-- and (2) suc can be applied to both sides by congruence.

-- ⇓ Now, let us prove that n + suc m ≡ suc (n + m) :

+-suc : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc zero m = refl
+-suc (suc n′) m = {!!}

--
-- Commutativity: n + m ≡ m + n
--

-- A proof (by transitivity):

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero = n+0≡n n
+-comm n (suc m′) =
  trans (+-suc n m′)         -- n + suc m′ ≡ suc (n + m′)
        (cong suc (+-comm n m′)) -- suc (n + m′) ≡ suc (m′ + n) ≡ suc m′ + n

----------------------------------------------------------------
-- A DSL for presenting ≡-reasoning in more human-friendly form
----------------------------------------------------------------

module ≡-Reasoning where

  infixr 2 _≡⟨_⟩_
  infix 3 _∎

  _≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : {A : Set} (x : A) → x ≡ x
  x ∎ = refl

-- Now we can rewrite the above proof of +-comm as follows:

+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ n zero = n+0≡n n
+-comm′ n (suc m′) =
   n + suc m′
     ≡⟨ +-suc n m′ ⟩
   suc (n + m′)
     ≡⟨ cong suc (+-comm′ n m′) ⟩
   suc (m′ + n)
     ≡⟨ refl ⟩
   suc m′ + n
   ∎
   where open ≡-Reasoning

---------------------------------------------
-- Induction for ℕ as a general "principle"
---------------------------------------------

-- In Agda this is just a theorem...

ℕ-ind : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind P base step zero = base
ℕ-ind P base step (suc n) = {!step n!}

---------------------------------------
-- Substitutivity: x ≡ y → P x → P y
---------------------------------------

-- In Agda this is a theorem...

subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- Now we can coerse Vec A (n + m) to Vec A (m + n) !

infixr 5 _++′_

_++′_ : ∀ {m n} {A : Set} → Vec A m → Vec A n → Vec A (n + m)
_++′_ {m} {n} {A} xs ys = subst (Vec A) (+-comm m n) (xs ++ ys)

--------------------------------------------
-- First-order intuitionistic logic in Agda
--------------------------------------------

-- Implication: just P → Q.

P→P : {P Q : Set} → (P → P)
P→P p = p

mp : {P Q : Set} → P → (P → Q) → Q
mp p p→q = {!!}

→-trans : {P Q R : Set} → (P → Q) → (Q → R) → (P → R)
→-trans pq qr = {!λ p → ?!}

-- Disjunction: A ⊎ B .

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

⊎-intro₁ : {P Q : Set} → P → P ⊎ Q
⊎-intro₁ p = {!!}

⊎-intro₂ : {P Q : Set} → Q → P ⊎ Q
⊎-intro₂ q = {!!}

⊎-comm : {P Q : Set} → P ⊎ Q → Q ⊎ P
⊎-comm p⊎q = {!-c!}

-- Conjunction: A × B.

infixr 4 _,_
infixr 2 _×_

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → (y : B x) → Σ A B

proj₁ : {A : Set} {B : A → Set} → Σ A B → A
proj₁ (x , y) = x

proj₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (proj₁ p)
proj₂ (x , y) = y

_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)

∃ : {A : Set} (P : A → Set) → Set
∃ = Σ _

×-elim₁ : {P Q : Set} → P × Q → P
×-elim₁ (p , q) = {!!}

×-elim₂ : {P Q : Set} → P × Q → Q
×-elim₂ (p , q) = {!!}

×-comm : {P Q : Set} → P × Q → Q × P
×-comm (p , q) = {!!}

×⊎-distrib₁ : {P Q R : Set} → P × (Q ⊎ R) → P × Q ⊎ P × R
×⊎-distrib₁ (p , inj₁ q) = {!!}
×⊎-distrib₁ (p , inj₂ r) = {!!}

×⊎-distrib₂ : {P Q R : Set} → (P ⊎ Q) × R → P × R ⊎ Q × R
×⊎-distrib₂ (inj₁ p , r) = {!!}
×⊎-distrib₂ (inj₂ q , r) = {!!}

-- Empty type ⊥

data ⊥ : Set where

-- A unit type (a singleton set)

data ⊤ : Set where
  tt : ⊤

-- Negation ¬ A

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

-- Some basic facts about negation

contradict : {P : Set} → ¬ (P × ¬ P)
contradict (p , ¬p) = {!!}

contrapos : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contrapos p→q ¬q p = {!!}

⊥-elim : {Whatever : Set} → ⊥ → Whatever
⊥-elim ()

infix 4 _≢_

_≢_ : {A : Set} (x y : A) → Set
x ≢ y = ¬ (x ≡ y)

-- Totality can be achieved by restricting the domain

total-pred : (n : ℕ) → n ≢ zero → ℕ
total-pred zero 0≢0 = ⊥-elim (0≢0 (refl {ℕ} {zero}))
total-pred (suc n′) _ = n′

------------------------------
-- Existential quantification
------------------------------

-- ∃ λ (x : A) → P x
--  is a shorthand for
-- Σ A P

-- A (silly) theorem:

∃pred : (n : ℕ) → n ≢ zero → ∃ λ m → n ≡ suc m
--∃pred n n≢0 = {!!}
∃pred zero 0≢0 = ⊥-elim (0≢0 refl)
∃pred (suc m) n≢0 = m , refl

-------------------
-- Problem solving
-------------------

open ≡-Reasoning

2+1≡x : ∃ λ x → suc (suc zero) + suc zero ≡ x
2+1≡x = {!!}

m+n≡? : ∀ m n →  ∃ λ x → (m + n ≡ x)
m+n≡? m n = {!!}

2+x≡3 : ∃ λ x → suc (suc zero) + x ≡ suc (suc (suc zero))
2+x≡3 = {!!}

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

m+?≡n : {m n : ℕ} → m ≤ n →  ∃ λ x → (m + x ≡ n)
m+?≡n (z≤n {n}) = n , refl
m+?≡n (s≤s m≤n) with m+?≡n m≤n
... | x , m+x≡n = x , cong suc m+x≡n

--
-- Conclusion
--

-- In Agda:

-- types = values
-- programming = theorem proving
-- testing = theorem proving

-- There can be defined DSLs for writing programs/proofs
-- in human-friendly form.

--
