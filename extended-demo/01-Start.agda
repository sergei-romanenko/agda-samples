module 01-Start where

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

------------------------------------------------------------
-- Propositional equality (= by definition = by evaluation)
------------------------------------------------------------

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- All values of the type x ≡ y have the form refl :

1≡1 : suc zero ≡ suc zero
1≡1 = refl

-- Or, with implicit arguments:

1≡1′ : suc zero ≡ suc zero
1≡1′ = refl {ℕ} {suc zero}


-------------------------------
-- Curry-Howard correspondence
-------------------------------

-- The above declaration+definition of 1≡1 can be read as follows:

-- Theorem 1≡1. 1 ≡ 1.
-- Proof. By reflexivity of equality.

-- Hence, the idea of "Curry-Howard correspondence":
--
--     type = statement
--     value = proof

-- Any theorem has the form
--     value : type
-- (1) `value` inhabits `type`.
-- (2) `value` is a proof of `type`.

-- Agda's type checker is (sometimes) able to automatically check that
--   value : type

-- A theorem: 2 is a natural number.
-- (This proof looks rather strange...)

2-inhabits-ℕ : ℕ
2-inhabits-ℕ = suc (suc zero)

-- In English.
-- `zero` and `suc` are names of rules and constructors at the same time.
-- (1) zero inhabits ℕ by the rule `zero`
-- (2) (suc zero) inhabits ℕ by (1) and the rule `suc`.
-- (3) (suc (suc zero)) inhabits ℕ by (2) and the rule `suc`.

-- A few theorems about 0 + n.

0+0≡0 : zero + zero ≡ zero
0+0≡0 = refl

0+1≡1 : zero + suc zero ≡ suc zero
0+1≡1 = refl

0+n≡n : (n : ℕ) → zero + n ≡ n
0+n≡n n = refl {ℕ} {n}

-- Quantification! for any n : ℕ the function 0+n≡n generates
-- a specific proof (0+n≡n n) of the fact zero + n ≡ n .

-- What about proving that n + zero ≡ n ?
-- We need a lemma about "congruence".

--
-- Congruence: x ≡ y → f x ≡ f y .
--

cong : {A B : Set} {x y : A} (f : A → B) →
          x ≡ y → f x ≡ f y
cong f refl = refl

-- ⇓ Now, using congruence, let us prove that n + zero ≡ n :

n+0≡n : (n : ℕ) → n + zero ≡ n
n+0≡n zero = refl
n+0≡n (suc n′) = cong suc (n+0≡n n′)

--  ⇑ In English.
-- Let n = zero . Then zero + zero ≡ zero by evaluation + reflexivity.
-- Let n = suc n′ . Then
-- n′ + zero ≡ n′           ⟨ by induction hypothesis ⟩
-- suc (n′ + zero) ≡ suc n′ ⟨ by applying suc to both sides ⟩
-- suc n′ + zero ≡ suc n′   ⟨ since suc n′ + zero evaluates to suc (n′ + zero) ⟩

-- Note that (1) the proof of n′ + zero ≡ n′ is returned by (n+0≡n n′),
-- and (2) suc can be applied to both sides by congruence.

-- ⇓ Now, let us prove that n + suc m ≡ suc (n + m) :

n+sm≡sn+m : (n m : ℕ) → n + suc m ≡ suc (n + m)
n+sm≡sn+m zero m = refl
n+sm≡sn+m (suc n′) m = cong suc (n+sm≡sn+m n′ m)

--
-- Commutativity: n + m ≡ m + n
--

-- A proof (by transitivity):

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

+-comm : (n m : ℕ) → n + m ≡ m + n
+-comm n zero = n+0≡n n
+-comm n (suc m′) =
  --subst (λ z → n + suc m′ ≡ suc z) (+-comm n m′) (n+sm≡sn+m n m′)
  trans (n+sm≡sn+m n m′)
  (trans (+-comm (suc n) m′) (n+sm≡sn+m m′ n))
  where
    prop₂ : n + suc m′ ≡ suc (n + m′)
    prop₂ = n+sm≡sn+m n m′
    prop₁ : n + m′ ≡ m′ + n
    prop₁ = +-comm n m′

-- Another proof (by substitutivity):

--
-- Substitutivity: x ≡ y → P x → P y
--

subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

+-comm′ : (n m : ℕ) → n + m ≡ m + n
+-comm′ n zero = n+0≡n n
+-comm′ n (suc m′) =
  subst (λ z → n + suc m′ ≡ suc z) (+-comm′ n m′) (n+sm≡sn+m n m′)


-- Certainly,

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

---------------------------------------------
-- Induction for ℕ as a general "principle"
---------------------------------------------

-- In Agda this is just a theorem...

ℕ-ind : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind P base step zero = base
ℕ-ind P base step (suc n) = step n (ℕ-ind P base step n)

--------------------------------------------
-- First-order intuitionistic logic in Agda
--------------------------------------------

-- Implication: just P → Q.

P→P : {P Q : Set} → (P → P)
P→P p = p

mp : {P Q : Set} → P → (P → Q) → Q
mp p p→q = p→q p

→-trans : {P Q R : Set} → (P → Q) → (Q → R) → (P → R)
→-trans pq qr = λ p → qr (pq p)

-- Disjunction: A ⊎ B .

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

⊎-intro₁ : {P Q : Set} → P → P ⊎ Q
⊎-intro₁ p = inj₁ p

⊎-intro₂ : {P Q : Set} → Q → P ⊎ Q
⊎-intro₂ q = inj₂ q

⊎-comm : {P Q : Set} → P ⊎ Q → Q ⊎ P
⊎-comm (inj₁ p) = inj₂ p
⊎-comm (inj₂ q) = inj₁ q

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
×-elim₁ (p , q) = p

×-elim₂ : {P Q : Set} → P × Q → Q
×-elim₂ (p , q) = q

×-comm : {P Q : Set} → P × Q → Q × P
×-comm (p , q) = q , p

×⊎-distrib₁ : {P Q R : Set} → P × (Q ⊎ R) → P × Q ⊎ P × R
×⊎-distrib₁ (p , inj₁ q) = inj₁ (p , q)
×⊎-distrib₁ (p , inj₂ r) = inj₂ (p , r)

×⊎-distrib₂ : {P Q R : Set} → (P ⊎ Q) × R → P × R ⊎ Q × R
×⊎-distrib₂ (inj₁ p , r) = inj₁ (p , r)
×⊎-distrib₂ (inj₂ q , r) = inj₂ (q , r)

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
contradict (p , ¬p) = ¬p p

contrapos : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contrapos p→q ¬q p = ¬q (p→q p)

⊥-elim : {Whatever : Set} → ⊥ → Whatever
⊥-elim ()

infix 4 _≢_

_≢_ : {A : Set} (x y : A) → Set
x ≢ y = ¬ (x ≡ y)

-- Totality can be achieved by restricting the domain

total-pred : (n : ℕ) → n ≢ zero → ℕ
total-pred zero 0≢0 = ⊥-elim (0≢0 (refl {ℕ} {zero}))
total-pred (suc n′) _ = n′


{-
-- Even numbers.

data Even : ℕ → Set where
  base  : Even zero
  step : {n : ℕ} → Even n → Even (suc (suc n))

-- Note that `Even` is a function that maps a number to a type.
-- The type of `step` is a "dependent type", since `Even n` depends on `n`.

-- A theorem: 2 is even (= 2 inhabits Even n).

2-is-even : Even (suc (suc zero))
2-is-even = step base

4-is-even : Even (suc (suc (suc (suc zero))))
4-is-even = step (step base)

-- Implicit arguments may be specified, if we like:

4-is-even′ : Even (suc (suc (suc (suc zero))))
4-is-even′ = step {suc (suc zero)} (step {zero} base)
-}



--
