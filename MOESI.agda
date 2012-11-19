module MOESI where

open import Data.Nat
open import Relation.Nullary using (¬_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Function using (_∘_)

infixr 4 _,_,_,_,_

data State : Set where
  _,_,_,_,_ : (i m s e o : ℕ) → State

data MOESI : State → Set where
  t1 : ∀ {i} →
     MOESI (i , 0 , 0 , 0 , 0)
  t2 : ∀ {i m s e o} →
     MOESI (suc i , m , s , e , o) → MOESI (i , 0 , suc (s + e) , 0 , m + o)
  t3 : ∀ {i m s e o} →
     MOESI (i , m , s , suc e , o) → MOESI (i , suc m , s , e , o)
  t4 : ∀ {i m s e o} →
     MOESI (i , m , suc s , e , o) →
       MOESI (i + m + s + e + o , 0 , 0 , suc 0 , 0)
  t5 : ∀ {i m s e o} →
     MOESI (suc i , m , s , e , o) →
       MOESI (i + m + s + e + o , 0 , 0 , suc 0 , 0)

data Unsafe : State → Set where 
  u1 : ∀ {i m s e o} → Unsafe (i , suc m , suc s , e , o)
  u2 : ∀ {i m s e o} → Unsafe (i , suc m , s , suc e , o)
  u3 : ∀ {i m s e o} → Unsafe (i , suc m , s , e , suc o)
  u4 : ∀ {i m s e o} → Unsafe (i , suc (suc m) , s , e , o)
  u5 : ∀ {i m s e o} → Unsafe (i , m , s , suc (suc e) , o)

data MOESI' : State → Set where
  w1 : ∀ {i} → MOESI'(i , 0 , 0 , suc 0 , 0)
  w2 : ∀ {i} → MOESI'(i , suc 0 , 0 , 0 , 0)
  w3 : ∀ {i s o} → MOESI'(i , 0 , s , 0 , o)

inclusion : ∀ {c : State} → MOESI c → MOESI' c
inclusion t1 = w3
inclusion (t2 m) = w3
inclusion (t3 m) with inclusion m
inclusion (t3 m) | w1 = w2
inclusion (t4 m) = w1
inclusion (t5 m) = w1

safety : ∀ {c : State} → MOESI' c → ¬ Unsafe c
safety w1 = λ ()
safety w2 = λ ()
safety w3 = λ ()

valid : ∀ {c : State} → MOESI c → ¬ Unsafe c
valid = safety ∘ inclusion

-- valid₁ m u = {! -c !}
-- C-c C-a

valid₁ : ∀ {c : State} → MOESI c → ¬ Unsafe c
valid₁ t1 ()
valid₁ (t2 m) ()
valid₁ (t3 (t3 m)) u = valid₁ m u5
valid₁ (t3 (t4 m)) ()
valid₁ (t3 (t5 m)) ()
valid₁ (t4 (t2 m)) ()
valid₁ (t4 (t3 m)) ()
valid₁ (t5 m) ()
