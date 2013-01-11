open import Data.Nat
open import Relation.Nullary using (¬_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Function using (_∘_)

module DataRace-Explicit where

data State : Set where
  _,_,_ : (out cs scs : ℕ) → State

data DataRace : State -> Set where
  t1 : (out : ℕ) → 
      DataRace (out , 0 , 0)
  t2 : (out : ℕ) →
      DataRace (suc out , 0 , 0) → DataRace (out , 1 , 0)
  t3 : (out scs : ℕ) →
      DataRace (suc out , 0 , scs) → DataRace (out , 0 , suc scs)
  t4 : (out cs scs : ℕ) →
      DataRace (out , suc cs , scs) → DataRace (suc out , cs , scs)
  t5 : (out cs scs : ℕ) →
      DataRace (out , cs , suc scs) → DataRace (suc out , cs , scs)

data Unsafe : State -> Set where
  u1 : (out cs scs : ℕ) →
      Unsafe (out , suc cs , suc scs)

data DataRace' : State -> Set where
  w1 : (out scs : ℕ) →
      DataRace' (out , 0 , scs)
  w2 : (out : ℕ) →
      DataRace' (out , 1 , 0)

inclusion : (c : State) → DataRace c → DataRace' c

inclusion .(out , 0 , 0) (t1 out) = w1 out 0
inclusion .(out , 1 , 0) (t2 out d) = w2 out
inclusion .(out , 0 , suc scs) (t3 out scs d) = w1 out (suc scs)

inclusion .(suc out , cs , scs) (t4 out cs scs d)
              with inclusion (out , suc cs , scs) d
inclusion .(suc out , zero , scs) (t4 out zero scs d) | d' = w1 (suc out) scs
inclusion .(suc out , suc n , scs) (t4 out (suc n) scs d) | ()

inclusion .(suc out , cs , scs) (t5 out cs scs d)
              with inclusion (out , cs , suc scs) d
inclusion .(suc out , zero , scs) (t5 out zero scs d) | d' = w1 (suc out) scs
inclusion .(suc out , suc n , scs) (t5 out (suc n) scs d) | ()

safety : (c : State) → DataRace' c → Unsafe c → ⊥
safety .(out , 0 , scs) (w1 out scs) ()
safety .(out , 1 , 0) (w2 out) ()

valid : (c : State) → DataRace c → Unsafe c → ⊥
valid c d u = safety c (inclusion c d) u

-- This is a scandal! :-)
-- Agda is able to find a direc proof by induction, which does not
-- use the relation DataRace' produced by supercompilation.
-- Hence, Agda internally implements something close to supercompilation.

-- valid₁ d u = {! -c !}
-- C-c C-a

valid₁ : (c : State) → DataRace c → ¬ Unsafe c

valid₁ .(out , 0 , 0) (t1 out) ()
valid₁ .(out , 1 , 0) (t2 out y) ()
valid₁ .(out , 0 , suc scs) (t3 out scs y) ()

valid₁ .(suc out , suc cs , suc scs)
       (t4 out .(suc cs) .(suc scs) d)
       (u1 .(suc out) cs scs) =
       valid₁ (out , suc (suc cs) , suc scs) d (u1 out (suc cs) scs)

valid₁ .(suc out , suc cs , suc scs)
       (t5 out .(suc cs) .(suc scs) d)
       (u1 .(suc out) cs scs) =
       valid₁ (out , suc cs , suc (suc scs)) d (u1 out cs (suc scs))
