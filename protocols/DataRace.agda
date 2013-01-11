open import Data.Nat
open import Relation.Nullary using (¬_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Function using (_∘_)

module DataRace where

data State : Set where
  _,_,_ : (out cs scs : ℕ) → State

data DataRace : State -> Set where
  t1 : ∀ {out} → 
      DataRace (out , 0 , 0)
  t2 : ∀ {out} →
      DataRace (suc out , 0 , 0) → DataRace (out , 1 , 0)
  t3 : ∀ {out scs} →
      DataRace (suc out , 0 , scs) → DataRace (out , 0 , suc scs)
  t4 : ∀ {out cs scs} →
      DataRace (out , suc cs , scs) → DataRace (suc out , cs , scs)
  t5 : ∀ {out cs scs} →
      DataRace (out , cs , suc scs) → DataRace (suc out , cs , scs)

data Unsafe : State -> Set where
  u1 : ∀ {out cs scs} →
      Unsafe (out , suc cs , suc scs)

data DataRace' : State -> Set where
  w1 : ∀ {out scs} →
      DataRace' (out , 0 , scs)
  w2 : ∀ {out} →
      DataRace' (out , 1 , 0)

inclusion : {c : State} → DataRace c → DataRace' c
inclusion t1 = w1
inclusion (t2 d) = w2
inclusion (t3 d) = w1
inclusion (t4 d) with inclusion d
inclusion (t4 d) | w2 = w1
inclusion (t5 d) with inclusion d
inclusion (t5 d) | w1 = w1

safety : {c : State} → DataRace' c → ¬ Unsafe c
safety w1 ()
safety w2 ()

valid : {c : State} → DataRace c → ¬ Unsafe c
valid = safety ∘ inclusion

-- This is a scandal! :-)
-- Agda is able to find a direc proof by induction, which does not
-- use the relation DataRace' produced by supercompilation.
-- Hence, Agda internally implements something close to supercompilation.

-- valid₁ d u = {! -c !}
-- C-c C-a

valid₁ : {c : State} → DataRace c → ¬ Unsafe c
valid₁ t1 ()
valid₁ (t2 d) ()
valid₁ (t3 d) ()
valid₁ (t4 d) u1 = valid₁ d u1
valid₁ (t5 d) u1 = valid₁ d u1
