{-# OPTIONS --copatterns #-}

{-
Based on the presentation

* Andreas Abel  with James Chapman, Brigitte Pientka, Anton Setzer, David Thibodeau.
  Coinduction in Agda using Copatterns and Sized Types.
  15 May 2014, Types for Proofs and Programs (TYPES 2014).
  http://www2.tcs.ifi.lmu.de/~abel/talkTYPES14.pdf
-}


module 13-CopatternsEval where

open import Size
--open import Function
open import Data.Nat
open import Data.Fin
open import Data.Vec using (Vec; []; _∷_; lookup)

-- De Bruijn lambda terms and values

data Tm (n : ℕ) : Set where
  var : (x : Fin n) → Tm n
  abs : (t : Tm (suc n)) → Tm n
  app : (r s : Tm n) → Tm n

mutual
  record Val : Set where
    inductive
    constructor clos
    field
      {n} : ℕ
      body : Tm (suc n)
      env : Env n

  Env : ℕ → Set
  Env = Vec Val

module Naive-CBV-interpreter where

  -- Termination check fails!

  {-# TERMINATING #-}
  mutual
    ⟦_⟧_ : ∀ {n} → Tm n → Env n → Val
    ⟦ var x ⟧ ρ = lookup x ρ
    ⟦ abs t ⟧ ρ = clos t ρ
    ⟦ app r s ⟧ ρ = apply (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)

    apply : Val → Val → Val
    apply (clos t ρ) v = ⟦ t ⟧ (v ∷ ρ)

--
-- The coinductive delay monad
--

module Coinductive-delay-monad where

  mutual

    data Delay (A : Set) : Set where
      return : (a : A) → Delay A
      later  : (a∞ : ∞Delay A) → Delay A

    record ∞Delay (A : Set) : Set where
      coinductive
      constructor delay
      field
        force : Delay A

  open ∞Delay public

  -- Nonterminating computation

  forever : ∀ {A} → ∞Delay A
  force forever = later forever

  -- Monad instance

  mutual
    _>>=_ : ∀ {A B} → Delay A → (A → Delay B) → Delay B
    return a >>= f = f a
    later a∞ >>= f = later (a∞ ∞>>= f)

    _∞>>=_ : ∀ {A B} → ∞Delay A → (A → Delay B) → ∞Delay B
    force (a∞ ∞>>= f) = force a∞ >>= f

  -- Evaluation in the delay monad

  -- Productivity check fails!

  {-# TERMINATING #-}
  mutual
    ⟦_⟧_ : ∀ {n} → Tm n → Env n → Delay Val
    ⟦ var x ⟧ ρ = return (lookup x ρ)
    ⟦ abs t ⟧ ρ = return (clos t ρ)
    ⟦ app r s ⟧ ρ = apply (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)

    apply : Delay Val → Delay Val → Delay Val
    apply u? v? =
      u? >>= (λ u →
      v? >>= (λ v →
        later (∞apply u v)))

    ∞apply : Val → Val → ∞Delay Val
    force (∞apply (clos t ρ) v) = ⟦ t ⟧ (v ∷ ρ)


--
-- Sized coinductive delay monad
--

mutual

  data Delay {i : Size} (A : Set) : Set where
    return : (a : A) → Delay {i} A
    later  : (a∞ : ∞Delay {i} A) → Delay {i} A

  record ∞Delay {i : Size} (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay {j} A

open ∞Delay public

-- Nonterminating computation

-- Since j < i, the recursive call `forever {j}` is OK.

forever : ∀ {i A} → ∞Delay {i} A
force (forever {i}) {j} = later (forever {j})

-- Sized monad instance

mutual
  _>>=_ : ∀ {i A B} → Delay {i} A → (A → Delay {i} B) → Delay {i} B
  return a >>= f = f a
  later a∞ >>= f = later (a∞ ∞>>= f)

  _∞>>=_ : ∀ {i A B} → ∞Delay {i} A → (A → Delay {i} B) → ∞Delay {i} B
  force (a∞ ∞>>= f) = force a∞ >>= f

--
-- Sized corecursive evaluator
--

-- Now termination checker is happy!

mutual
  ⟦_⟧_ : ∀ {i n} → Tm n → Env n → Delay {i} Val
  ⟦ var x ⟧ ρ = return (lookup x ρ)
  ⟦ abs t ⟧ ρ = return (clos t ρ)
  ⟦ app r s ⟧ ρ = apply (⟦ r ⟧ ρ) (⟦ s ⟧ ρ)

  apply : ∀ {i} → Delay {i} Val → Delay {i} Val → Delay {i} Val
  apply u? v? =
    u? >>= (λ u →
    v? >>= (λ v →
      later (∞apply u v)))

  ∞apply : ∀ {i} → Val → Val → ∞Delay {i} Val
  force (∞apply (clos t ρ) v) = ⟦ t ⟧ (v ∷ ρ)

--
