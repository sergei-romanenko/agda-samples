--
-- Small-step operational semantics
-- making use of dependent types
--

{-
This (slightly modified) code is from

  Proof by Smugness
  by Conor on August 7, 2007.
  http://fplab.bitbucket.org/posts/2007-08-07-proof-by-smugness.html

  The same stuff as in SmallStepDep, but via explicit recursion.

-}

module SmallStepDepRec where

open import Data.Nat
  using (ℕ; _+_)
open import Data.Vec
  using (Vec; []; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

--
-- A Toy Language
--

infixl 6 _⊕_

data Tm : Set where
  val : (n : ℕ) → Tm
  _⊕_  : (t1 t2 : Tm) → Tm

-- Big-step evaluator

eval : Tm → ℕ
eval (val n) = n
eval (t1 ⊕ t2) = eval t1 + eval t2

--
-- Virtual machine
--

-- Program

-- The idea is to index code by initial and final stack depth
-- in order to ensure stack safety. 

data Code : (i j : ℕ) → Set where
  seq  : ∀ {i j k} (c1 : Code i j) (c2 : Code j k) → Code i k
  push : ∀ {i} (n : ℕ) → Code i (1 + i)
  add  : ∀ {i} → Code (2 + i) (1 + i)

-- State

Stack : ℕ → Set
Stack i = Vec ℕ i

-- Interpreter

exec : ∀ {i j} (c : Code i j) (s : Stack i) → Stack j
exec (seq c1 c2) s = exec c2 (exec c1 s)
exec (push n) s = n ∷ s
exec add (n2 ∷ n1 ∷ s) = (n1 + n2) ∷ s

-- Compiler

compile : ∀ {i} (t : Tm) → Code i (1 + i)
compile (val n) = push n
compile (t1 ⊕ t2) = seq (seq (compile t1) (compile t2)) add

-- `compile` is correct with respect to `exec`

correct : ∀ {i} (t : Tm) (s : Stack i) →
  exec {i} (compile t) s ≡ eval t ∷ s
correct (val n) s = refl
correct (t1 ⊕ t2) s =
  exec (compile (t1 ⊕ t2)) s
    ≡⟨⟩
  exec (seq (seq c1 c2) add) s
    ≡⟨⟩
  exec add (exec c2 (exec c1 s))
    ≡⟨ cong (exec add ∘ exec c2) (correct t1 s) ⟩
  exec add (exec c2 (n1 ∷ s))
    ≡⟨ cong (exec add) (correct t2 (n1 ∷ s)) ⟩
  exec add (n2 ∷ n1 ∷ s)
    ≡⟨⟩
  n1 + n2 ∷ s
    ≡⟨⟩
  eval (t1 ⊕ t2) ∷ s
  ∎
  where
  open ≡-Reasoning
  n1 = eval t1; n2 = eval t2
  c1 = compile t1; c2 = compile t2

-- Here is another proof, which is shorter, but is more mysterious.

correct′ : ∀ {i} (t : Tm) (s : Stack i) →
  exec {i} (compile t) s ≡ eval t ∷ s
correct′ (val n) s = refl
correct′ {i} (t1 ⊕ t2) s
  rewrite correct t1 s | correct t2 (eval t1 ∷ s)
  = refl
