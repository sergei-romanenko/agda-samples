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
  using (ℕ; _+_; zero; suc)
open import Data.Vec
  using (Vec; []; _∷_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

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
  exec (compile t) s ≡ eval t ∷ s
correct (val n) s =
  n ∷ s ≡⟨⟩ n ∷ s ∎
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
  n1 = eval t1; n2 = eval t2
  c1 = compile t1; c2 = compile t2

-- Here is another proof, which is shorter, but is more mysterious.

correct′ : ∀ {i} (t : Tm) (s : Stack i) →
  exec (compile t) s ≡ eval t ∷ s
correct′ (val n) s = refl
correct′ {i} (t1 ⊕ t2) s
  rewrite correct′ t1 s | correct′ t2 (eval t1 ∷ s)
  = refl

--
-- Compiling to a list of instructions
--

-- Instructions

data Inst : (i j : ℕ) → Set where
  push : ∀ {i} (n : ℕ) → Inst i (1 + i)
  add  : ∀ {i} → Inst (2 + i) (1 + i)

-- Programs

infixr 5 _∷_

data Prog : (i j : ℕ) → Set where
  [] : ∀ {i} → Prog i i
  _∷_ : ∀ {i j k} (c : Inst i j) (p : Prog j k) → Prog i k

-- Interpreter

p-exec : ∀ {i j} (p : Prog i j) (s : Stack i) → Stack j
p-exec [] s = s
p-exec (push n ∷ p) s = p-exec p (n ∷ s)
p-exec (add ∷ p) (n2 ∷ n1 ∷ s) = p-exec p ((n1 + n2) ∷ s)

-- Compiler

p-compile : ∀ {i j} (t : Tm) (p : Prog (1 + i) j) → Prog i j
p-compile (val n) p = push n ∷ p
p-compile (t1 ⊕ t2) p =
  p-compile t1 (p-compile t2 (add ∷ p))

-- Code → Prog

flatten : ∀ {i j k} (c : Code i j) (p : Prog j k) → Prog i k
flatten (seq c1 c2) p = flatten c1 (flatten c2 p)
flatten (push n) p = push n ∷ p
flatten add p = add ∷ p

-- `flatten` is correct.

flatten-correct′ : ∀ {i j k} (c : Code i j) (p : Prog j k) (s : Stack i) →
  p-exec p (exec c s) ≡ p-exec (flatten c p) s
flatten-correct′ (seq c1 c2) p s =
  p-exec p (exec (seq c1 c2) s)
    ≡⟨⟩
  p-exec p (exec c2 (exec c1 s))
    ≡⟨ flatten-correct′ c2 p (exec c1 s) ⟩
  p-exec (flatten c2 p) (exec c1 s)
    ≡⟨ flatten-correct′ c1 (flatten c2 p) s ⟩
  p-exec (flatten c1 (flatten c2 p)) s
    ≡⟨⟩
  p-exec (flatten (seq c1 c2) p) s
  ∎
flatten-correct′ (push n) p s = refl
flatten-correct′ add p (n2 ∷ n1 ∷ s) = refl

flatten-correct : ∀ {i j} (c : Code i j) (s : Stack i) →
  exec c s ≡ p-exec (flatten c []) s
flatten-correct c s = flatten-correct′ c [] s

-- compile ~ p compile

compile~p-compile : ∀ {i j} (t : Tm) (p : Prog (1 + i) j) →
  flatten (compile t) p ≡ p-compile t p
compile~p-compile (val n) p = refl
compile~p-compile (t1 ⊕ t2) p =
  flatten (compile (t1 ⊕ t2)) p
    ≡⟨⟩
  flatten (compile t1) (flatten (compile t2) (add ∷ p))
    ≡⟨ compile~p-compile t1 (flatten (compile t2) (add ∷ p)) ⟩
  p-compile t1 (flatten (compile t2) (add ∷ p))
    ≡⟨ cong (p-compile t1) (compile~p-compile t2 (add ∷ p)) ⟩
  p-compile t1 (p-compile t2 (add ∷ p))
    ≡⟨⟩
  p-compile (t1 ⊕ t2) p
  ∎
