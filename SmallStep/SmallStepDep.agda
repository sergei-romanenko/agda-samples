--
-- Small-step operational semantics
-- making use of dependent types
--

{-
This (slightly modified) code is from

  Proof by Smugness
  by Conor on August 7, 2007.
  http://fplab.bitbucket.org/posts/2007-08-07-proof-by-smugness.html
-}

module SmallStepDep where

open import Data.Nat
open import Data.Vec
  using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality

--
-- A Toy Language
--

infixl 6 _⊕_

data Tm : Set where
  val : (n : ℕ) → Tm
  _⊕_  : (t₁ t₂ : Tm) → Tm

-- Big-step evaluator

eval : Tm → ℕ
eval (val n) = n
eval (t₁ ⊕  t₂) = eval t₁ + eval t₂

--
-- Virtual machine
--

-- Program

-- The idea is to index code by initial and final stack depth
-- in order to ensure stack safety. 

data HCode : ℕ → ℕ → Set where
  push : {i : ℕ} → ℕ → HCode i (suc i)
  add  : {i : ℕ} → HCode (suc (suc i)) (suc i)
  seq  : {i j k : ℕ} → HCode i j → HCode j k → HCode i k

-- State

Stack : ℕ → Set
Stack i = Vec ℕ i

-- Stack transformer

Transformer : ℕ → ℕ → Set
Transformer i j = Stack i → Stack j

-- HCode-algebra with Transformer as its carrier, enables the interpreter
-- to be implemented as a fold (= "catamorphism" in Greek).

record HCodeAlg (P : ℕ → ℕ → Set) : Set where
  field
    push′ : {i : ℕ} → ℕ → P i (suc i)
    add′  : {i : ℕ} → P (suc (suc i)) (suc i)
    seq′  : {i j k : ℕ} → P i j → P j k → P i k

open HCodeAlg public

-- And now, foldH is a "catamorphism"...

foldH : {P : ℕ → ℕ → Set} → HCodeAlg P →
          {i j : ℕ} → HCode i j → P i j
foldH φ (push n) = push′ φ n
foldH φ add = add′ φ
foldH φ (seq c₁ c₂) = seq′ φ (foldH φ c₁) (foldH φ c₂)

-- Let us instantiate HCodeAlg with Transformer

semAlg : HCodeAlg Transformer
semAlg = record
  { push′ = λ n s → n ∷ s
  ; add′  = λ { (n ∷ m ∷ s) → (m + n) ∷ s}
  ; seq′  = λ f g x → g (f x)
  }

-- Interpreter

-- Good... The interpreter is a fold!

exec : ∀ {i j : ℕ} → HCode i j → Transformer i j
exec = foldH semAlg

-- Now the challenge is to build correctness into the compiled code.
-- The idea is to ornament the code with some semantic markup.

data HCodeM {P : ℕ → ℕ → Set} (φ : HCodeAlg P) :
            (i j : ℕ) → P i j → Set where
  pushM : {i : ℕ} → (n : ℕ) →
    HCodeM φ i (suc i) (push′ φ n)
  addM : {i : ℕ} →
    HCodeM φ (suc (suc i)) (suc i) (add′ φ)
  seqM : {i j k : ℕ}{a : P i j}{b : P j k} →
    HCodeM φ i j a → HCodeM φ j k b →
    HCodeM φ i k (seq′ φ a b)

-- Thus, each constructor in HCodeM is labeled with its semantics,
-- using the given algebra to calculate the semantics of the whole
-- from the semantics of the part.

-- The following operation throws away the markup.

forget : {P : ℕ → ℕ → Set}{phi : HCodeAlg P}
  {i j : ℕ} {p : P i j} → HCodeM phi i j p → HCode i j
forget (pushM n) = push n
forget addM = add
forget (seqM c₁ c₂) = seq (forget c₁) (forget c₂)

-- Even if we forget the markup, we can still recover the semantics
-- by computing it recursively with fold.

correct : {P : ℕ → ℕ → Set}{φ : HCodeAlg P}
  {i j : ℕ} {p : P i j} → (c : HCodeM φ i j p) →
  foldH φ (forget c) ≡ p
correct (pushM n) = refl
correct addM = refl
correct {P} {φ} (seqM c₁ c₂) =
  cong₂ (seq′ φ) (correct c₁) (correct c₂)

-- Now let’s write a correct compiler. First we write the core of the thing,
-- producing marked up code with the right semantics.

compileM : (t : Tm){i : ℕ} →
  HCodeM semAlg i (suc i) (λ s → eval t ∷ s)
compileM (val n) = pushM n
compileM (t₁ ⊕ t₂) = seqM (seqM (compileM t₁) (compileM t₂)) addM

-- That code typechecks!
-- Now, to produce actual code, forget the markup:

compile : (t : Tm){i : ℕ} → HCode i (suc i)
compile e = forget (compileM e)

-- And now we get the proof of correctness for the compiler
-- virtually for free.

-- The usual proof is an induction on the execution of the code,
-- with a mixture of partial evaluation (which we get for free)
-- and rewriting by the inductive hypothesis (which is what was being
-- set up by the construction of HCodeM). Rather than writing a recursive
-- program and then doing an inductive proof exactly following
-- its structure, we have glued the two together.

compileCorrect : (t : Tm){i : ℕ} →
  exec {i} (compile t) ≡ λ s → eval t ∷ s
compileCorrect t = correct (compileM t)

--
