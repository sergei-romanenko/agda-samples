module 05-ProblemSolving where

open import Data.Nat
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

2+1≡x : ∃ λ x → 2 + 1 ≡ x
2+1≡x = {!!}

2+x≡3 : ∃ λ x → 2 + x ≡ 3
2+x≡3 = {!!}

x+1≡3 : ∃ λ x → x + 1 ≡ 3
x+1≡3 = {!!}


module Pratt5 where
  {-
  My Favorite Logic Puzzles
  by John P. Pratt

  http://www.johnpratt.com/items/puzzles/logic_puzzles.html

  When asked her 3 children's ages, Mrs. Muddled said that Alice is the youngest
  unless Bill is, and that if Carl isn't the youngest then Alice is the oldest.
  Who is the oldest and who is the youngest?
  -}

  data Child : Set where
    Alice : Child
    Bill  : Child
    Carl  : Child

  postulate

    youngest : Child → Set
    oldest   : Child → Set

    superlative1 : ∀ a b → a ≢ b → youngest a → ¬ youngest b
    superlative2 : ∀ a b → a ≢ b → oldest a → ¬ oldest b

    antonym1 : ∀ a → oldest a → ¬ youngest a
    antonym2 : ∀ a → youngest a → ¬ oldest a

    given1 : ¬ youngest Alice → youngest Bill
    given2 : ¬ youngest Carl  → oldest Alice

  ∃-oldest : Σ Child (λ a → oldest a)
  ∃-oldest = {!!}

  ∃-youngest : Σ Child (λ a → youngest a)
  ∃-youngest = {!!}

  problem : Σ Child (λ a → Σ Child (λ b → oldest a × youngest b))
  problem = {!!}

x≤1 : ∃ λ x → x ≤ 1
x≤1 = {!!}

x≤1×y≤1 : ∃ λ x → ∃ λ y → x ≢ y × x ≤ 1 × y ≤ 1
x≤1×y≤1 = {!!}