module 05-ProblemSolvingSol where

open import Data.Nat
open import Data.Nat.Properties.Simple
  using (+-right-identity; +-suc; +-comm)
open import Data.Product

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- +-right-identity : ∀ n → n + 0 ≡ n
-- +-suc : ∀ m n → m + suc n ≡ suc (m + n)
-- +-comm : ∀ m n → m + n ≡ n + m

open ≡-Reasoning

2+1≡x : ∃ λ x → 2 + 1 ≡ x
2+1≡x = suc (suc (suc zero)) , refl

m+n≡? : ∀ m n →  ∃ λ x → (m + n ≡ x)
m+n≡? m n = m + n , refl

2+x≡3 : ∃ λ x → 2 + x ≡ 3
2+x≡3 = suc zero , refl

m+?≡n : ∀ m n → m ≤ n →  ∃ λ x → (m + x ≡ n)
m+?≡n .0 n z≤n = n , refl
m+?≡n .(suc m) .(suc n) (s≤s {m} {n} m≤n) with m+?≡n m n m≤n
... | x , m+x≡n = x , cong suc m+x≡n

x+1≡3 : ∃ λ x → x + 1 ≡ 3
x+1≡3 = suc (suc zero) , refl

---- Now x + m ≡  n can be reduced to m + x ≡ n

?+m≡n-comm : ∀ m n → m ≤ n →  ∃ λ x → (x + m ≡ n)
?+m≡n-comm m n m≤n with m+?≡n m n m≤n
... | x , m+x≡n rewrite +-comm m x = x , m+x≡n

{- rewrite

    f ps rewrite eqn = rhs

  where eqn : a ≡ b , is equivalent to

    f ps with a | eqn
    ... | ._ | refl = rhs

-}

---- A direct proof looks as a fusion of +-comm and m+?≡n,
---- and uses +-right-identity and +-suc directly .

?+m≡n : ∀ m n → m ≤ n →  ∃ λ x → (x + m ≡ n)
?+m≡n .0 n z≤n = n , +-right-identity n
?+m≡n .(suc m) .(suc n) (s≤s {m} {n} m≤n) with ?+m≡n m n m≤n
... | x , x+m≡n rewrite +-suc x m = x , x+sm≡sn
  where x+sm≡sn : x + suc m ≡ suc n
        x+sm≡sn = begin
                    x + suc m   ≡⟨ +-suc x m ⟩
                    suc (x + m) ≡⟨ cong suc x+m≡n ⟩
                    suc n
                  ∎

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
  ∃-oldest = Alice ,
    given2 (λ z → superlative1
      Bill Carl (λ ()) (given1 (superlative1 Carl Alice (λ ()) z)) z)

  ∃-youngest : Σ Child (λ a → youngest a)
  ∃-youngest = Bill , given1 (antonym1 Alice (proj₂ ∃-oldest))

  problem : Σ Child (λ a → Σ Child (λ b → oldest a × youngest b))
  problem = Alice , Bill , proj₂ ∃-oldest , proj₂ ∃-youngest

x≤1 : ∃ λ x → x ≤ 1
x≤1 = zero , z≤n

x≤1×y≤1 : ∃ λ x → ∃ λ y → x ≢ y × x ≤ 1 × y ≤ 1
x≤1×y≤1 = zero , suc zero , (λ ()) , z≤n , s≤s z≤n
