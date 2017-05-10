module 06-Induction where

open import Data.Nat
open import Data.List
open import Data.List.Properties
open import Data.Empty
open import Data.Sum
  using (_⊎_; inj₁; inj₂)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function
import Function.Related as Related


ℕ-ind : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind P base step zero = {!!}
ℕ-ind P base step (suc n) = {!-l!}

ℕ-ind₁ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind₁ P base step zero = {!!}
ℕ-ind₁ P base step (suc n) = {!-l!}

+-suc : ∀ n m → n + suc m ≡ suc (n + m)
+-suc n m = {!!}

+-suc₁ : ∀ m n → n + suc m ≡ suc (n + m)
+-suc₁ m = ℕ-ind (λ n → n + suc m ≡ suc (n + m)) {!!} {!!}

mutual

  data Even : ℕ → Set where
    ev-base : Even zero
    ev-step : ∀ {n} → (odd-n : Odd n) → Even (suc n)

  data Odd : ℕ → Set where
    odd-step : ∀ {n} → (even-n : Even n) → Odd (suc n)

data Even₁ : ℕ → Set
data Odd₁  : ℕ → Set

data Even₁ where
  ev-base : Even₁ zero
  ev-step : ∀ {n} → (odd-n : Odd₁ n) → Even₁ (suc n)

data Odd₁ where
  odd-step : ∀ {n} → (even-n : Even₁ n) → Odd₁ (suc n)


even3 : Even 2
even3 = {!!}

odd4 : Odd 3
odd4 = {!!}

even2n : ∀ n → Even (n + n)
even2n zero = ev-base
even2n (suc n) = {!!}

even2n′ : ∀ n → Even (n + n)
even2n′ zero = ev-base
even2n′ (suc n) = step (even2n′ n)
  where
    open Related.EquationalReasoning renaming (sym to ∼sym)
    step : Even (n + n) → Even (suc n + suc n)
    step = Even (n + n)
             ∼⟨ {!!} ⟩
           Odd (suc (n + n))
             ∼⟨ {!!} ⟩
           Even (suc (suc (n + n)))
             ∼⟨ {!!} ⟩
           Even (suc (n + suc n))
             ∼⟨ {!!} ⟩
           Even (suc n + suc n) ∎

even⊎odd : ∀ n → Even n ⊎ Odd n
even⊎odd zero = inj₁ ev-base
even⊎odd (suc n) with even⊎odd n
... | r = {!!}

-- even⊎odd (suc n) = [ inj₂ ∘ odd-step , inj₁ ∘ ev-step ]′ (even-odd n)

odd→¬even : ∀ {n} → Odd n → ¬ Even n
odd→¬even odd-n even-n = {!!}

even? : ∀ n → Dec (Even n)
even? n with even⊎odd n
even? n | r = {!!}

-- Trees

data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : (t₁ t₂ : Tree A) → Tree A

tree-ind :  ∀ {A : Set} (P : Tree A → Set) →
              (∀ a → P (leaf a)) →
              (∀ (t₁ t₂ : Tree A) → P t₁ → P t₂ → P (node t₁ t₂)) →
              ∀ t → P t
tree-ind P base step (leaf a) = {!!}
tree-ind P base step (node t₁ t₂) =
  {!!}

flatten : {A : Set} → Tree A → List A
flatten (leaf a) = a ∷ []
flatten (node t₁ t₂) = flatten t₁ ++ flatten t₂

append : {A : Set} → Tree A → List A → List A
append (leaf a) as = a ∷ as
append (node t₁ t₂) as = append t₁ (append t₂ as)

module Test-flatten {A : Set} (a b c : A) where

  t1 : flatten (leaf a) ≡ a ∷ []
  t1 = refl

  t2 : flatten (node (node (leaf a) (leaf b)) (leaf c)) ≡ a ∷ b ∷ c ∷ []
  t2 = refl

  t3 : append (leaf a) [] ≡ a ∷ []
  t3 = refl

  t4 : append (node (node (leaf a) (leaf b)) (leaf c)) [] ≡ a ∷ b ∷ c ∷ []
  t4 = refl

++-[] : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) = cong (_∷_ x) (++-[] xs)

++-assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

append-correct′ : {A : Set} (t : Tree A) (xs : List A) →
  flatten t ++ xs ≡ append t xs
append-correct′ (leaf a) xs = {!!}
append-correct′ (node t₁ t₂) xs = begin
  (flatten t₁ ++ flatten t₂) ++ xs
    ≡⟨ {!!} ⟩
  flatten t₁ ++ (flatten t₂ ++ xs)
    ≡⟨ {!!} ⟩
  flatten t₁ ++ (append t₂ xs)
    ≡⟨ {!!} ⟩
  append t₁ (append t₂ xs)
  ∎
  where open ≡-Reasoning

append-correct : {A : Set} (t : Tree A) →
  flatten t ≡ append t []
append-correct t =
  flatten t
    ≡⟨ {!!} ⟩
  flatten t ++ []
    ≡⟨ {!!} ⟩
  append t []
  ∎
  where open ≡-Reasoning
