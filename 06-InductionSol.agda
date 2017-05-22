module 06-InductionSol where

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


indℕ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
indℕ P base step zero = base
indℕ P base step (suc n) = step n (indℕ P base step n)

indℕ₁ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
indℕ₁ P base step zero = base
indℕ₁ P base step (suc n) =
  indℕ₁ (λ m → P (suc m)) (step zero base) (λ m → step (suc m)) n

+-suc : ∀ n m → n + suc m ≡ suc (n + m)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-suc₁ : ∀ m n → n + suc m ≡ suc (n + m)
+-suc₁ m = indℕ (λ n → n + suc m ≡ suc (n + m)) refl (λ n → cong suc)

mutual

  data Even : ℕ → Set where
    even0 : Even zero
    even1 : ∀ {n} → (odd-n : Odd n) → Even (suc n)

  data Odd : ℕ → Set where
    odd1 : ∀ {n} → (even-n : Even n) → Odd (suc n)


even3 : Even 2
even3 = even1 (odd1 even0)

odd4 : Odd 3
odd4 = odd1 (even1 (odd1 even0))

even2n : ∀ n → Even (n + n)
even2n zero = even0
even2n (suc n) =
  subst (Even ∘ suc) (sym $ +-suc n n) (even1 (odd1 (even2n n)))

even2n′ : ∀ n → Even (n + n)
even2n′ zero = even0
even2n′ (suc n) = step (even2n′ n)
  where
    open Related.EquationalReasoning renaming (sym to ∼sym)
    step : Even (n + n) → Even (suc n + suc n)
    step = Even (n + n)
             ∼⟨ odd1 ⟩
           Odd (suc (n + n))
             ∼⟨ even1 ⟩
           Even (suc (suc (n + n)))
             ≡⟨ cong (Even ∘ suc) (sym $ +-suc n n) ⟩
           Even (suc (n + suc n))
             ≡⟨ refl ⟩
           Even (suc n + suc n) ∎

even⊎odd : ∀ n → Even n ⊎ Odd n
even⊎odd zero = inj₁ even0
even⊎odd (suc n) with even⊎odd n
... | inj₁ even-n  = inj₂ (odd1 even-n)
... | inj₂ odd-n = inj₁ (even1 odd-n)

-- even⊎odd (suc n) = [ inj₂ ∘ odd1 , inj₁ ∘ even1 ]′ (even-odd n)

odd→¬even : ∀ {n} → Odd n → ¬ Even n
odd→¬even (odd1 even-n) (even1 odd-n) = odd→¬even odd-n even-n

even? : ∀ n → Dec (Even n)
even? n with even⊎odd n
even? n | inj₁ even-n  = yes even-n
even? n | inj₂ odd-n = no (odd→¬even odd-n)

-- Trees

data Tree (A : Set) : Set where
  leaf : (a : A) → Tree A
  node : (t₁ t₂ : Tree A) → Tree A

tree-ind :  ∀ {A : Set} (P : Tree A → Set) →
              (∀ a → P (leaf a)) →
              (∀ (t₁ t₂ : Tree A) → P t₁ → P t₂ → P (node t₁ t₂)) →
              ∀ t → P t
tree-ind P base step (leaf a) = base a
tree-ind P base step (node t₁ t₂) =
  step t₁ t₂ (tree-ind P base step t₁) (tree-ind P base step t₂)

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
append-correct′ (leaf a) xs = refl
append-correct′ (node t₁ t₂) xs = begin
  (flatten t₁ ++ flatten t₂) ++ xs
    ≡⟨ ++-assoc (flatten t₁) (flatten t₂) xs ⟩
  flatten t₁ ++ (flatten t₂ ++ xs)
    ≡⟨ cong (_++_ (flatten t₁)) (append-correct′ t₂ xs) ⟩
  flatten t₁ ++ (append t₂ xs)
    ≡⟨ append-correct′ t₁ (append t₂ xs) ⟩
  append t₁ (append t₂ xs)
  ∎
  where open ≡-Reasoning

append-correct : {A : Set} (t : Tree A) →
  flatten t ≡ append t []
append-correct t =
  flatten t
    ≡⟨ sym $ ++-[] (flatten t) ⟩
  flatten t ++ []
    ≡⟨ append-correct′ t [] ⟩
  append t []
  ∎
  where open ≡-Reasoning
