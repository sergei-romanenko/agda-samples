module 06-Induction where

open import Data.Nat
open import Data.List
open import Data.List.Properties
open import Data.Empty
open import Data.Sum
  renaming([_,_] to ⊎[_,_])

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function

open ≡-Reasoning

ℕ-ind : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind P base step zero = {!!}
ℕ-ind P base step (suc n) = {!-l!}

ℕ-ind₁ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind₁ P base step zero = {!!}
ℕ-ind₁ P base step (suc n) = {!-l!}

+s : ∀ n m → n + suc m ≡ suc (n + m)
+s n m = {!!}

+s₁ : ∀ m n → n + suc m ≡ suc (n + m)
+s₁ m = ℕ-ind (λ n → n + suc m ≡ suc (n + m)) {!!} {!!}

mutual

  data Even : ℕ → Set where
    ev-base : Even zero
    ev-step : ∀ {n} → (odd-n : Odd n) → Even (suc n)

  data Odd : ℕ → Set where
    odd-step : ∀ {n} → (even-n : Even n) → Odd (suc n)

even3 : Even 2
even3 = {!!}

odd4 : Odd 3
odd4 = {!!}

even2n : ∀ n → Even (n + n)
even2n zero = ev-base
even2n (suc n) = {!!}

even⊎odd : ∀ n → Even n ⊎ Odd n
even⊎odd zero = inj₁ ev-base
even⊎odd (suc n) with even⊎odd n
... | r = {!!}

-- even-odd (suc n) = [ inj₂ ∘ odd-step , inj₁ ∘ ev-step ]′ (even-odd n)

odd→¬even : ∀ {n} → Odd n → ¬ Even n
odd→¬even odd-n even-n = {!!}

even? : ∀ n → Dec (Even n)
even? n with even⊎odd n
even? n | r = {!!}

-- Trees

data Tree (A : Set) : Set where

  ● : Tree A
  _<_>_ : (t1 : Tree A) → (a : A) → (t2 : Tree A) → Tree A

Tree-ind : ∀ {A : Set} → (P : Tree A → Set) →
              P (●{A}) →
              (∀ (t1 t2 : Tree A) (a : A) →
              P t1 → P t2 → P (t1 < a > t2)) →
              ∀ t → P t
Tree-ind P base step t = {!!}

_⟱ : {A : Set} → Tree A → List A
● ⟱ = []
(t1 < a > t2 ) ⟱ = t1 ⟱ ++ a ∷ t2 ⟱

_➥_ : {A : Set} → Tree A → List A → List A
● ➥ xs = xs
(t1 < a > t2) ➥ xs = t1 ➥ (a ∷ t2 ➥ xs)

module Test⟱ {A : Set} (a b c : A) where

  t1 : ● {A} ⟱ ≡ []
  t1 = refl

  t2 : ((● < a > (● < b > ●)) < c > ●) ⟱ ≡ a ∷ b ∷ c ∷ []
  t2 = refl

  t3 : ● {A} ➥ [] ≡ []
  t3 = refl

  t4 : ((● < a > (● < b > ●)) < c > ●) ➥ [] ≡ a ∷ b ∷ c ∷ []
  t4 = refl

++-assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys zs = {!!}

➥-correct' : {A : Set} (t : Tree A) (xs : List A) →
  t ⟱ ++ xs ≡ t ➥ xs

➥-correct' ● xs = {!!}
➥-correct' (t1 < a > t2) xs =
  begin
    (t1 < a > t2) ⟱ ++ xs
      ≡⟨ {!!} ⟩
    (t1 < a > t2) ➥ xs
  ∎

++-[] : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] xs = {!!}

➥-correct : {A : Set} (t : Tree A) → t ⟱ ≡ t ➥ []

➥-correct t =
  begin
    t ⟱
      ≡⟨ {!!} ⟩
    t ➥ []
  ∎
