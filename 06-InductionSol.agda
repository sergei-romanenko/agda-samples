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


ℕ-ind : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind P base step zero = base
ℕ-ind P base step (suc n) = step n (ℕ-ind P base step n)

ℕ-ind₁ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) →
           ∀ n → P n
ℕ-ind₁ P base step zero = base
ℕ-ind₁ P base step (suc n) =
  ℕ-ind₁ (λ m → P (suc m)) (step zero base) (λ m → step (suc m)) n

+s : ∀ n m → n + suc m ≡ suc (n + m)
+s zero m = refl
+s (suc n) m = cong suc (+s n m)

+s₁ : ∀ m n → n + suc m ≡ suc (n + m)
+s₁ m = ℕ-ind (λ n → n + suc m ≡ suc (n + m)) refl (λ n → cong suc)

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
even3 = ev-step (odd-step ev-base)

odd4 : Odd 3
odd4 = odd-step (ev-step (odd-step ev-base))

even2n : ∀ n → Even (n + n)
even2n zero = ev-base
even2n (suc n) =
  subst (Even ∘ suc)
        (sym (+s n n) ∶ suc (n + n) ≡ n + suc n)
        (ev-step (odd-step (even2n n)) ∶ Even (suc (suc (n + n))))

even2n′ : ∀ n → Even (n + n)
even2n′ zero = ev-base
even2n′ (suc n) = step (even2n′ n)
  where
    open Related.EquationalReasoning
      renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; sym to ⇒-sym)
    step : Even (n + n) → Even (suc n + suc n)
    step = Even (n + n)
             ⇒⟨ odd-step ⟩
           Odd (suc (n + n))
             ⇒⟨ ev-step ⟩
           Even (suc (suc (n + n)))
             ⇒⟨ subst (Even ∘ suc) (sym (+s n n)) ⟩
           Even (suc (n + suc n))
             ⇒⟨ id ⟩
           Even (suc n + suc n) ∎

even⊎odd : ∀ n → Even n ⊎ Odd n
even⊎odd zero = inj₁ ev-base
even⊎odd (suc n) with even⊎odd n
... | inj₁ ev-n  = inj₂ (odd-step ev-n)
... | inj₂ odd-n = inj₁ (ev-step odd-n)

-- even⊎odd (suc n) = [ inj₂ ∘ odd-step , inj₁ ∘ ev-step ]′ (even-odd n)

odd→¬even : ∀ {n} → Odd n → ¬ Even n
odd→¬even (odd-step even-n) (ev-step odd-n) = odd→¬even odd-n even-n

even? : ∀ n → Dec (Even n)
even? n with even⊎odd n
even? n | inj₁ ev-n  = yes ev-n
even? n | inj₂ odd-n = no (odd→¬even odd-n)

-- Trees

data Tree (A : Set) : Set where

  ● : Tree A
  _<_>_ : (t1 : Tree A) → (a : A) → (t2 : Tree A) → Tree A

Tree-ind : ∀ {A : Set} → (P : Tree A → Set) →
              P (●{A}) →
              (∀ (t1 t2 : Tree A) (a : A) →
              P t1 → P t2 → P (t1 < a > t2)) →
              ∀ t → P t
Tree-ind P base step ● =
  base
Tree-ind P base step (t1 < a > t2 ) =
  step t1 t2 a (Tree-ind P base step t1) (Tree-ind P base step t2)

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
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

➥-correct' : {A : Set} (t : Tree A) (xs : List A) →
  t ⟱ ++ xs ≡ t ➥ xs
➥-correct' ● xs = refl
➥-correct' (t1 < a > t2) xs =
  begin
    (t1 < a > t2) ⟱ ++ xs
      ≡⟨ refl ⟩
    (t1 ⟱ ++ a ∷ t2 ⟱) ++ xs
      ≡⟨ ++-assoc (t1 ⟱) (a ∷ t2 ⟱) xs ⟩
    t1 ⟱ ++ (a ∷ t2 ⟱ ++ xs)
      ≡⟨ ➥-correct' t1 (a ∷ t2 ⟱ ++ xs) ⟩
    t1 ➥ (a ∷ t2 ⟱ ++ xs)
      ≡⟨ cong (λ z → t1 ➥ (a ∷ z)) (➥-correct' t2 xs) ⟩
    t1 ➥ (a ∷ t2 ➥ xs)
      ≡⟨ refl ⟩
    (t1 < a > t2) ➥ xs
  ∎
  where open ≡-Reasoning

++-[] : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) = cong (_∷_ x) (++-[] xs)

➥-correct : {A : Set} (t : Tree A) →
  t ⟱ ≡ t ➥ []

➥-correct t =
  begin
    t ⟱
      ≡⟨ sym (++-[] (t ⟱)) ⟩
    t ⟱ ++ []
      ≡⟨ ➥-correct' t [] ⟩
    t ➥ []
  ∎
  where open ≡-Reasoning

--