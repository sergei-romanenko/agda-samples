module 02-PropEq where

open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Function
import Function.Related as Related

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc (+-right-identity n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n = sym (+-right-identity n)
+-comm (suc m) n = begin
  suc m + n
    ≡⟨⟩
  suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)
    ≡⟨ sym (+-suc n m) ⟩
  n + suc m
  ∎
  where open ≡-Reasoning

-- Induction by derivation

data Even : ℕ → Set where
  ev-z  : Even zero
  ev-ss : ∀ {n} → Even n → Even (suc (suc n))

ev2 : Even 2
ev2 = ev-ss ev-z

ev4 : Even 4
ev4 = ev-ss (ev-ss ev-z)


ev2n : ∀ n → Even (n + n)
ev2n zero = ev-z
ev2n (suc n) =
  Even (suc (n + suc n)) ∋
  subst (λ e → Even e)
        (suc (suc (n + n)) ≡ suc (n + suc n)
          ∋ sym (cong suc (+-comm n (suc n))))
        (Even (suc (suc (n + n)))
          ∋ ev-ss (ev2n n))


ev2n₂ : ∀ n → Even (n + n)
ev2n₂ zero = ev-z
ev2n₂ (suc n) = step (ev2n₂ n)
  where
    open Related.EquationalReasoning renaming (sym to ∼sym)
    step : Even (n + n) → Even (suc n + suc n)
    step =
      Even (n + n)
        ∼⟨ ev-ss ⟩
      Even (suc (suc (n + n)))
        ≡⟨ cong (Even ∘ suc) (sym $ +-suc n n) ⟩
      Even (suc (n + suc n))
        ∼⟨ id ⟩
      Even (suc n + suc n) ∎
