module 02-PropEqSol where

open import Data.Nat

open import Relation.Binary.PropositionalEquality

open import Function

open ≡-Reasoning

n+0 : ∀ n → n + 0 ≡ n
n+0 zero = refl
n+0 (suc n) = cong suc (n+0 n)

n+sm : ∀ n m → n + suc m ≡ suc (n + m)
n+sm zero m = refl
n+sm (suc n) m = cong suc (n+sm n m)

+-comm : ∀ n m → n + m ≡ m + n
+-comm zero m = sym (n+0 m)
+-comm (suc n) m =
  begin
    suc n + m ≡⟨ refl ⟩
    suc (n + m) ≡⟨ cong suc (+-comm n m) ⟩
    suc (m + n) ≡⟨ sym (n+sm m n) ⟩
    m + suc n
  ∎

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
  subst (λ e → Even e)
        (sym (cong suc (+-comm n (suc n)))
        ∶ suc (suc (n + n)) ≡ suc (n + suc n))
        (ev-ss (ev2n n)
        ∶ Even (suc (suc (n + n))))
  ∶ Even (suc (n + suc n))