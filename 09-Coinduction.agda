module 09-Coinduction where

open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open ≡-Reasoning

record AbsStore : Set₁ where
  field
    Var   : Set

  Store : Set
  Store = Var → ℕ

  field
    _[_≔_] : Store → Var → ℕ → Store
  

record AbsCmd (absStore : AbsStore) : Set₁ where
  open AbsStore absStore
  field
    AExp  : Set
    BExp  : Set
    A⟦_⟧  : AExp → Store → ℕ
    B⟦_⟧  : BExp → Store → Bool

  data Cmd : Set where
    skip   : Cmd
    assign : Var → AExp → Cmd
    seq    : Cmd → Cmd → Cmd
    while  : BExp → Cmd → Cmd

  return : Store → Maybe Store
  return σ = just σ

  bind : Maybe Store → (Store → Maybe Store) → Maybe Store
  bind (just σ) f = f σ
  bind nothing f = nothing

  syntax bind e1 (λ σ → e2) = σ ← e1 , e2

record AbsCmdSem (absStore : AbsStore) (absCmd : AbsCmd absStore) : Set₁ where
  open AbsStore absStore
  open AbsCmd absCmd

  data _/_⇩_ : (c : Cmd) (σ σ′ : Store) → Set where
    ⇩-skip :
      ∀ {σ} → skip / σ ⇩ σ
    ⇩-assign :
      ∀ {σ v a} → assign v a / σ ⇩ σ [ v ≔ A⟦ a ⟧ σ ]
    ⇩-seq :
      ∀ {σ σ′ σ′′ c₁ c₂} → c₁ / σ ⇩ σ′ → c₂ / σ′ ⇩ σ′′ → seq c₁ c₂ / σ ⇩ σ′′
    ⇩-while-true :
      ∀ {σ σ′ σ′′ b c} → B⟦ b ⟧ σ ≡ true → c / σ ⇩ σ′ → while b c / σ′ ⇩ σ′′ →
        while b c / σ ⇩ σ′′
    ⇩-while-false :
      ∀ {σ b c} → B⟦ b ⟧ σ ≡ false → while b c / σ ⇩ σ

  C_⟦_⟧ : (i : ℕ) (c : Cmd) (σ : Store) → Maybe Store
  C zero ⟦ c ⟧ σ =
    nothing
  C suc i ⟦ skip ⟧ σ =
    return σ
  C suc i ⟦ assign v a ⟧ σ =
    return (σ [ v ≔ A⟦ a ⟧ σ ])
  C suc i ⟦ seq c₁ c₂ ⟧ σ =
    σ′ ← C i ⟦ c₁ ⟧ σ , C i ⟦ c₂ ⟧ σ′
  C suc i ⟦ while b c ⟧ σ with B⟦ b ⟧ σ
  ... | true = σ′ ← C i ⟦ c ⟧ σ , C i ⟦ while b c ⟧ σ′
  ... | false = return σ

  C-correct : (i : ℕ) (c : Cmd) (σ σ′ : Store) →
    C i ⟦ c ⟧ σ ≡ just σ′ → c / σ ⇩ σ′
  C-correct zero c σ σ′ ()
  C-correct (suc i) skip .σ′ σ′ refl = ⇩-skip
  C-correct (suc i) (assign v a) σ .(σ [ v ≔ A⟦ a ⟧ σ ]) refl = ⇩-assign
  C-correct (suc i) (seq c₁ c₂) σ σ′′ h
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C-correct (suc i) (seq c₁ c₂) σ σ′′ h
       | just σ′ | [ g ]ⁱ =
    ⇩-seq (C-correct i c₁ σ σ′ g) (C-correct i c₂ σ′ σ′′ h)
  C-correct (suc i) (seq c₁ c₂) σ σ′′ () | nothing | [ g ]ⁱ
  C-correct (suc i) (while b c) σ σ′′ h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C-correct (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
  C-correct (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
       | just σ′ | [ g ]ⁱ =
    ⇩-while-true f (C-correct i c σ σ′ g) (C-correct i (while b c) σ′ σ′′ h)
  C-correct (suc i) (while b c) σ σ′′ () | true | [ f ]ⁱ
       | nothing | [ g ]ⁱ
  C-correct (suc i) (while b c) .σ′′ σ′′ refl | false | [ f ]ⁱ = ⇩-while-false f

--
