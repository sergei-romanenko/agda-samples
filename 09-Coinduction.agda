module 09-Coinduction where

open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.Product

open import Function

open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality
  renaming ([_] to [_]ⁱ)

open ≡-Reasoning

record AbsStore : Set₁ where
  field
    Var   : Set
    Store : Set

  field
    get : Store → Var → ℕ
    update : Store → Var → ℕ → Store
  

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
      ∀ {σ v a} → assign v a / σ ⇩ update σ v (A⟦ a ⟧ σ)
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
    return (update σ v (A⟦ a ⟧ σ))
  C suc i ⟦ seq c₁ c₂ ⟧ σ =
    σ′ ← C i ⟦ c₁ ⟧ σ , C i ⟦ c₂ ⟧ σ′
  C suc i ⟦ while b c ⟧ σ with B⟦ b ⟧ σ
  ... | true = σ′ ← C i ⟦ c ⟧ σ , C i ⟦ while b c ⟧ σ′
  ... | false = return σ

  -- Auxiliaries

  <′⇨≤′ : {i j : ℕ} → i <′ j → i ≤′ j
  <′⇨≤′ ≤′-refl = ≤′-step ≤′-refl
  <′⇨≤′ (≤′-step m≤′n) = ≤′-step (<′⇨≤′ m≤′n)

  -- C-mono

  C-mono : (i j : ℕ) → i ≤′ j → (c : Cmd) (σ σ′ : Store) →
    C i ⟦ c ⟧ σ ≡ just σ′ → C j ⟦ c ⟧ σ ≡ just σ′
  C-mono zero j i≤′j c σ σ′ ()
  C-mono (suc i) zero () c σ σ′ h
  C-mono (suc .j) (suc j) ≤′-refl c σ σ′ h = h
  C-mono (suc i) (suc j) (≤′-step i<′j) c σ σ′′ h = helper c h
    where
      helper : (c : Cmd) →
               C suc i ⟦ c ⟧ σ ≡ just σ′′ → C suc j ⟦ c ⟧ σ ≡ just σ′′
      helper skip h = h
      helper (assign v a) h = h
      helper (seq c₁ c₂) h
        with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
      helper (seq c₁ c₂) h
        | just σ′ | [ g ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c₁ σ σ′ g
        = C-mono i j (<′⇨≤′ i<′j) c₂ σ′ σ′′ h
      helper (seq c₁ c₂) ()
        | nothing | [ g ]ⁱ
      helper (while b c) h  with B⟦ b ⟧ σ
      helper (while b c) h | true
        with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
      helper (while b c) h | true
        | just σ′ | [ g ]ⁱ rewrite C-mono i j (<′⇨≤′ i<′j) c σ σ′ g
        = C-mono i j (<′⇨≤′ i<′j) (while b c) σ′ σ′′ h
      helper (while b c') () | true
        | nothing | [ g ]ⁱ
      helper (while b c) h | false = h

  -- C⇒⇩

  C⇒⇩ : (i : ℕ) (c : Cmd) (σ σ′ : Store) →
    C i ⟦ c ⟧ σ ≡ just σ′ → c / σ ⇩ σ′
  C⇒⇩ zero c σ σ′ ()
  C⇒⇩ (suc i) skip .σ′ σ′ refl = ⇩-skip
  C⇒⇩ (suc i) (assign v a) σ .(update σ v (A⟦ a ⟧ σ )) refl = ⇩-assign
  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ h
    with C i ⟦ c₁ ⟧ σ | inspect (C i ⟦ c₁ ⟧) σ
  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ h
       | just σ′ | [ g ]ⁱ =
    ⇩-seq (C⇒⇩ i c₁ σ σ′ g) (C⇒⇩ i c₂ σ′ σ′′ h)
  C⇒⇩ (suc i) (seq c₁ c₂) σ σ′′ () | nothing | [ g ]ⁱ
  C⇒⇩ (suc i) (while b c) σ σ′′ h with B⟦ b ⟧ σ | inspect (B⟦ b ⟧) σ
  C⇒⇩ (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
    with C i ⟦ c ⟧ σ | inspect (C i ⟦ c ⟧) σ
  C⇒⇩ (suc i) (while b c) σ σ′′ h | true | [ f ]ⁱ
       | just σ′ | [ g ]ⁱ =
    ⇩-while-true f (C⇒⇩ i c σ σ′ g) (C⇒⇩ i (while b c) σ′ σ′′ h)
  C⇒⇩ (suc i) (while b c) σ σ′′ () | true | [ f ]ⁱ
       | nothing | [ g ]ⁱ
  C⇒⇩ (suc i) (while b c) .σ′′ σ′′ refl | false | [ f ]ⁱ = ⇩-while-false f

--
