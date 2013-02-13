open import Algebra

module Semantics {c} {ℓ} (CM : CommutativeMonoid c ℓ) where

open import Level using() renaming(_⊔_ to _⊔l_)

open import Data.Nat
open import Data.Fin using(Fin; zero; suc)
open import Data.Vec
  using(Vec; _∷_; []; lookup; replicate; zipWith; tabulate)
open import Data.Vec.Properties
  using (lookup∘tabulate)

open import Function 

open import Relation.Binary.PropositionalEquality as P using ()
import Relation.Binary.EqReasoning as EqR

open CommutativeMonoid CM
open module ≈-Reasoning = EqR setoid

open import Expr

Env : ℕ → Set c
Env n = Vec Carrier n

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ var i ⟧ ρ = lookup i ρ
⟦ a ⊕ b ⟧ ρ = ⟦ a ⟧ ρ ∙ ⟦ b ⟧ ρ
⟦ nil  ⟧ ρ = ε

[∣_∣] : ∀ {n} → Eqn n → Env n → Set ℓ
[∣ a == b ∣] ρ = ⟦ a ⟧ ρ ≈ ⟦ b ⟧ ρ

_≅_ : ∀ {n} → Expr n → Expr n → Set (ℓ ⊔l c)
a ≅ b = ∀ ρ → ⟦ a ⟧ ρ ≈ ⟦ b ⟧ ρ

-- Soundness

open import Data.Product

sound-zero : ∀ {n m} (es : Vec (Expr m) n) →
             nil ≅ fold-zip (replicate 0) es
sound-zero {zero}  [] ρ = refl
sound-zero {suc n} (e ∷ es) ρ =
  begin
    ⟦ nil ⟧ ρ
      ≈⟨ refl ⟩
    ε
      ≈⟨ sym $ proj₁ identity ε ⟩
    ε ∙ ε
      ≈⟨ ∙-cong refl (sound-zero es ρ) ⟩
    ε ∙ ⟦ fold-zip (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ fold-zip (replicate 0) (e ∷ es) ⟧ ρ
  ∎

distr : ∀ {n} k j (e : Expr n) → k ⊗ e ⊕ j ⊗ e ≅ (k + j) ⊗ e
distr zero    j e ρ = proj₁ identity (⟦ j ⊗ e ⟧ ρ)
distr (suc k) j e ρ =
  begin
    ⟦ suc k ⊗ e ⊕ j ⊗ e ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (e ⊕ k ⊗ e) ⊕ j ⊗ e ⟧ ρ
      ≈⟨ assoc (⟦ e ⟧ ρ) (⟦ k ⊗ e ⟧ ρ) (⟦ j ⊗ e ⟧ ρ) ⟩
    ⟦ e ⊕ (k ⊗ e ⊕ j ⊗ e) ⟧ ρ
      ≈⟨ ∙-cong refl (distr k j e ρ) ⟩
    ⟦ e ⊕ (k + j) ⊗ e ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (suc k + j) ⊗ e ⟧ ρ
  ∎

shuffle : ∀ {n} (a b c d : Expr n) →
          (a ⊕ b) ⊕ (c ⊕ d) ≅ (a ⊕ c) ⊕ (b ⊕ d)
shuffle a b c d ρ =
  begin
    ⟦ (a ⊕ b) ⊕ (c ⊕ d) ⟧ ρ
      ≈⟨ assoc (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ c ⊕ d ⟧ ρ) ⟩
    ⟦ a ⊕ (b ⊕ (c ⊕ d)) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ sym (assoc (⟦ b ⟧ ρ) (⟦ c ⟧ ρ) (⟦ d ⟧ ρ)) ⟩
    ⟦ a ⊕ ((b ⊕ c) ⊕ d) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ (comm (⟦ b ⟧ ρ) (⟦ c ⟧ ρ) ⟨ ∙-cong ⟩ refl) ⟩
    ⟦ a ⊕ ((c ⊕ b) ⊕ d) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ assoc (⟦ c ⟧ ρ) (⟦ b ⟧ ρ) (⟦ d ⟧ ρ) ⟩
    ⟦ a ⊕ (c ⊕ (b ⊕ d)) ⟧ ρ
      ≈⟨ sym $ assoc (⟦ a ⟧ ρ) (⟦ c ⟧ ρ) (⟦ b ⊕ d ⟧ ρ) ⟩
    ⟦ (a ⊕ c) ⊕ (b ⊕ d) ⟧ ρ
  ∎
  where open ≈-Reasoning


sound-plus : ∀ {n m} (ks js : Vec ℕ n) (xs : Vec (Expr m) n) →
             fold-zip ks xs ⊕ fold-zip js xs ≅
             fold-zip (zipWith _+_ ks js) xs
sound-plus [] [] [] ρ = proj₁ identity _
sound-plus (k ∷ ks) (j ∷ js) (x ∷ xs) ρ =
  begin
    ⟦ fold-zip (k ∷ ks) (x ∷ xs) ⊕ fold-zip (j ∷ js) (x ∷ xs) ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (k ⊗ x ⊕ fold-zip ks xs) ⊕ (j ⊗ x ⊕ fold-zip js xs) ⟧ ρ
      ≈⟨ shuffle (k ⊗ x) (fold-zip ks xs) (j ⊗ x) (fold-zip js xs) ρ ⟩
    ⟦ (k ⊗ x ⊕ j ⊗ x) ⊕ (fold-zip ks xs ⊕ fold-zip js xs) ⟧ ρ
      ≈⟨ distr k j x ρ ⟨ ∙-cong ⟩ sound-plus ks js xs ρ ⟩
    ⟦ (k + j) ⊗ x ⊕ fold-zip (zipWith _+_ ks js) xs ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ fold-zip (zipWith _+_ (k ∷ ks) (j ∷ js)) (x ∷ xs) ⟧ ρ
  ∎
  where open ≈-Reasoning

sound-var : ∀ {n m} (i : Fin n) (es : Vec (Expr m) n) →
            (lookup i es) ≅ fold-zip (1-at i) es
sound-var zero (e ∷ es) ρ =
  begin
    ⟦ lookup zero (e ∷ es) ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ e ⟧ ρ
      ≈⟨ sym $ proj₂ identity (⟦ e ⟧ ρ) ⟩
    ⟦ e ⊕ nil ⟧ ρ
      ≈⟨ sym $ proj₂ identity (⟦ e ⊕ nil ⟧ ρ) ⟩
    ⟦ (e ⊕ nil) ⊕ nil ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero es ρ ⟩
    ⟦ (e ⊕ nil) ⊕ fold-zip (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ fold-zip (1-at zero) (e ∷ es) ⟧ ρ
  ∎
  where open ≈-Reasoning

sound-var (suc i) (e ∷ es) ρ =
  begin
    ⟦ lookup (suc i) (e ∷ es) ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ lookup i es ⟧ ρ
      ≈⟨ sound-var i es ρ ⟩
    ⟦ fold-zip (1-at i) es ⟧ ρ
      ≈⟨ sym $ proj₁ identity (⟦ fold-zip (1-at i) es ⟧ ρ) ⟩
    ⟦ nil ⊕ fold-zip (1-at i) es ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ fold-zip (1-at (suc i)) (e ∷ es) ⟧ ρ
  ∎

sound : ∀ {n} (e : Expr n) → e ≅ norm e
sound {n} (var i) ρ =
  begin
    ⟦ var i ⟧ ρ
      ≡⟨ P.cong (flip ⟦_⟧ ρ) (P.sym $ lookup∘tabulate var i) ⟩
    ⟦ lookup i vars ⟧ ρ
      ≈⟨ sound-var i vars ρ ⟩
    ⟦ fold-zip (1-at i) vars ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ norm (var i) ⟧ ρ
  ∎
sound (a ⊕ b) ρ =
  begin
    ⟦ a ⊕ b ⟧ ρ
      ≈⟨ sound a ρ ⟨ ∙-cong ⟩ sound b ρ ⟩
    ⟦ norm a ⊕ norm b ⟧ ρ
      ≈⟨ sound-plus (eval a) (eval b) vars ρ ⟩
    ⟦ norm (a ⊕ b) ⟧ ρ
  ∎
sound nil ρ = sound-zero vars ρ

prove : ∀ {n} (eq : Eqn n) ρ → [∣ normEqn eq ∣] ρ → [∣ eq ∣] ρ
prove (a == b) ρ prf =
  begin
    ⟦ a ⟧ ρ
      ≈⟨ sound a ρ ⟩
    ⟦ norm a ⟧ ρ
      ≈⟨ prf ⟩
    ⟦ norm b ⟧ ρ
      ≈⟨ sym (sound b ρ) ⟩
    ⟦ b ⟧ ρ
  ∎

--
