open import Algebra

module Prover {c} {ℓ} (CM : CommutativeMonoid c ℓ) where

open import Level using() renaming(_⊔_ to _⊔l_)

open import Data.Nat
open import Data.Fin using(Fin; zero; suc)
open import Data.Vec
  using(Vec; _∷_; []; lookup; replicate; zipWith; tabulate)
open import Data.Vec.Properties
  using (lookup∘tabulate)
open import Data.Product
  using (_×_; proj₁; proj₂)

open import Function 

open import Relation.Binary.PropositionalEquality as P using ()
import Relation.Binary.EqReasoning as EqR

open CommutativeMonoid CM
open module ≈-Reasoning = EqR setoid

open import Expr

-- Evaluation

Env : ℕ → Set c
Env n = Vec Carrier n

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ var i ⟧ ρ = lookup i ρ
⟦ a ⊕ b ⟧ ρ = ⟦ a ⟧ ρ ∙ ⟦ b ⟧ ρ
⟦ ◇ ⟧ ρ = ε

-- Semantic equivalence

_≅_ : ∀ {n} → Expr n → Expr n → Set (ℓ ⊔l c)
a ≅ b = ∀ ρ → ⟦ a ⟧ ρ ≈ ⟦ b ⟧ ρ

--
-- Soundness: e ≅ norm e
--

-- sound-zero

sound-zero : ∀ {n m} (es : Vec (Expr m) n) →
               ◇ ≅ eval-nr (replicate 0) es

sound-zero {zero}  [] ρ = refl

sound-zero {suc n} (e ∷ es) ρ =
  begin
    ⟦ ◇ ⟧ ρ
      ≈⟨ refl ⟩
    ε
      ≈⟨ sym $ proj₁ identity ε ⟩
    ε ∙ ε
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero es ρ ⟩
    ε ∙ ⟦ eval-nr (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ eval-nr (replicate 0) (e ∷ es) ⟧ ρ
  ∎

-- distr

distr : ∀ {n} k j (e : Expr n) →
          k ⊗ e ⊕ j ⊗ e ≅ (k + j) ⊗ e

distr zero    j e ρ = proj₁ identity (⟦ j ⊗ e ⟧ ρ)

distr (suc k) j e ρ =
  begin
    ⟦ suc k ⊗ e ⊕ j ⊗ e ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (e ⊕ k ⊗ e) ⊕ j ⊗ e ⟧ ρ
      ≈⟨ assoc (⟦ e ⟧ ρ) (⟦ k ⊗ e ⟧ ρ) (⟦ j ⊗ e ⟧ ρ) ⟩
    ⟦ e ⊕ (k ⊗ e ⊕ j ⊗ e) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ distr k j e ρ ⟩
    ⟦ e ⊕ (k + j) ⊗ e ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (suc k + j) ⊗ e ⟧ ρ
  ∎

-- shuffle

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

-- sound-plus

sound-plus : ∀ {n m} (ks js : Vec ℕ n) (xs : Vec (Expr m) n) →
             eval-nr ks xs ⊕ eval-nr js xs ≅
             eval-nr (zipWith _+_ ks js) xs

sound-plus [] [] [] ρ = proj₁ identity _

sound-plus (k ∷ ks) (j ∷ js) (x ∷ xs) ρ =
  begin
    ⟦ eval-nr (k ∷ ks) (x ∷ xs) ⊕ eval-nr (j ∷ js) (x ∷ xs) ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ (k ⊗ x ⊕ eval-nr ks xs) ⊕ (j ⊗ x ⊕ eval-nr js xs) ⟧ ρ
      ≈⟨ shuffle (k ⊗ x) (eval-nr ks xs) (j ⊗ x) (eval-nr js xs) ρ ⟩
    ⟦ (k ⊗ x ⊕ j ⊗ x) ⊕ (eval-nr ks xs ⊕ eval-nr js xs) ⟧ ρ
      ≈⟨ distr k j x ρ ⟨ ∙-cong ⟩ sound-plus ks js xs ρ ⟩
    ⟦ (k + j) ⊗ x ⊕ eval-nr (zipWith _+_ ks js) xs ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ eval-nr (zipWith _+_ (k ∷ ks) (j ∷ js)) (x ∷ xs) ⟧ ρ
  ∎

-- sound-var

sound-var : ∀ {n m} (i : Fin n) (es : Vec (Expr m) n) →
            (lookup i es) ≅ eval-nr (1-at i) es
sound-var zero (e ∷ es) ρ =
  begin
    ⟦ lookup zero (e ∷ es) ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ e ⟧ ρ
      ≈⟨ sym $ proj₂ identity (⟦ e ⟧ ρ) ⟩
    ⟦ e ⊕ ◇ ⟧ ρ
      ≈⟨ sym $ proj₂ identity (⟦ e ⊕ ◇ ⟧ ρ) ⟩
    ⟦ (e ⊕ ◇) ⊕ ◇ ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero es ρ ⟩
    ⟦ (e ⊕ ◇) ⊕ eval-nr (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ eval-nr (1-at zero) (e ∷ es) ⟧ ρ
  ∎

sound-var (suc i) (e ∷ es) ρ =
  begin
    ⟦ lookup (suc i) (e ∷ es) ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ lookup i es ⟧ ρ
      ≈⟨ sound-var i es ρ ⟩
    ⟦ eval-nr (1-at i) es ⟧ ρ
      ≈⟨ sym $ proj₁ identity (⟦ eval-nr (1-at i) es ⟧ ρ) ⟩
    ⟦ ◇ ⊕ eval-nr (1-at i) es ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ eval-nr (1-at (suc i)) (e ∷ es) ⟧ ρ
  ∎

-- sound

sound : ∀ {n} (e : Expr n) → e ≅ norm e

sound {n} (var i) ρ =
  begin
    ⟦ var i ⟧ ρ
      ≡⟨ P.cong (flip ⟦_⟧ ρ) (P.sym $ lookup∘tabulate var i) ⟩
    ⟦ lookup i vars ⟧ ρ
      ≈⟨ sound-var i vars ρ ⟩
    ⟦ eval-nr (1-at i) vars ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ norm (var i) ⟧ ρ
  ∎

sound (a ⊕ b) ρ =
  begin
    ⟦ a ⊕ b ⟧ ρ
      ≈⟨ sound a ρ ⟨ ∙-cong ⟩ sound b ρ ⟩
    ⟦ norm a ⊕ norm b ⟧ ρ
      ≈⟨ sound-plus (nr a) (nr b) vars ρ ⟩
    ⟦ norm (a ⊕ b) ⟧ ρ
  ∎

sound ◇ ρ = sound-zero vars ρ

-- Proving that e₁ ≅ e₂
-- See Relation.Binary.Reflection

prove : ∀ {n} (ρ : Env n) e₁ e₂ →
           ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ →
           ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

prove ρ e₁ e₂ hyp =
  begin
    ⟦ e₁ ⟧ ρ
      ≈⟨ sound e₁ ρ ⟩
    ⟦ norm e₁ ⟧ ρ
      ≈⟨ hyp ⟩
    ⟦ norm e₂ ⟧ ρ
      ≈⟨ sym $ sound e₂ ρ ⟩
    ⟦ e₂ ⟧ ρ
  ∎

--
