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
  using (_×_; _,_; proj₁; proj₂)

open import Function 

open import Relation.Binary.PropositionalEquality as P using ()
import Relation.Binary.EqReasoning as EqR

open CommutativeMonoid CM
open module ≈-Reasoning = EqR setoid

open import Expr public

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

sound-zero′ : ∀ {n m} (es : Vec (Expr m) n) →
                eval-nr (replicate 0) es ≅ ◇

sound-zero′ {zero}  [] ρ = refl

sound-zero′ {suc n} (e ∷ es) ρ =
  begin
    ⟦ eval-nr (replicate 0) (e ∷ es) ⟧ ρ
      ≡⟨⟩
    ε ∙ ⟦ eval-nr (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero′ es ρ ⟩
    ε ∙ ε
      ≈⟨ proj₁ identity ε ⟩
    ε
      ≡⟨⟩
    ⟦ ◇ ⟧ ρ
  ∎

sound-zero : ∀ {n} → norm ◇ ≅  (Expr n ∋ ◇)
sound-zero ρ =
  begin
    ⟦ norm ◇ ⟧ ρ
      ≡⟨⟩
    ⟦ eval-nr (replicate 0) vars ⟧ ρ
      ≈⟨ sound-zero′ vars ρ ⟩
    ⟦ ◇ ⟧ ρ
  ∎

-- distr

distr : ∀ {n} k j (e : Expr n) →
          (k + j) ⊗ e ≅ k ⊗ e ⊕ j ⊗ e

distr zero    j e ρ = sym $ proj₁ identity (⟦ j ⊗ e ⟧ ρ)

distr (suc k) j e ρ =
  begin
    ⟦ (suc k + j) ⊗ e ⟧ ρ
      ≡⟨⟩
    ⟦ e ⊕ (k + j) ⊗ e ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ distr k j e ρ ⟩
    ⟦ e ⊕ (k ⊗ e ⊕ j ⊗ e) ⟧ ρ
      ≈⟨ sym $ assoc (⟦ e ⟧ ρ) (⟦ k ⊗ e ⟧ ρ) (⟦ j ⊗ e ⟧ ρ) ⟩
    ⟦ (e ⊕ k ⊗ e) ⊕ j ⊗ e ⟧ ρ
      ≡⟨⟩
    ⟦ suc k ⊗ e ⊕ j ⊗ e ⟧ ρ
  ∎

-- shuffle

shuffle : ∀ {n} (a b c d : Expr n) →
            (a ⊕ c) ⊕ (b ⊕ d) ≅ (a ⊕ b) ⊕ (c ⊕ d) 
shuffle a b c d ρ =
  begin
    ⟦ (a ⊕ c) ⊕ (b ⊕ d) ⟧ ρ
      ≈⟨ assoc (⟦ a ⟧ ρ) (⟦ c ⟧ ρ) (⟦ b ⊕ d ⟧ ρ) ⟩
    ⟦ a ⊕ (c ⊕ (b ⊕ d)) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ (sym $ assoc (⟦ c ⟧ ρ) (⟦ b ⟧ ρ) (⟦ d ⟧ ρ)) ⟩
    ⟦ a ⊕ ((c ⊕ b) ⊕ d) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ (comm (⟦ c ⟧ ρ) (⟦ b ⟧ ρ) ⟨ ∙-cong ⟩ refl) ⟩
    ⟦ a ⊕ ((b ⊕ c) ⊕ d) ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ assoc (⟦ b ⟧ ρ) (⟦ c ⟧ ρ) (⟦ d ⟧ ρ) ⟩
    ⟦ a ⊕ (b ⊕ (c ⊕ d)) ⟧ ρ
      ≈⟨ sym $ assoc (⟦ a ⟧ ρ) (⟦ b ⟧ ρ) (⟦ c ⊕ d ⟧ ρ) ⟩
    ⟦ (a ⊕ b) ⊕ (c ⊕ d) ⟧ ρ
  ∎

-- sound-plus

sound-plus′ : ∀ {n m} (ks js : Vec ℕ n) (xs : Vec (Expr m) n) →
              eval-nr (zipWith _+_ ks js) xs ≅
              eval-nr ks xs ⊕ eval-nr js xs

sound-plus′ [] [] [] ρ = sym $ proj₁ identity _

sound-plus′ (k ∷ ks) (j ∷ js) (x ∷ xs) ρ =
  begin
    ⟦ eval-nr (zipWith _+_ (k ∷ ks) (j ∷ js)) (x ∷ xs) ⟧ ρ
      ≡⟨⟩
    ⟦ (k + j) ⊗ x ⊕ eval-nr (zipWith _+_ ks js) xs ⟧ ρ
      ≈⟨ (distr k j x ρ) ⟨ ∙-cong ⟩ sound-plus′ ks js xs ρ ⟩
    ⟦ (k ⊗ x ⊕ j ⊗ x) ⊕ (eval-nr ks xs ⊕ eval-nr js xs) ⟧ ρ
      ≈⟨ shuffle (k ⊗ x) (eval-nr ks xs) (j ⊗ x) (eval-nr js xs) ρ ⟩
    ⟦ (k ⊗ x ⊕ eval-nr ks xs) ⊕ (j ⊗ x ⊕ eval-nr js xs) ⟧ ρ
      ≡⟨⟩
    ⟦ eval-nr (k ∷ ks) (x ∷ xs) ⊕ eval-nr (j ∷ js) (x ∷ xs) ⟧ ρ
  ∎

sound-plus : ∀ {n} → (a b : Expr n) →
  norm (a ⊕ b) ≅ norm a ⊕ norm b

sound-plus a b ρ =
  begin
    ⟦ norm (a ⊕ b) ⟧ ρ
      ≡⟨⟩
    ⟦ eval-nr (nr (a ⊕ b)) vars ⟧ ρ
      ≡⟨⟩
    ⟦ eval-nr (zipWith _+_ (nr a)(nr b)) vars ⟧ ρ
      ≈⟨ sound-plus′ (nr a) (nr b) vars ρ ⟩
    ⟦ eval-nr (nr a) vars ⊕ eval-nr (nr b) vars ⟧ ρ
      ≡⟨⟩
    ⟦ norm a ⊕ norm b ⟧ ρ
  ∎

-- sound-var

sound-var′ : ∀ {n m} (i : Fin n) (es : Vec (Expr m) n) →
            eval-nr (1-at i) es ≅ (lookup i es)
sound-var′ zero (e ∷ es) ρ =
  begin
    ⟦ eval-nr (1-at zero) (e ∷ es) ⟧ ρ
      ≡⟨⟩
    ⟦ (e ⊕ ◇) ⊕ eval-nr (replicate 0) es ⟧ ρ
      ≡⟨⟩
    ⟦ (e ⊕ ◇) ⟧ ρ ∙ ⟦ eval-nr (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero′ es ρ ⟩
    ⟦ e ⊕ ◇ ⟧ ρ ∙ ⟦ ◇ ⟧ ρ
      ≡⟨⟩
    ⟦ (e ⊕ ◇) ⊕ ◇ ⟧ ρ
      ≈⟨ proj₂ identity (⟦ e ⊕ ◇ ⟧ ρ) ⟩
    ⟦ e ⊕ ◇ ⟧ ρ
      ≈⟨ proj₂ identity (⟦ e ⟧ ρ) ⟩
    ⟦ e ⟧ ρ
      ≡⟨⟩
    ⟦ lookup zero (e ∷ es) ⟧ ρ
  ∎

sound-var′ (suc i) (e ∷ es) ρ =
  begin
    ⟦ eval-nr (1-at (suc i)) (e ∷ es) ⟧ ρ
      ≡⟨⟩
    ⟦ ◇ ⊕ eval-nr (1-at i) es ⟧ ρ
      ≡⟨⟩
    ε ∙ ⟦ eval-nr (1-at i) es ⟧ ρ
      ≈⟨ proj₁ identity (⟦ eval-nr (1-at i) es ⟧ ρ) ⟩
    ⟦ eval-nr (1-at i) es ⟧ ρ
      ≈⟨ sound-var′ i es ρ ⟩
    ⟦ lookup i es ⟧ ρ
      ≡⟨⟩
    ⟦ lookup (suc i) (e ∷ es) ⟧ ρ
  ∎

sound-var : ∀ {n} → (i : Fin n) →
  norm (var i) ≅ var i
sound-var i ρ =
  begin
    ⟦ norm (var i) ⟧ ρ
      ≡⟨⟩
    ⟦ eval-nr (1-at i) vars ⟧ ρ
      ≈⟨ sound-var′ i vars ρ ⟩
    ⟦ lookup i vars ⟧ ρ
      ≡⟨⟩
    ⟦ lookup i (tabulate var) ⟧ ρ
      ≡⟨ P.cong (flip ⟦_⟧ ρ) (lookup∘tabulate var i) ⟩
    ⟦ var i ⟧ ρ
  ∎

-- sound

sound : ∀ {n} (e : Expr n) → norm e ≅ e

sound {n} (var i) ρ =
  sound-var i ρ

sound (a ⊕ b) ρ =
  begin
    ⟦ norm (a ⊕ b) ⟧ ρ
      ≈⟨ sound-plus a b ρ ⟩
    ⟦ norm a ⊕ norm b ⟧ ρ
      ≡⟨⟩
    ⟦ norm a ⟧ ρ ∙ ⟦ norm b ⟧ ρ
      ≈⟨ sound a ρ ⟨ ∙-cong ⟩ sound b ρ ⟩
    ⟦ a ⟧ ρ ∙ ⟦ b ⟧ ρ
      ≡⟨⟩
    ⟦ a ⊕ b ⟧ ρ
  ∎

sound ◇ ρ =
  sound-zero ρ

-- Proving that e₁ ≅ e₂
-- See Relation.Binary.Reflection

prove : ∀ {n} (eq : Expr n × Expr n) (ρ : Env n)  →
          let e₁ = proj₁ eq; e₂ = proj₂ eq in
            ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

prove (e₁ , e₂) ρ hyp =
  begin
    ⟦ e₁ ⟧ ρ
      ≈⟨ sym $ sound e₁ ρ ⟩
    ⟦ norm e₁ ⟧ ρ
      ≈⟨ hyp ⟩
    ⟦ norm e₂ ⟧ ρ
      ≈⟨ sound e₂ ρ ⟩
    ⟦ e₂ ⟧ ρ
  ∎
