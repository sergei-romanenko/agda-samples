open import Algebra

module Semantics {c} {ℓ} (CM : CommutativeMonoid c ℓ) where

open import Level using() renaming(_⊔_ to _⊔l_)

open import Data.Nat
open import Data.Fin using(Fin; zero; suc)
open import Data.Vec
  using(Vec; _∷_; []; lookup; replicate; zipWith; tabulate)
open import Data.Vec.Properties
  using (lookup∘tabulate)
open import Data.Product
open import Data.Vec.N-ary

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
               ◇ ≅ fold-zip (replicate 0) es

sound-zero {zero}  [] ρ = refl

sound-zero {suc n} (e ∷ es) ρ =
  begin
    ⟦ ◇ ⟧ ρ
      ≈⟨ refl ⟩
    ε
      ≈⟨ sym $ proj₁ identity ε ⟩
    ε ∙ ε
      ≈⟨ refl ⟨ ∙-cong ⟩ sound-zero es ρ ⟩
    ε ∙ ⟦ fold-zip (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ fold-zip (replicate 0) (e ∷ es) ⟧ ρ
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

-- sound-var

sound-var : ∀ {n m} (i : Fin n) (es : Vec (Expr m) n) →
            (lookup i es) ≅ fold-zip (1-at i) es
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
    ⟦ (e ⊕ ◇) ⊕ fold-zip (replicate 0) es ⟧ ρ
      ≈⟨ refl ⟩
    ⟦ fold-zip (1-at zero) (e ∷ es) ⟧ ρ
  ∎

sound-var (suc i) (e ∷ es) ρ =
  begin
    ⟦ lookup (suc i) (e ∷ es) ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ lookup i es ⟧ ρ
      ≈⟨ sound-var i es ρ ⟩
    ⟦ fold-zip (1-at i) es ⟧ ρ
      ≈⟨ sym $ proj₁ identity (⟦ fold-zip (1-at i) es ⟧ ρ) ⟩
    ⟦ ◇ ⊕ fold-zip (1-at i) es ⟧ ρ
      ≡⟨ P.refl ⟩
    ⟦ fold-zip (1-at (suc i)) (e ∷ es) ⟧ ρ
  ∎

-- sound

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
      ≈⟨ sound-plus (nf a) (nf b) vars ρ ⟩
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

-- Specialized variants of prove for n = 0, 1 , 2.

-- ρ = []

solve0 : ∀ (f : Expr 0 × Expr 0) →
  let e₁ = proj₁ f
      e₂ = proj₂ f
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  let ρ = [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve0 f hyp =
  prove [] (proj₁ f) (proj₂ f) hyp

-- ρ = a ∷ []

solve1 : ∀ (f : (a : Expr 1) → Expr 1 × Expr 1) →
  let e₁ = proj₁ (close 1 f)
      e₂ = proj₂ (close 1 f)
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  (a : Carrier) → let ρ = a ∷ [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve1 f hyp a =
  prove (a ∷ []) (proj₁ (close 1 f)) (proj₂ (close 1 f)) hyp

-- ρ = a ∷ b ∷ []

solve2 : ∀ (f : (a b : Expr 2) → Expr 2 × Expr 2) →
  let e₁ = proj₁ (close 2 f)
      e₂ = proj₂ (close 2 f)
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  (a b : Carrier) → let ρ = a ∷ b ∷ [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve2 f hyp a b =
  prove (a ∷ b ∷ []) (proj₁ (close 2 f)) (proj₂ (close 2 f)) hyp


-- A variant of prove which should in many cases be easier to use,
-- because variables and environments are handled in a less explicit
-- way.
--
-- (Try to instantiate n with a small natural number and normalise
-- the remainder of the type.)

-- See Relation.Binary.Reflection

solve : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
  let e₁ = proj₁ (close n f)
      e₂ = proj₂ (close n f)
  in
  Eqʰ n _≈_ (curryⁿ ⟦ norm e₁ ⟧) (curryⁿ ⟦ norm e₂ ⟧) →
  Eq  n _≈_ (curryⁿ ⟦ e₁ ⟧) (curryⁿ ⟦ e₂ ⟧)

solve n f hyp =
  curryⁿ-cong _≈_ ⟦ e₁ ⟧ ⟦ e₂ ⟧ (λ ρ → prove ρ e₁ e₂
    (curryⁿ-cong⁻¹ _≈_ ⟦ norm e₁ ⟧ ⟦ norm e₂ ⟧ (Eqʰ-to-Eq n _≈_ hyp) ρ))
  where
    e₁ = proj₁ (close n f)
    e₂ = proj₂ (close n f)

-- A variant of _,_ which is intended to make uses of solve
-- look a bit nicer.

infix 4 _⊜_

_⊜_ : ∀ {n} → Expr n → Expr n → Expr n × Expr n
_⊜_ = _,_

--
