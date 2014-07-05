open import Algebra

module Solver {c} {ℓ} (CM : CommutativeMonoid c ℓ) where

open import Data.Product
  using (_×_; proj₁; proj₂)

open import Data.Vec
  using ([]; _∷_)
open import Data.Vec.N-ary

open import Expr public

open CommutativeMonoid CM

import Prover
open Prover CM using (⟦_⟧; prove)

-- Specialized versions of prove for n = 0, 1, 2.

-- ρ = []

solve0 : ∀ (f : Expr 0 × Expr 0) →
  let e₁ = proj₁ f; e₂ = proj₂ f
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  let ρ = [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve0 f hyp =
  prove f [] (hyp {[]})

-- ρ = a ∷ []

solve1 : ∀ (f : (a : Expr 1) → Expr 1 × Expr 1) →
  let eq = close 1 f; e₁ = proj₁ eq; e₂ = proj₂ eq
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  (a : Carrier) → let ρ = a ∷ [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve1 f hyp a =
  prove (close 1 f) (a ∷ []) hyp

-- ρ = a ∷ b ∷ []

solve2 : ∀ (f : (a b : Expr 2) → Expr 2 × Expr 2) →
  let eq = close 2 f; e₁ = proj₁ eq; e₂ = proj₂ eq
  in
  (∀ {ρ} → ⟦ norm e₁ ⟧ ρ ≈ ⟦ norm e₂ ⟧ ρ) →
  (a b : Carrier) → let ρ = a ∷ b ∷ [] in ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ

solve2 f hyp a b =
  prove (close 2 f) (a ∷ b ∷ []) hyp


-- `solve` is a variant of `prove` which should in many cases be easier
-- to use, because variables and environments are handled in a less explicit
-- way.

-- See Relation.Binary.Reflection

solve : ∀ n (f : N-ary n (Expr n) (Expr n × Expr n)) →
  let eq = close n f; e₁ = proj₁ eq; e₂ = proj₂ eq
  in
  Eqʰ n _≈_ (curryⁿ ⟦ norm e₁ ⟧) (curryⁿ ⟦ norm e₂ ⟧) →
  Eq  n _≈_ (curryⁿ ⟦ e₁ ⟧) (curryⁿ ⟦ e₂ ⟧)

solve n f hyp =
  curryⁿ-cong _≈_ ⟦ e₁ ⟧ ⟦ e₂ ⟧
    (λ ρ → prove eq ρ
       (curryⁿ-cong⁻¹ _≈_ ⟦ norm e₁ ⟧ ⟦ norm e₂ ⟧ (Eqʰ-to-Eq n _≈_ hyp) ρ))
  where
    eq = close n f; e₁ = proj₁ eq; e₂ = proj₂ eq

--
