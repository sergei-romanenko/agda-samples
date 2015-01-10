{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  Based on

    Thierry Coquand and Peter Dybjer. 1997.
    Intuitionistic model constructions and normalization proofs.
    Mathematical. Structures in Comp. Sci. 7, 1 (February 1997), 75-94.
    DOI=10.1017/S0960129596002150 http://dx.doi.org/10.1017/S0960129596002150 

  and

    Peter Dybjer and Andrzej Filinski. 2000.
    Normalization and Partial Evaluation.
    In Applied Semantics, International Summer School, APPSEM 2000, Caminha,
    Portugal, September 9-15, 2000, Advanced Lectures,
    Gilles Barthe, Peter Dybjer, Luis Pinto, and João Saraiva (Eds.).
    Springer-Verlag, London, UK, UK, 137-192.

  and

    Andreas Abel and James Chapman. 2014.
    Normalization by evaluation in the delay monad: A case study for
    coinduction via copatterns and sized types.
    In MSFP'14, volume 153 of EPTCS, pages 51--67.
    http://arxiv.org/abs/1406.2059v1

-}

{-# OPTIONS --copatterns #-}

module STCC-Delay-SK-red where

open import Agda.Primitive
open import Size
open import Category.Monad
  using (RawMonad; module RawMonad)

open import Data.Nat
open import Data.Empty
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

open import STCC-Delay-SK-norm

--
-- Reduction.
--

infix 4 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K : ∀ {α β} {x : Tm α} {y : Tm β} →
            K ∙ x ∙ y ⟶ x
  ⟶S : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
            S ∙ x ∙ y ∙ z ⟶ (x ∙ z) ∙ (y ∙ z)
  ⟶AL : ∀ {α β} {x x′ : Tm (α ⇒ β)} {y   : Tm α} →
            x ⟶ x′  →  x ∙ y ⟶ x′ ∙ y
  ⟶AR : ∀ {α β} {x : Tm (α ⇒ β)} {y y′ : Tm α} →
            y ⟶ y′  →  x ∙ y ⟶ x ∙ y′

-- Reflexive and transitive closure of _⟶_ .

infix 4 _⟶*_

data _⟶*_ : ∀ {α} → Tm α → Tm α → Set where
  here  : ∀ {α} {t : Tm α} →
            t ⟶* t
  there : ∀ {α} {t1 t2 t3 : Tm α} →
            t1 ⟶  t2  →  t2 ⟶* t3  →  t1 ⟶* t3

-- Example: the behavior of I .

reduction-example : ∀ {α} (x : Tm α) → (I {α}) ∙ x ⟶* x
reduction-example x = there ⟶S (there ⟶K here)

--
-- `reify u` does return a term that cannot be reduced).
--

Irreducible : ∀ {α} (x : Tm α) → Set
Irreducible x = ∄ (λ y → x ⟶ y)

reify→nf : ∀ {α} (u : Nf α) → Irreducible (reify u)

reify→nf K0 (y , ())
reify→nf (K1 u) (._ , ⟶AL ())
reify→nf (K1 u) (._ , ⟶AR ⟶y) =
  reify→nf u (, ⟶y)
reify→nf S0 (y , ())
reify→nf (S1 u) (._ , ⟶AL ())
reify→nf (S1 u) (._ , ⟶AR ⟶y) =
  reify→nf u (, ⟶y)
reify→nf (S2 u v) (._ , ⟶AL (⟶AL ()))
reify→nf (S2 u v) (._ , ⟶AL (⟶AR ⟶y)) =
  reify→nf u (, ⟶y)
reify→nf (S2 u v) (._ , ⟶AR ⟶y) =
  reify→nf v (, ⟶y)
