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

module STCC-SK-Delay where

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

--
-- Coinductive delay monad.
--

mutual

  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

module Bind where
  infixl 1 _>>=_

  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

--
-- Termination/Convergence.  Makes sense only for Delay A ∞.
--

infix 4 _⇓_

data _⇓_ {A : Set} : (a? : Delay ∞ A) (a : A) → Set where
  now⇓   : ∀ {a} → now a ⇓ a
  later⇓ : ∀ {a} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

_⇓ : {A : Set} (x : Delay ∞ A) → Set
x ⇓ = ∃ λ a → x ⇓ a

-- Lifting a predicate to Delay using convergence.

record Delay⇓ {A : Set} (P : A → Set) (a? : Delay ∞ A) : Set where
  constructor delay⇓
  field
    a  : A
    a⇓ : a? ⇓ a
    pa : P a

-- Monotonicity.

map⇓ : ∀ {A B} {a : A} {a? : Delay ∞ A}
  (f : A → B) (a⇓ : a? ⇓ a) → (f <$> a?) ⇓ f a
map⇓ f now⇓        = now⇓
map⇓ f (later⇓ a⇓) = later⇓ (map⇓ f a⇓)

⇓bind : ∀ {A B} (f : A → Delay ∞ B)
  {?a : Delay ∞ A} {a : A} → ?a ⇓ a →
  {b : B} → (?a >>= f) ⇓ b → f a ⇓ b
⇓bind f now⇓ q = q
⇓bind f (later⇓ p) (later⇓ q) = ⇓bind f p q

bind⇓ : ∀{A B} (f : A → Delay ∞ B)
       {?a : Delay ∞ A} {a : A} → ?a ⇓ a →
       {b : B} → f a ⇓ b → (?a >>= f) ⇓ b
bind⇓ f now⇓ q = q
bind⇓ f (later⇓ p) q = later⇓ (bind⇓ f p q)

>>=⇓→∃ : ∀{A B} (f : A → Delay ∞ B)
  (?a : Delay ∞ A) →
  {b : B} → (?a >>= f) ⇓ b → ∃ λ a → ?a ⇓ a × f a ⇓ b
>>=⇓→∃ f (now a) ⇓b = a , now⇓ , ⇓b
>>=⇓→∃ f (later a∞) {b} (later⇓ ⇓b)
  with >>=⇓→∃ f (force a∞) {b} ⇓b
... | a , ⇓a , fa⇓b = a , later⇓ ⇓a , fa⇓b


--
-- Types.
--

infixr 5 _⇒_

data Ty : Set where
  ⋆   :  Ty
  _⇒_ : (α β : Ty) → Ty

--
-- Typed terms.
--

infixl 5 _∙_

data Tm : Ty → Set where
  K   : ∀ {α β} → Tm (α ⇒ β ⇒ α)
  S   : ∀ {α β γ} → Tm ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  _∙_ : ∀ {α β} → Tm (α ⇒ β) → Tm α → Tm β

--
-- Example terms.
--

I : ∀ {α} → Tm (α ⇒ α)
I {α} = S {α} ∙ K {α} ∙ K {α} {α}

KI : ∀ α β → Tm (α ⇒ β ⇒ β)
KI α β = K ∙ (S ∙ K ∙ K {β = α})

III : Tm (⋆ ⇒ ⋆)
III = I {⋆ ⇒ ⋆} ∙ (I {⋆ ⇒ ⋆} ∙ I {⋆})

--
-- Reduction.
--

infix 4 _⟶_

data _⟶_ : ∀ {α} → Tm α → Tm α → Set where
  ⟶K :  ∀ {α β} {x : Tm α} {y : Tm β} →
             K ∙ x ∙ y ⟶ x
  ⟶S :  ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
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
-- Normal forms.
-- 

data Nf : Ty → Set where
  K0 : ∀ {α β} →
         Nf (α ⇒ β ⇒ α)
  K1 : ∀ {α β} (u : Nf α) →
         Nf (β ⇒ α)
  S0 : ∀ {α β γ} →
         Nf ((α ⇒ β ⇒ γ) ⇒ (α ⇒ β) ⇒ α ⇒ γ)
  S1 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) →
         Nf ((α ⇒ β) ⇒ α ⇒ γ)
  S2 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β))→
         Nf (α ⇒ γ)

reify : ∀ {α} (n : Nf α) → Tm α
reify K0 = K
reify (K1 u) = K ∙ reify u
reify S0 = S
reify (S1 u) = S ∙ reify u
reify (S2 u v) = S ∙ reify u ∙ reify v

--
-- `reify u` does return a term that cannot be reduced).
--

Normal-form : ∀ {α} (x : Tm α) → Set
Normal-form x = ∄ (λ y → x ⟶ y)

reify→nf : ∀ {α} (u : Nf α) → Normal-form (reify u)
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

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  infixl 5 _⟨∙⟩_

  {-# TERMINATING #-}
  _⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (w : Nf α) → Nf β
  K0 ⟨∙⟩ w       = K1 w
  K1 u ⟨∙⟩ w    = u
  S0 ⟨∙⟩ w       = S1 w
  S1 u ⟨∙⟩ w    = S2 u w
  S2 u v ⟨∙⟩ w = (u ⟨∙⟩ w) ⟨∙⟩ (v ⟨∙⟩ w)

  ⟦_⟧ : ∀ {α} (x : Tm α) → Nf α
  ⟦ K ⟧ = K0
  ⟦ S ⟧ = S0
  ⟦ x ∙ y ⟧ = ⟦ x ⟧ ⟨∙⟩ ⟦ y ⟧

  norm : ∀ {α} → Tm α → Tm α
  norm = reify ∘ ⟦_⟧

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- Normalization by evaluation with the delay monad.
--

infixl 5 _⟨∙⟩_

mutual

  _⟨∙⟩_ : ∀ {α β i} (u : Nf (α ⇒ β)) (w : Nf α) → Delay i (Nf β)

  K0 ⟨∙⟩ w = now (K1 w)
  K1 u ⟨∙⟩ w = now u
  S0 ⟨∙⟩ w = now (S1 w)
  S1 u ⟨∙⟩ w = now (S2 u w)
  S2 u v ⟨∙⟩ w = later (∞S u v w)

  ∞S : ∀ {α β γ i}
    (u : Nf (α ⇒ β ⇒ γ)) (v : Nf (α ⇒ β)) (w : Nf α) → ∞Delay i (Nf γ)
  force (∞S u v w) {j} =
    u ⟨∙⟩ w >>= λ uw → v ⟨∙⟩ w >>= λ vw → uw ⟨∙⟩ vw

  ⟦_⟧ : ∀ {α i} (x : Tm α) → Delay i (Nf α)

  ⟦ K ⟧ = now K0
  ⟦ S ⟧ = now S0
  ⟦ x ∙ y ⟧ =
    ⟦ x ⟧ >>= λ u → ⟦ y ⟧ >>= λ v → u ⟨∙⟩ v

dnorm : ∀ {α} (x : Tm α) → ∀ {i} → Delay i (Tm α)
dnorm x = reify <$> ⟦ x ⟧

dnorm-III⇓ : dnorm III ⇓ (S ∙ K ∙ K)
dnorm-III⇓ = later⇓ (later⇓ now⇓)

--
-- Computability of normal forms.
--

mutual

  -- "Computability"

  Comp : ∀ {α} (u? : Delay ∞ (Nf α)) → Set
  Comp {α} u? = ∃ (λ u → u? ⇓ u × Stab u)

  -- "Stability"

  Stab : ∀ {α} (u : Nf α) → Set
  Stab {⋆} u = ⊥
  Stab {α ⇒ β} u = ∀ (v : Nf α) (q : Stab v) → Comp {β} (u ⟨∙⟩ v)

mutual

  all-comp : ∀ {α} (x : Tm α) → Comp ⟦ x ⟧

  all-comp K =
    K0 , now⇓ , λ u p →
      K1 u , now⇓ ,
        λ v q → u , now⇓ , p
  all-comp S =
    S0 , now⇓ , λ u p →
      S1 u , now⇓ , λ v q →
        S2 u v , now⇓ , λ w r →
          all-comp-S3 u p v q w r          
  all-comp (x ∙ y)=
    let
      u , ⇓u , p = all-comp x
      v , ⇓v , q = all-comp y
      uv , ⇓uv , pq = p v q
      pq⇓ : (⟦ x ⟧ >>= λ u₁ → ⟦ y ⟧ >>= λ v₁ → u₁ ⟨∙⟩ v₁) ⇓ uv
      pq⇓ = bind⇓ (λ u₁ → ⟦ y ⟧ >>= (λ v₁ → u₁ ⟨∙⟩ v₁))
                  ⇓u
                  (bind⇓ (λ v₁ → u ⟨∙⟩ v₁) ⇓v ⇓uv)
    in uv , pq⇓ , pq

  all-comp-S3 : ∀ {α β γ} (u : Nf (α ⇒ β ⇒ γ)) (p : Stab u)
    (v : Nf (α ⇒ β)) (q  : Stab v) (w  : Nf α) (r  : Stab w) →
      Comp (later (∞S u v w))
  all-comp-S3 u p v q w r =
    let
      uw , ⇓uw , pr = p w r
      vw , ⇓vw , qr = q w r
      uwvw , ⇓uwvw , prqr = pr vw qr
      ⇓uwvwr : (u ⟨∙⟩ w >>= (λ uw₁ → v ⟨∙⟩ w >>= λ vw₁ →  uw₁ ⟨∙⟩ vw₁)) ⇓ uwvw
      ⇓uwvwr = bind⇓ (λ uw₁ → (v ⟨∙⟩ w) >>= (λ vw₁ → uw₁ ⟨∙⟩ vw₁))
                     ⇓uw
                     (bind⇓ (λ vw₁ → uw ⟨∙⟩ vw₁) ⇓vw ⇓uwvw)
    in uwvw , later⇓ ⇓uwvwr , prqr

eval : ∀ {α} (x : Tm α) → Nf α
eval x = proj₁ (all-comp x)

eval-III : eval III ≡ S2 K0 K0
eval-III = refl

norm : ∀ {α} (x : Tm α) → Tm α
norm = reify ∘ eval

norm-III : norm III ≡ S ∙ K ∙ K
norm-III = refl
