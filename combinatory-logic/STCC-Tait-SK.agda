{-
  Normalization theorem for the Simply Typed Combinators:

    "every typable term is normalizable".

  Based on

    Ana Bove and Venanzio Capretta. 2001.
    Nested General Recursion and Partiality in Type Theory.
    In Proceedings of the 14th International Conference on Theorem Proving
    in Higher Order Logics (TPHOLs '01),
    Richard J. Boulton and Paul B. Jackson (Eds.).
    Springer-Verlag, London, UK, UK, 121-135. 

  and

    Thorsten Altenkirch and James Chapman. 2006.
    Tait in one big step.
    In Proceedings of the 2006 international conference on Mathematically
    Structured Functional Programming (MSFP'06),
    Conor McBride and Tarmo Uustalu (Eds.).
    British Computer Society, Swinton, UK, UK, 4-4. 

-}


module STCC-Tait-SK where
open import Data.Empty
open import Data.Product

open import Function
import Function.Related as Related

open import Relation.Binary.PropositionalEquality as P
  renaming ([_] to ≡[_])

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqReasoning

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
-- Convertibility
--

infix 4 _≈_

data _≈_  : {α : Ty} (x y : Tm α) → Set where
  ≈refl  : ∀ {α} {x : Tm α} →
             x ≈ x
  ≈sym   : ∀ {α} {x y : Tm α} →
             x ≈ y → y ≈ x
  ≈trans : ∀ {α} {x y z : Tm α} →
             x ≈ y → y ≈ z → x ≈ z
  ≈K     : ∀ {α β} {x : Tm α} {y : Tm β} →
             K ∙ x ∙ y ≈ x
  ≈S     : ∀ {α β γ} {x : Tm (α ⇒ β ⇒ γ)} {y : Tm (α ⇒ β)} {z : Tm α} →
             S ∙ x ∙ y ∙ z ≈ (x ∙ z) ∙ (y ∙ z)
  ∙-cong : ∀ {α β} {x y : Tm (α ⇒ β)} {x′ y′ : Tm α} →
             x ≈ y → x′ ≈ y′ → x ∙ x′ ≈ y ∙ y′

≈setoid : {α : Ty} → Setoid _ _

≈setoid {α} = record
  { Carrier = Tm α
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans } }

module ≈-Reasoning {α : Ty} = EqReasoning (≈setoid {α})

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
-- There is no non-functional normal form!
--

∄-Nf-⋆ : (u : Nf ⋆) → ⊥
∄-Nf-⋆ ()

--
-- A "naive" big-step normalization function.
--

module NaiveNorm where

  infixl 5 _⟨∙⟩_

  {-# TERMINATING #-}

  _⟨∙⟩_ : ∀ {α β} (u : Nf (α ⇒ β)) (w : Nf α) → Nf β
  K0 ⟨∙⟩ w = K1 w
  K1 u ⟨∙⟩ w = u
  S0 ⟨∙⟩ w = S1 w
  S1 u ⟨∙⟩ w = S2 u w
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
-- Big-step reduction.
--

-- Since Agda's termination checker is unable to prove that
-- the "naive" normalazation function is total, let's rewrite
-- this function in form of a relation.

infix 4 _⇓_ _⟨∙⟩_⇓_

data _⟨∙⟩_⇓_ : ∀ {α β} (x : Nf (α ⇒ β)) (y : Nf α) (u : Nf β) → Set where
  K0⇓ : ∀ {α β w} →
    K0 {α} {β} ⟨∙⟩ w ⇓ K1 w
  K1⇓ : ∀ {α β u w} →
    K1 {α} {β} u ⟨∙⟩ w ⇓ u
  S0⇓ : ∀ {α β γ w} →
    S0 {α} {β} {γ} ⟨∙⟩ w ⇓ S1 w
  S1⇓ : ∀ {α β γ u w} →
    S1 {α} {β} {γ} u ⟨∙⟩ w ⇓ S2 u w
  S2⇓ : ∀ {α β γ u v w uw vw uwvw}
    (⇓uw : u ⟨∙⟩ w ⇓ uw) (⇓vw : v ⟨∙⟩ w ⇓ vw) (uwvw⇓ : uw ⟨∙⟩ vw ⇓ uwvw) →
    S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ uwvw

data _⇓_ : {α : Ty} (x : Tm α) (u : Nf α) → Set where 
  K⇓ : ∀ {α β : Ty} →
    K {α} {β} ⇓ K0
  S⇓ : ∀ {α β γ : Ty} →
    S {α} {β} {γ} ⇓ S0
  ∙⇓ : ∀ {α β : Ty} {x : Tm (α ⇒ β)} {y : Tm α} {u v uv}
    (x⇓u : x ⇓ u) (y⇓v : y ⇓ v) (⇓uv : u ⟨∙⟩ v ⇓ uv)  →
    x ∙ y ⇓ uv

--
-- Determinism: x ⇓ u → x ⇓ v → u ≡ v
--

⟨∙⟩⇓-det : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w w′ : Nf β} →
  u ⟨∙⟩ v ⇓ w → u ⟨∙⟩ v ⇓ w′ → w ≡ w′
⟨∙⟩⇓-det K0⇓ K0⇓ = refl
⟨∙⟩⇓-det K1⇓ K1⇓ = refl
⟨∙⟩⇓-det S0⇓ S0⇓ = refl
⟨∙⟩⇓-det S1⇓ S1⇓ = refl
⟨∙⟩⇓-det (S2⇓ ⇓uw ⇓vw ⇓uwvw) (S2⇓ ⇓uw′ ⇓vw′ ⇓uwvw′)
  rewrite ⟨∙⟩⇓-det ⇓uw ⇓uw′ | ⟨∙⟩⇓-det ⇓vw ⇓vw′
  = ⟨∙⟩⇓-det ⇓uwvw ⇓uwvw′

⇓-det : ∀ {α} {x : Tm α} {u u′ : Nf α} →
  x ⇓ u → x ⇓ u′ → u ≡ u′
⇓-det K⇓ K⇓ = refl
⇓-det S⇓ S⇓ = refl
⇓-det (∙⇓ x⇓u y⇓v uv⇓w) (∙⇓ x⇓u′ y⇓v′ u′v′⇓w′)
  rewrite ⇓-det x⇓u x⇓u′ | ⇓-det y⇓v y⇓v′
  = ⟨∙⟩⇓-det uv⇓w u′v′⇓w′

--
-- Soundness: terms are convertible to their normal forms
--     x ⇓ u → x ≈ reify u
-- 

⟨∙⟩⇓-sound : ∀ {α β} {u : Nf (α ⇒ β)} {v : Nf α} {w : Nf β} →
  u ⟨∙⟩ v ⇓ w → reify u ∙ reify v ≈ reify w
⟨∙⟩⇓-sound K0⇓ = ≈refl
⟨∙⟩⇓-sound K1⇓ = ≈K
⟨∙⟩⇓-sound S0⇓ = ≈refl
⟨∙⟩⇓-sound S1⇓ = ≈refl
⟨∙⟩⇓-sound (S2⇓ {u = u} {v} {w} {uw} {vw} {uwvw} ⇓uw ⇓vw ⇓uwvw) = begin
  S ∙ reify u ∙ reify v ∙ reify w
    ≈⟨ ≈S ⟩
  (reify u ∙ reify w) ∙ (reify v ∙ reify w)
    ≈⟨ ∙-cong (⟨∙⟩⇓-sound ⇓uw) (⟨∙⟩⇓-sound ⇓vw) ⟩
  reify uw ∙ reify vw
    ≈⟨ ⟨∙⟩⇓-sound ⇓uwvw ⟩
  reify uwvw
  ∎
  where open ≈-Reasoning

⇓-sound : ∀ {α} {x : Tm α} {u : Nf α} →
  x ⇓ u → x ≈ reify u
⇓-sound K⇓ = ≈refl
⇓-sound S⇓ = ≈refl
⇓-sound (∙⇓ {x = x} {y} {u} {v} {uv} x⇓u y⇓v ⇓uv) = begin
  x ∙ y
    ≈⟨ ∙-cong (⇓-sound x⇓u) (⇓-sound y⇓v) ⟩
  reify u ∙ reify v
    ≈⟨ ⟨∙⟩⇓-sound ⇓uv ⟩
  reify uv
  ∎
  where open ≈-Reasoning

--
-- Now we are going to prove that
--     ∀ x → ∃ λ u → x ⇓ u
-- The main idea is to define a "Strong Computability" predicate
-- on normal forms by induction over types.
--

--
-- "Strong computability" on normal forms.
--

SCN : ∀ {α} (u : Nf α) → Set
SCN {⋆} ()
SCN {α ⇒ β} u = ∀ v → SCN v → ∃ λ w → u ⟨∙⟩ v ⇓ w × SCN w

--
-- All normal forms are strongly computable!
--    ∀ {α} (u : Nf α) → SCN u
--

all-scn-K2 : ∀ {α β} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → K1 {α} {β} u ⟨∙⟩ v ⇓ w × SCN w
all-scn-K2 u p v q =
  u , K1⇓ , p

all-scn-K1 : ∀ {α β} u (p : SCN u) →
  ∃ λ w → K0 {α} {β} ⟨∙⟩ u ⇓ w × SCN w
all-scn-K1 u p =
  K1 u , K0⇓ , all-scn-K2 u p

all-scn-S3 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) w (r : SCN w) →
  ∃ λ w′ → S2 {α} {β} {γ} u v ⟨∙⟩ w ⇓ w′ × SCN w′
all-scn-S3 u p v q w r =
  let uw , uw⇓ , pr = p w r
      vw , vw⇓ , qr = q w r
      uwvw , uwvw⇓ , prqr = pr vw qr
  in uwvw , S2⇓ uw⇓ vw⇓ uwvw⇓ , prqr

all-scn-S2 : ∀ {α β γ} u (p : SCN u) v (q : SCN v) →
  ∃ λ w → S1 {α} {β} {γ} u ⟨∙⟩ v ⇓ w × SCN w
all-scn-S2 u p v q =
  S2 u v , S1⇓ , all-scn-S3 u p v q

all-scn-S1 : ∀ {α β γ} u (p : SCN u) →
  ∃ λ w → S0 {α} {β} {γ} ⟨∙⟩ u ⇓ w × SCN w
all-scn-S1 u p =
  S1 u , S0⇓ , all-scn-S2 u p

-- ∀ {α} (u : Nf α) → SCN u

all-scn : ∀ {α} (u : Nf α) → SCN u

all-scn K0 =
  all-scn-K1
all-scn (K1 u) =
  all-scn-K2 u (all-scn u)
all-scn S0 =
  all-scn-S1
all-scn (S1 u) =
  all-scn-S2 u (all-scn u)
all-scn (S2 u v) =
  all-scn-S3 u (all-scn u) v (all-scn v)

--
-- "Strong computability" on terms.
--

SC : ∀ {α} (t : Tm α) → Set
SC t = ∃ λ u → t ⇓ u × SCN u

--
-- All terms are strongly computable!
--    ∀ {α} (x : Tm α) → SC u
--

all-sc : ∀ {α} (x : Tm α) → SC x

all-sc K =
  K0 , K⇓ , all-scn-K1
all-sc S =
  S0 , S⇓ , all-scn-S1
all-sc (x ∙ y) =
  let u , ⇓u , p = all-sc x
      v , ⇓v , q = all-sc y
      uv , ⇓uv , pq = p v q
  in uv , ∙⇓ ⇓u ⇓v ⇓uv , pq

--
-- Completeness: the normal forms of two convertible terms are equal
--     x ≈ y → x ⇓ u → y ⇓ v → u ≡ v
--

⇓-complete : ∀ {α} {x y : Tm α} {u v : Nf α} →
  x ≈ y → x ⇓ u → y ⇓ v → u ≡ v

⇓-complete ≈refl x⇓u x⇓v =
  ⇓-det x⇓u x⇓v
⇓-complete (≈sym x≈y) x⇓u x⇓v =
  sym $ ⇓-complete x≈y x⇓v x⇓u
⇓-complete (≈trans {α} {x} {z} {y} x≈z z≈y) x⇓u y⇓v =
  let w , z⇓w , r = all-sc z
  in trans (⇓-complete x≈z x⇓u z⇓w) (⇓-complete z≈y z⇓w y⇓v)
⇓-complete ≈K (∙⇓ (∙⇓ K⇓ x⇓′ K0⇓) y⇓ K1⇓) x⇓′′ =
  ⇓-det x⇓′ x⇓′′
⇓-complete ≈S
           (∙⇓ (∙⇓ (∙⇓ S⇓ x⇓ S0⇓) y⇓ S1⇓) z⇓ (S2⇓ ⇓uw ⇓vw ⇓uwvw))
           xzyz⇓ =
  ⇓-det (∙⇓ (∙⇓ x⇓ z⇓ ⇓uw) (∙⇓ y⇓ z⇓ ⇓vw) ⇓uwvw) xzyz⇓
⇓-complete (∙-cong x≈y x′≈y′) (∙⇓ x⇓u x′⇓u′ ⇓uv) (∙⇓ y⇓v y′⇓v′ ⇓u′v′)
  rewrite ⇓-complete x≈y x⇓u y⇓v | ⇓-complete x′≈y′ x′⇓u′ y′⇓v′
  = ⟨∙⟩⇓-det ⇓uv ⇓u′v′

--
-- All terms are normalizable.
--    ∀ x → ∃ λ u → x ⇓ u
--

all-⇓ : ∀ {α} (x : Tm α) → ∃ λ u → x ⇓ u
all-⇓ x =
  let u , ⇓u , p = all-sc x
  in u , ⇓u

module TerminatingNorm where

  norm : ∀ {α} → Tm α → Tm α
  norm x = reify (proj₁ (all-⇓ x))

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl

--
-- Now, as suggested by Bove and Capretta, we add to the normalization function
-- an additional argument: a proof of the existence of the normal form.
--
-- Since, unlike Coq, Agda doesn't make a distinction
-- between `Set` and `Prop`, it's not clear if the trick
-- by Bove and Capretta makes sense (for Agda)?
-- 

⟨∙⟩⇓-subst : ∀ {α β} {u u′ : Nf (α ⇒ β)} {v v′ : Nf α} {w} →
  u′ ≡ u → v′ ≡ v → u ⟨∙⟩ v ⇓ w → u′ ⟨∙⟩ v′ ⇓ w
⟨∙⟩⇓-subst refl refl h = h

{-# TERMINATING #-}

apply : ∀ {α β} (u : Nf (α ⇒ β)) (v : Nf α)
  {w} (uv⇓ : u ⟨∙⟩ v ⇓ w) → ∃ λ w′ → w′ ≡ w
apply K0 u K0⇓ = K1 u , refl
apply (K1 u) v K1⇓ = u , refl
apply S0 u S0⇓ = S1 u , refl
apply (S1 u) v S1⇓ = S2 u v , refl
apply (S2 u v) w (S2⇓ {uwvw = uwvw} uw⇓ vw⇓ uwvw⇓) =
  let uw′ , uw′≡uw = apply u w uw⇓
      vw′ , vw′≡vw = apply v w vw⇓
  in apply uw′ vw′ (⟨∙⟩⇓-subst uw′≡uw vw′≡vw uwvw⇓)

eval : ∀ {α} (x : Tm α) {u} (x⇓ : x ⇓ u) → ∃ λ u′ → u′ ≡ u
eval K K⇓ = K0 , refl
eval S S⇓ = S0 , refl
eval (x ∙ y) (∙⇓ {uv = uv} x⇓ y⇓ ⇓uv) =
  let u′ , u′≡u = eval x x⇓
      v′ , v′≡v = eval y y⇓
  in apply u′ v′ (⟨∙⟩⇓-subst u′≡u v′≡v ⇓uv)


module BoveCaprettaNorm where

  norm : ∀ {α} → Tm α → Tm α
  norm x =
    let u , x⇓ = all-⇓ x
    in reify (proj₁ (eval x {u} x⇓))

  norm-III : norm III ≡ S ∙ K ∙ K
  norm-III = refl
