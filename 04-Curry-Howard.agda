module 04-Curry-Howard where

open import Function

{- Conceptually -}

-- Prop : Set₁
-- Prop = Set

{- implication -}

module SKI where

  I : {P : Set} → P → P
  I p = {!!}

  K : {P Q : Set} → P → Q → P
  K p q = {!!}

  S : {A B C : Set} → (A → B → C) → (A → B) → A → C
  S p q r = {!!}

  I' : {P : Set}→ P → P
  I' {P}  = S K (K {P}{P})

mp : {P Q : Set} → (P → Q) → P → Q
mp pq p = {!!}

comp : {P Q R : Set} → (P → Q) → (Q → R) → P → R
comp pq qr p = {!!}

comp' : {P Q R : Set} → (P → Q) → (Q → R) → P → R
comp' pq qr = qr ∘ pq

{- Conjunction ×

   A proof of P × Q is a proof of P and a proof of Q.

  data _×_ (P Q : Set) : Set where
    _,_ : P → Q → P × Q

   Actually, × is a special case of a more general construct:

  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  _×_ : ∀ (A : Set) (B : Set) → Set
  A × B = Σ A (λ _ → B)

-}

open import Data.Product

{- × is commutative. -}

×-comm : {P Q : Set} → P × Q → Q × P
×-comm (p , q) = {!!}

--proj₁ (x , y) = x
--proj₂ (x , y) = y
--< f , g > x = (f x , g x)

×-comm' : {P Q : Set} → P × Q → Q × P
×-comm' pq = < proj₂ , proj₁ > pq


{- Disjunction ⊎

   A proof of P ⊎ Q is either a proof of P prefixed with inj₁ or
   a proof of Q prefixed with inj₂.

  data _⊎_ (P Q : Set) : Set where
    inj₁ : P → P ⊎ Q
    inj₂ : Q → P ⊎ Q
-}

open import Data.Sum

{- ⊎ is commutative -}

⊎-comm : {P Q : Set} → P ⊎ Q → Q ⊎ P
⊎-comm pq = {!!}

-- [ f , g ] (inj₁ x) = f x
-- [ f , g ] (inj₂ y) = g y

⊎-comm' : {P Q : Set} → P ⊎ Q → Q ⊎ P
⊎-comm' pq = [ inj₂ , inj₁ ] pq

{- Distributivity of × over ⊎ -}

distrib-×-⊎-1 : {P Q R : Set} → P × (Q ⊎ R) → (P × Q) ⊎ (P × R)
distrib-×-⊎-1 pqr = {!!}

{- The other direction -}

distrib-×-⊎-2 : {P Q R : Set} → (P × Q) ⊎ (P × R) → P × (Q ⊎ R)
distrib-×-⊎-2 pqpr = {!!}

{- True (⊤ = \top) has a trivial proof.

  record ⊤ : Set where
    constructor tt
-}

open import Data.Unit

{- False (⊥ = \bot) has no proof.

  data ⊥ : Set where

  ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
  ⊥-elim ()

-}

open import Data.Empty

{- Negation ¬

  ¬ : Set → Set
  ¬ P = P → ⊥

  data Dec (P : Set) : Set where
    yes : ( p :   P) → Dec P
    no  : (¬p : ¬ P) → Dec P
-}

open import Relation.Nullary

{- Some basic facts about negation. -}

contradict : {P : Set} → ¬ (P × ¬ P)
contradict (np , p) = {!!}

contrapos : {P Q : Set} → (P → Q) → ¬ Q → ¬ P
contrapos pq nq p = {!!}

-- We show that Peirce's law is equivalent to the Law of
-- Excluded Middle (EM).

peirce : Set₁
peirce = ∀ (P Q : Set) → ((P → Q) → P) → P

em : Set₁
em = ∀ (R : Set) → R ⊎ ¬ R

peirce→em : peirce → em
peirce→em h R = {!!}

em→peirce : em → peirce
em→peirce e P Q h with e P
... | eP = {!!}


{- Universal quantification. Given a set A, and a predicate P : A → Set
   (x : A) →  P x means that P a is true (inhabited) for all a : A.

   ∀ x is an abbreviation for (x ∶ _).
-}

∀×-lem-1 : {A : Set} {P Q : A → Set} → 
  (∀ a → P a × Q a) → (∀ a → P a) × (∀ a → Q a)
∀×-lem-1 pq = {!!}

∀×-lem-2 : {A : Set} {P Q : A → Set} → 
  (∀ a → P a) × (∀ a → Q a) → (∀ a → P a × Q a) 
∀×-lem-2 (p , q) = {!!}

{- Existence. Given a set A, and a predicate P : A → Set
   Σ A P means that there is an (x : A) such that (P x).
   Technically, if (x , p) : Σ A P, then (x : A) and
   p x : P x.

  ∃ : ∀ {A : Set} → (A → Set) → Set
  ∃ = Σ _

-}


∀∃-lem-1 : {A : Set} {P : A → Set} {Q : Set} → 
  (∀ a → P a → Q) → (∃ λ a → P a) → Q
∀∃-lem-1 pq (a , p) = {!!}

∀∃-lem-2 : {A : Set} {P : A → Set} {Q : Set} → 
  ((∃ λ a → P a) → Q) → (∀ a → P a → Q)
∀∃-lem-2 pq = λ a p → {!!}
