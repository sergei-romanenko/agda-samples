module 14-InfiniteDescent where

{--
  Based on

    James Brotherston. Sequent Calculus Proof Systems for Inductive Definitions.
    PhD thesis, University of Edinburgh, 2006.
    http://hdl.handle.net/1842/1458
--}

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Sum as Sum
open import Data.Product as Prod
open import Data.Empty

open import Function
import Function.Related as Related

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- Mathematical induction.
-- Augustus de Morgan (1838).

indℕ : ∀ {P : ℕ → Set}
  (base : P zero)
  (step : ∀ m → P m → P (suc m)) →
  ∀ n → P n 
indℕ base step zero =
  base
indℕ base step (suc n) =
  step n (indℕ base step n)

-- Infinite descent.
-- Pierre de Fermat (1659)

descℕ : ∀ {P : ℕ → Set}
  (base : ¬ P zero)
  (step : ∀ m → P (suc m) → P m) →
  ∀ n → ¬ P n 
descℕ base step zero h =
  base h
descℕ base step (suc k) h =
  descℕ base step k (step k h)

-- suc is injective.

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- n : ℕ is either `zero` or `suc k`

caseℕ : ∀ n → n ≡ zero ⊎ (∃ λ k → n ≡ suc k)
caseℕ zero = inj₁ refl
caseℕ (suc k) = inj₂ (k , refl)

module +-suc-1 where

  P : ℕ → Set
  P n = n + 0 ≡ n

  base : P zero
  base = refl

  step : ∀ n → P n → P(suc n)
  step n n+0≡n = cong suc n+0≡n

  +-zero : ∀ n → P n
  +-zero = indℕ base step

module +-suc-2 where

  +-zero : ∀ n → n + 0 ≡ n
  +-zero zero = refl
  +-zero (suc n) = cong suc (+-zero n)

module +-suc-3 where

  open ≡-Reasoning
  
  +-zero : ∀ n → n + zero ≡ n
  +-zero zero =
    zero + zero ≡⟨⟩ zero ∎
  +-zero (suc n) =
    suc n + zero
      ≡⟨⟩
    suc (n + zero)
      ≡⟨ cong suc (+-zero n) ⟩
    suc n ∎

module n≢1+n-v1 where

  P : ℕ → Set
  P n = n ≡ suc n

  base : ¬ P zero
  base ()

  step : ∀ n → P (suc n) → P n
  step n =
    suc n ≡ suc (suc n)
      ∼⟨ suc-inj ⟩
    n ≡ suc n ∎
    where open Related.EquationalReasoning
  
  n≢1+n : ∀ n → ¬ P n
  n≢1+n = descℕ base step

module n≢1+n-v2 where

  n≢1+n : ∀ n → n ≢ suc n
  n≢1+n zero ()
  n≢1+n (suc k) 1+k≡2+k =
    n≢1+n k (suc-inj 1+k≡2+k)


module Foldℕ where

  -- `indℕ` has the same structure as `foldℕ`.

  foldℕ : (base : ℕ) (step : ℕ → ℕ → ℕ) (n : ℕ) → ℕ
  foldℕ base step zero =
    base
  foldℕ base step (suc n) =
    step n (foldℕ base step n)

  plus : (n m : ℕ) → ℕ
  plus n m = foldℕ m (const suc) n

  +~plus : ∀ n m → n + m ≡ plus n m
  +~plus zero m = refl
  +~plus (suc n) m = cong suc (+~plus n m)

mutual

  data Even : ℕ → Set where
    even0  : Even zero
    even1 : ∀ {n} → Odd n → Even (suc n)

  data Odd : ℕ → Set where
    odd1 : ∀ {n} → Even n → Odd (suc n)

odd-1 : Odd 1
odd-1 = odd1 even0

even-2 : Even 2
even-2 = even1 (odd1 even0)

-- Inversion.

¬odd-0 : ¬ Odd zero
¬odd-0 ()

even-suc : ∀ {n} → Even (suc n) → Odd n
even-suc (even1 odd-n) = odd-n

odd-suc : ∀ {n} → Odd (suc n) → Even n
odd-suc (odd1 even-n) = even-n

module Evn-2*-1 where

  -- "Ordinary" induction.

  even-2* : ∀ m → Even (m + m)
  even-2* zero = even0
  even-2* (suc n) = step (even-2* n)
    where
    open Related.EquationalReasoning renaming (sym to ∼sym)
    step : Even (n + n) → Even (suc n + suc n) 
    step =
      Even (n + n)
        ∼⟨ even1 ∘ odd1 ⟩
      Even (suc (suc (n + n)))
        ≡⟨ cong (Even ∘ suc) (sym $ +-suc n n) ⟩
      Even (suc (n + suc n))
        ≡⟨ refl ⟩
      Even (suc n + suc n)
      ∎

module Odd-2*-1 where

  -- "Infinite descent" in style of Fermat.

  ¬odd-2* : ∀ m → ¬ Odd (m + m)
  ¬odd-2* zero odd-0 =
    ¬odd-0 odd-0
  ¬odd-2* (suc zero) odd-2 =
    ¬odd-0 (even-suc (odd-suc odd-2))
  ¬odd-2* (suc (suc n)) h = ¬odd-2n odd-2n
    where
    open Related.EquationalReasoning renaming (sym to ∼sym)

    ¬odd-2n : ¬ Odd (n + n)
    ¬odd-2n = ¬odd-2* n

    down : Odd (suc (suc (n + suc (suc n)))) → Odd (n + n)
    down =
      Odd (suc (suc (n + suc (suc n))))
        ∼⟨ even-suc ∘ odd-suc ⟩
      Odd (n + suc (suc n))
        ≡⟨ cong Odd (+-suc n (suc n)) ⟩
      Odd (suc (n + suc n))
        ≡⟨ cong (Odd ∘ suc) (+-suc n n) ⟩
      Odd (suc (suc (n + n)))
        ∼⟨ even-suc ∘ odd-suc ⟩
      Odd (n + n)
      ∎

    odd-2n : Odd (n + n)
    odd-2n = down h

module Odd-2*-2 where

  -- A more Agda-idiomatic style...

  ¬odd-2* : ∀ m → ¬ Odd (m + m)
  ¬odd-2* zero ()
  ¬odd-2* (suc zero) (odd1 (even1 ()))
  ¬odd-2* (suc (suc n)) (odd1 (even1 h))
    rewrite +-suc n (suc n)
          | +-suc n n
    = ¬odd-2* n $ even-suc (odd-suc h)

module Even⊎Odd-1 where

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd zero =
    inj₁ even0
  even⊎odd (suc zero) =
    inj₂ (odd1 even0)
  even⊎odd (suc (suc n)) =
     Sum.map (even1 ∘ odd1) (odd1 ∘ even1) (even⊎odd n)

module Even⊎Odd-2 where

  mutual

    even⊎odd : ∀ n → Even n ⊎ Odd n
    even⊎odd zero =
      inj₁ even0
    even⊎odd (suc n) =
      Sum.map even1 odd1 (odd⊎even n)

    odd⊎even : ∀ n → Odd n ⊎ Even n
    odd⊎even zero =
      inj₂ even0
    odd⊎even (suc n) =
      Sum.map odd1 even1 (even⊎odd n)

module Even⊎Odd-3 where

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd zero =
    inj₁ even0
  even⊎odd (suc n) =
    ([ inj₂ , inj₁ ]′ ∘ Sum.map odd1 even1) (even⊎odd n)

module Even⊎Odd-4 where

  even⊎odd : ∀ n → Even n ⊎ Odd n
  even⊎odd n =
    indℕ {λ n → Even n ⊎ Odd n}
      (inj₁ even0) (λ m → [ inj₂ ∘ odd1 , inj₁ ∘ even1 ]′) n

module Even×Odd-1 where

  -- "Infinite descent" in style of Fermat.

  ¬even×odd : ∀ m → ¬ (Even m × Odd m)
  ¬even×odd zero (even-0 , odd-0) =
    ¬odd-0 odd-0
  ¬even×odd (suc n) (even-suc-n , odd-suc-n) =
    ¬even×odd n (odd-suc odd-suc-n , even-suc even-suc-n)

module Even×Odd-2 where

  -- A more Agda-idiomatic style...

  ¬even×odd : ∀ m → Even m → Odd m → ⊥
  ¬even×odd zero even-0 ()
  ¬even×odd (suc n) (even1 odd-n) (odd1 even-n) =
    ¬even×odd n even-n odd-n


-- The R example

data R : (x y : ℕ) → Set where
  zy : ∀ {y} → R zero y
  xz : ∀ {x} → R x zero
  ss : ∀ {x y} → R (suc (suc x)) y → R (suc x) (suc y)

all-r : ∀ x y → R x y
all-r x zero = xz
all-r zero (suc y) = zy
all-r (suc x) (suc y) =
  ss (all-r (suc (suc x)) y)

-- The P & Q example

mutual

  data P : (x : ℕ) → Set where
    pz : P zero
    ps : ∀ {x} → P x → Q x (suc x) → P (suc x)

  data Q : (x y : ℕ) → Set where
    qz : ∀ {x} → Q x zero
    qs : ∀ {x y} → P x → Q x y → Q x (suc y)

mutual

  all-q : ∀ x y → Q x y
  all-q x zero = qz
  all-q x (suc y) =
    qs (all-p x) (all-q x y)

  all-p : ∀ x → P x
  all-p zero = pz
  all-p (suc x) =
    ps (all-p x) (all-q x (suc x))

-- The N′ example

  data N′ : (x y : ℕ) → Set where
    nz : ∀ {y} → N′ zero y
    ns : ∀ {x y} → N′ y x → N′ (suc x) y

mutual

  all-n : ∀ x y → N′ x y
  all-n zero y = nz
  all-n (suc x) y = ns (all-n y x)

-- The "problem" with Agda is that it is a statically-typed language,
-- while Brotherston deals with an untyped language.
-- Thus some examples are too easy to reproduce in Agda.
-- Hence, let us define natural numbers in "unnatural" way,
-- in order that they be a subset of an Agda type.

open import Data.Bool
open import Data.List

data BN : (bs : List Bool) → Set where
  zero : BN []
  suc  : ∀ {bs} → BN bs → BN (true ∷ bs)

bn3 : BN (true ∷ true ∷ true ∷ [])
bn3 = suc (suc (suc zero))

mutual

  data BE : (bs : List Bool) → Set where
    be0 : BE []
    be1 : ∀ {bs} → BO bs → BE (true ∷ bs)

  data BO : (bs : List Bool) → Set where
    bo1 : ∀ {bs} → BE bs → BO (true ∷ bs)

be2 : BE (true ∷ true ∷ [])
be2 = be1 (bo1 be0)

bo3 : BO (true ∷ true ∷ true ∷ [])
bo3 = bo1 (be1 (bo1 be0))

module BE⊎BO-1 where

  be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
  be⊎bo zero = inj₁ be0
  be⊎bo (suc zero) = inj₂ (bo1 be0)
  be⊎bo (suc (suc bn)) =
    Sum.map (be1 ∘ bo1) (bo1 ∘ be1) (be⊎bo bn)

module BE⊎BO-2 where

  mutual

    be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
    be⊎bo zero = inj₁ be0
    be⊎bo (suc bn) =
      Sum.map be1 bo1 (bo⊎be bn)

    bo⊎be : ∀ {n} (bn : BN n) → BO n ⊎ BE n
    bo⊎be zero = inj₂ be0
    bo⊎be (suc bn) =
      Sum.map bo1 be1 (be⊎bo bn)

module BE⊎BO-3 where

  be⊎bo : ∀ {n} (bn : BN n) → BE n ⊎ BO n
  be⊎bo zero = inj₁ be0
  be⊎bo (suc bn) =
    [ inj₂ , inj₁ ]′ (Sum.map bo1 be1 (be⊎bo bn))

module BE⊎BO-BN-1 where

  be-bn : ∀ {n} (be : BE n) → BN n
  be-bn be0 = zero
  be-bn (be1 (bo1 be)) = suc (suc (be-bn be))

  be⊎bo-bn : ∀ {n} (beo : BE n ⊎ BO n) → BN n
  be⊎bo-bn (inj₁ be) = be-bn be
  be⊎bo-bn (inj₂ (bo1 be)) = suc (be-bn be)

module BE⊎BO-BN-2 where

  mutual

    be-bn : ∀ {n} (be : BE n) → BN n
    be-bn be0 = zero
    be-bn (be1 bo) = suc (bo-bn bo)

    bo-bn : ∀ {n} (bo : BO n) → BN n
    bo-bn (bo1 be) = suc (be-bn be)

  be⊎bo-bn : ∀ {n} (beo : BE n ⊎ BO n) → BN n
  be⊎bo-bn = [ be-bn , bo-bn ]′

-- Complete induction

data Acc<′ (n : ℕ) : Set where
  acc : (rs : ∀ m → m <′ n → Acc<′ m) → Acc<′ n

mutual

  <′-acc : ∀ n m → m <′ n → Acc<′ m
  <′-acc .(suc m) m ≤′-refl = all-acc<′ m
  <′-acc .(suc n) m (≤′-step {n} m<′n) = <′-acc n m m<′n

  all-acc<′ : ∀ n → Acc<′ n
  all-acc<′ n = acc (<′-acc n)

ind<′-acc : ∀ {P : ℕ → Set}
  (step : ∀ n → (∀ m → m <′ n → P m) → P n) →
  ∀ n → Acc<′ n → P n 
ind<′-acc step n (acc rs) =
  step n (λ m m<′n → ind<′-acc step m (rs m m<′n))

ind<′ : ∀ {P : ℕ → Set}
  (step : ∀ n → (∀ m → m <′ n → P m) → P n) →
  ∀ n → P n 
ind<′ step n =
  ind<′-acc step n (all-acc<′ n)
