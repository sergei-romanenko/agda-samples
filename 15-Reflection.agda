module 15-Reflection where

open import Reflection

open import Data.Empty
  using (⊥)
open import Data.Unit.Base
  using (⊤)
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_)
open import Data.List.Base
  using (List; []; _∷_)
open import Data.Maybe.Base
  using (Maybe; nothing; just; from-just)

open import Function
 using (_$_)

open import Relation.Nullary
 using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (From-yes; from-yes)

data Even : ℕ → Set where
  even0 : Even zero
  even2 : ∀ {n} → Even n → Even (2 + n)

ev2 : Even 2
ev2 = even2 even0

ev4 : Even 4
ev4 = even2 (even2 even0)

¬even1 : Even 1 → ⊥
¬even1 ()

inv-even2 : ∀ {n} → Even (2 + n) → Even n
inv-even2 (even2 even-n) = even-n

even? : (n : ℕ) → Dec (Even n)
even? zero = yes even0
even? (suc zero) = no ¬even1 -- no (λ ())
even? (suc (suc n)) with even? n
... | yes even-n = yes (even2 even-n)
... | no ¬even-n = no (λ even-2+n → ¬even-n (inv-even2 even-2+n))

ev12 : Even 12
ev12 = from-yes (even? 12)

maybe-even : (n : ℕ) → Maybe (Even n)
maybe-even zero = just even0
maybe-even (suc zero) = nothing
maybe-even (suc (suc n)) with maybe-even n
... | just even-n = just (even2 even-n)
... | nothing = nothing

mb-ev12 : Even 12
mb-ev12 = from-just $ maybe-even 12

nat2term : ℕ → Term
nat2term zero =
  con (quote zero) []
nat2term (suc n) =
  con (quote suc) (arg (arg-info visible relevant) (nat2term n) ∷ [])

mk-even : ℕ → Term
mk-even zero =
  con (quote even0) []
mk-even (suc zero) =
  unknown
mk-even (suc (suc n)) =
  con (quote even2)
      (arg (arg-info hidden relevant) (nat2term n)
        ∷ arg (arg-info visible relevant) (mk-even n) ∷ [])

magic-even : Type → Term
magic-even (def _ (arg _ (lit (nat n)) ∷ [])) = mk-even n
magic-even t = unknown

macro

  by-magic-even : Term → TC ⊤
  by-magic-even hole =
    bindTC (inferType hole) λ goal →
    unify hole (magic-even goal)
  
by-magic-even4 : Even 4
by-magic-even4 = by-magic-even

-- by-magic-even5 : Even 5
-- by-magic-even5 = by-magic-even
