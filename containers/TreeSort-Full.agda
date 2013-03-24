-- The algorithm and the treatment of ordering information is taken
-- from Conor McBride's talk "Pivotal pragmatism".

-- The module is parametrised by a total relation.

open import Data.Sum

module TreeSort-Full
  {Key : Set}
  (_≤_ : Key → Key → Set)
  (≤-total : ∀ x y → x ≤ y ⊎ y ≤ x)
 where

open import Level
  using (Lift; lift)


open import Data.List
  hiding ([_])

open import Data.Empty
open import Data.Unit
  using (⊤; tt)
open import Data.Product


open import Function

open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Function.Inverse
  using (_↔_)

import Function.Related as Related

open import Algebra
  using (module CommutativeSemiring)
open import Function.Related.TypeIsomorphisms
  using(×⊎-CommutativeSemiring)
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)


------------------------------------------------------------------------
-- Extending the order with new minimum and maximum elements

-- A extended with a new minimum and maximum.

data Key⁺ : Set where
  ⊥⁺ ⊤⁺ : Key⁺
  [_]   : (x : Key) → Key⁺

infix 4 _≤⁺_

_≤⁺_ : Key⁺ → Key⁺ → Set

⊥⁺    ≤⁺ _     = Lift ⊤
[ x ] ≤⁺ [ y ] = x ≤ y
_     ≤⁺ ⊤⁺    = Lift ⊤
_     ≤⁺ _     = Lift ⊥

-- A pair of ordering constraints (written as a record type to aid
-- type inference).

infix 4 _≤≤_

record _≤[_]≤_ (l : Key⁺) (x : Key) (u : Key⁺) : Set where
  constructor _≤≤_
  field
    lower : l ≤⁺ [ x ]
    upper : [ x ] ≤⁺ u

------------------------------------------------------------------------
-- Ordered lists

data Ordered-list (l u : Key⁺) : Set where
  nil  : (l≤u : l ≤⁺ u) → Ordered-list l u
  cons : (x : Key) (xs : Ordered-list [ x ] u) (l≤x : l ≤⁺ [ x ]) →
         Ordered-list l u

-- Conversion to ordinary lists.

to-list : ∀ {l u} → Ordered-list l u → List Key

to-list (nil l≤u)       = []
to-list (cons x xs l≤x) = x ∷ to-list xs

------------------------------------------------------------------------
-- Unbalanced binary search trees

infix 5 node

syntax node x lx xu = lx [- x -] xu

data Search-tree (l u : Key⁺) : Set where
  leaf : (l≤u : l ≤⁺ u) → Search-tree l u
  node : (x : Key) (lx : Search-tree l [ x ]) (xu : Search-tree [ x ] u) →
         Search-tree l u

-- AnyT.

AnyT : ∀ {l u} → (Key → Set) → Search-tree l u → Set

AnyT P (leaf _)     = Lift ⊥
AnyT P (node x l r) = AnyT P l ⊎ P x ⊎ AnyT P r

-- AnyL.

AnyL : (Key → Set) → List Key → Set

AnyL P [] = Lift ⊥
AnyL P (x ∷ xs) = P x ⊎ AnyL P xs

------------------------------------------------------------------------
-- An ad-hoc universe consisting of lists, ordered lists and search
-- trees

-- The purpose of this universe is to allow overloading of Any, _∈_
-- and _≈-bag_.

-- Codes.

data Kind : Set where
  list ordered-list search-tree : Kind

-- Index type.
--
-- Note that Agda infers values of type ⊤ automatically.

Index : Kind → Set

Index list = Lift ⊤
Index _    = Key⁺

-- Interpretation.

⟦_⟧ : (k : Kind) → (Index k → Index k → Set)

⟦ list         ⟧ _ _ = List Key
⟦ ordered-list ⟧ l u = Ordered-list l u
⟦ search-tree  ⟧ l u = Search-tree l u

-- Any.

Any : ∀ {k l u} → (Key → Set) → (⟦ k ⟧ l u → Set)

Any {list}         = AnyL
Any {ordered-list} = λ P → AnyL P ∘ to-list
Any {search-tree}  = AnyT

-- Membership.

infix 4 _∈_

_∈_ : ∀ {k l u} → Key → ⟦ k ⟧ l u → Set
x ∈ xs = Any (_≡_ x) xs

-- Bag equivalence.

infix 4 _≈-bag_

_≈-bag_ : ∀ {k₁ k₂ l₁ u₁ l₂ u₂} → ⟦ k₁ ⟧ l₁ u₁ → ⟦ k₂ ⟧ l₂ u₂ → Set
xs ≈-bag ys = ∀ z → z ∈ xs ↔ z ∈ ys


------------------------------------------------------------------------
-- Singleton trees

singleton : ∀ {l u} (x : Key) → l ≤[ x ]≤ u → Search-tree l u
singleton x (l≤x ≤≤ x≤u) = leaf l≤x [- x -] leaf x≤u

-- Any lemma for singleton.

Any-singleton : ∀ (P : Key → Set) {l u x} (l≤x≤u : l ≤[ x ]≤ u) →
                Any P (singleton x l≤x≤u) ↔ P x
Any-singleton P {x = x} l≤x≤u =
  Any P (singleton x l≤x≤u)
    ↔⟨ _ ∎ ⟩
  (Lift ⊥ ⊎ P x ⊎ Lift ⊥)
    ↔⟨ proj₁ ×⊎.+-identity (P x ⊎ Lift ⊥) ⟩
  (P x ⊎ Lift ⊥)
    ↔⟨ proj₂ ×⊎.+-identity (P x) ⟩
  P x ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Insertion into a search tree

insert : ∀ {l u} (x : Key) → Search-tree l u → l ≤[ x ]≤ u →
         Search-tree l u
insert x (leaf _) l≤x≤u = singleton x l≤x≤u
insert x (ly [- y -] yu) (l≤x ≤≤ x≤u) with ≤-total x y
... | inj₁ x≤y = insert x ly (l≤x ≤≤ x≤y) [- y -] yu
... | inj₂ y≤x = ly [- y -] insert x yu (y≤x ≤≤ x≤u)

-- Any lemma for insert.

Any-insert : ∀ (P : Key → Set) {l u} x t (l≤x≤u : l ≤[ x ]≤ u) →
             Any P (insert x t l≤x≤u) ↔ (P x ⊎ Any P t)

Any-insert P {l} {u} x (leaf l≤u) l≤x≤u =
  Any P (insert x (leaf l≤u) l≤x≤u)
    ↔⟨ _ ∎ ⟩
  Any P (singleton x l≤x≤u)
    ↔⟨ Any-singleton P l≤x≤u ⟩
  P x
    ↔⟨ sym $ proj₂ ×⊎.+-identity (P x) ⟩
  (P x ⊎ Lift ⊥)
    ↔⟨ _ ∎ ⟩
  (P x ⊎ Any P (leaf {l = l} {u = u} l≤u)) ∎
  where open Related.EquationalReasoning

Any-insert P x (ly [- y -] yu) (l≤x ≤≤ x≤u) with ≤-total x y
... | inj₁ x≤y =
  Any P (insert x ly (l≤x ≤≤ x≤y) [- y -] yu)
    ↔⟨ _ ∎ ⟩
  (Any P (insert x ly (l≤x ≤≤ x≤y)) ⊎ P y ⊎ Any P yu)
    ↔⟨ Any-insert P x ly (l≤x ≤≤ x≤y) ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
  ((P x ⊎ Any P ly) ⊎ P y ⊎ Any P yu)
     ↔⟨ ×⊎.+-assoc (P x) (AnyT P ly) (P y ⊎ AnyT P yu) ⟩
  (P x ⊎ Any P ly ⊎ P y ⊎ Any P yu)
    ↔⟨ _ ∎ ⟩ 
  (P x ⊎ Any P (ly [- y -] yu))
  ∎
  where open Related.EquationalReasoning
... | inj₂ y≤x =
  Any P (ly [- y -] insert x yu (y≤x ≤≤ x≤u))
    ↔⟨ _ ∎ ⟩
  (AnyT P ly ⊎ P y ⊎ AnyT P (insert x yu (y≤x ≤≤ x≤u)))
    ↔⟨  _ ∎ ⟨ ×⊎.+-cong ⟩
        (_ ∎ ⟨ ×⊎.+-cong ⟩ Any-insert P x yu (y≤x ≤≤ x≤u)) ⟩
  (AnyT P ly ⊎ P y ⊎ P x ⊎ AnyT P yu)
    ↔⟨ shuffle ⟩
  (P x ⊎ AnyT P ly ⊎ P y ⊎ AnyT P yu) ∎
  where
    open Related.EquationalReasoning
    shuffle : ∀ {A B C D : Set} →
      (B ⊎ C ⊎ A ⊎ D) ↔ (A ⊎ B ⊎ C ⊎ D)
    shuffle {A} {B} {C} {D} =
      (B ⊎ C ⊎ A ⊎ D)
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (sym $ ×⊎.+-assoc C A D) ⟩
      (B ⊎ (C ⊎ A) ⊎ D)
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ (×⊎.+-comm C A ⟨ ×⊎.+-cong ⟩ _ ∎) ⟩
      (B ⊎ (A ⊎ C) ⊎ D)
        ↔⟨ sym $ ×⊎.+-assoc B (A ⊎ C) D ⟩
      ((B ⊎ (A ⊎ C)) ⊎ D)
        ↔⟨ (sym $ ×⊎.+-assoc B A C) ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      (((B ⊎ A) ⊎ C) ⊎ D)
        ↔⟨ ×⊎.+-comm B A ⟨ ×⊎.+-cong ⟩ _ ∎ ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      (((A ⊎ B) ⊎ C) ⊎ D)
        ↔⟨ ×⊎.+-assoc A B C ⟨ ×⊎.+-cong ⟩ _ ∎ ⟩
      ((A ⊎ (B ⊎ C)) ⊎ D)
        ↔⟨ ×⊎.+-assoc A (B ⊎ C) D ⟩
      (A ⊎ (B ⊎ C) ⊎ D)
        ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ ×⊎.+-assoc B C D ⟩
      (A ⊎ B ⊎ C ⊎ D) ∎

------------------------------------------------------------------------
-- Turning an unordered list into a search tree

to-search-tree : List Key → Search-tree ⊥⁺ ⊤⁺
to-search-tree =
 foldr (λ x t → insert x t (lift tt ≤≤ lift tt)) (leaf (lift tt))

-- No elements are added or removed.

to-search-tree-lemma : (xs : List Key) → to-search-tree xs ≈-bag xs

to-search-tree-lemma [] z =
  z ∈ to-search-tree []
    ↔⟨ _ ∎ ⟩
  z ∈ leaf {⊥⁺} {⊤⁺} (lift tt)
    ↔⟨ _ ∎ ⟩
  Lift ⊥
    ↔⟨ _ ∎ ⟩
  z ∈ ([] ∶ List Key) ∎
  where open Related.EquationalReasoning

to-search-tree-lemma (x ∷ xs) z =
  z ∈ insert x (to-search-tree xs) _
    ↔⟨ Any-insert (_≡_ z) x (to-search-tree xs) (lift tt ≤≤ lift tt) ⟩
  (z ≡ x ⊎ z ∈ to-search-tree xs)
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ to-search-tree-lemma xs z ⟩
  z ∈ x ∷ xs ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Appending two ordered lists with an extra element in between

infixr 5 append

syntax append x lx xu = lx ⁅- x -⁆ xu

append : ∀ {l u} (x : Key) →
         Ordered-list l [ x ] → Ordered-list [ x ] u → Ordered-list l u
nil l≤x       ⁅- x -⁆ xu = cons x xu l≤x
cons y yx l≤y ⁅- x -⁆ xu = cons y (yx ⁅- x -⁆ xu) l≤y

-- Any lemma for append.

Any-append : ∀ (P : Key → Set) {l u} x
             (lx : Ordered-list l [ x ]) (xu : Ordered-list [ x ] u) →
             Any P (lx ⁅- x -⁆ xu) ↔ (Any P lx ⊎ P x ⊎ Any P xu)

Any-append P x (nil l≤x) xu =
  (P x ⊎ Any P xu)
    ↔⟨ sym $ proj₁ ×⊎.+-identity (P x ⊎ Any P xu) ⟩
  (Lift ⊥ ⊎ P x ⊎ Any P xu) ∎
  where open Related.EquationalReasoning

Any-append P {l} x (cons y yx l≤y) xu =
  Any P (cons {l} y yx l≤y ⁅- x -⁆ xu)
    ↔⟨ _ ∎ ⟩
  (P y ⊎ Any P (yx ⁅- x -⁆ xu))
    ↔⟨ _ ∎ ⟨ ×⊎.+-cong ⟩ Any-append P x yx xu ⟩
  (P y ⊎ (Any P yx ⊎ P x ⊎ Any P xu))
    ↔⟨ sym $ ×⊎.+-assoc (P y) (Any P yx) (P x ⊎ Any P xu) ⟩
  ((P y ⊎ Any P yx) ⊎ P x ⊎ Any P xu)
    ↔⟨ _ ∎ ⟩
  (Any P (cons {l} y yx l≤y) ⊎ P x ⊎ Any P xu) ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Inorder flattening of a tree

flatten : ∀ {l u} → Search-tree l u → Ordered-list l u

flatten (leaf l≤u)    = nil l≤u
flatten (l [- x -] r) = flatten l ⁅- x -⁆ flatten r

-- Flatten does not add or remove any elements.

flatten-lemma : ∀ {l u} (t : Search-tree l u) → flatten t ≈-bag t

flatten-lemma {l} {u} (leaf l≤u) z =
  z ∈ flatten (leaf {l} {u} l≤u)
    ↔⟨ _ ∎ ⟩
  Lift ⊥
    ↔⟨ _ ∎ ⟩
  z ∈ leaf {l} {u} l≤u ∎
  where open Related.EquationalReasoning
flatten-lemma (l [- x -] r) z =
  z ∈ flatten (node x l r)
    ↔⟨ _ ∎ ⟩
  z ∈ flatten l ⁅- x -⁆ flatten r
    ↔⟨ Any-append (_≡_ z) x (flatten l) (flatten r) ⟩
  (z ∈ flatten l ⊎ z ≡ x ⊎ z ∈ flatten r)
    ↔⟨ flatten-lemma l z ⟨ ×⊎.+-cong ⟩
                     (_ ∎ ⟨ ×⊎.+-cong ⟩ flatten-lemma r z) ⟩
  (z ∈ l ⊎ z ≡ x ⊎ z ∈ r)
    ↔⟨ _ ∎ ⟩
  z ∈ l [- x -] r ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Sorting

-- Sorts a list.

tree-sort : List Key → Ordered-list ⊥⁺ ⊤⁺
tree-sort = flatten ∘ to-search-tree

-- The result is a permutation of the input.

tree-sort-permutes : ∀ xs → tree-sort xs ≈-bag xs

tree-sort-permutes xs z =
  z ∈ tree-sort xs
    ↔⟨ _ ∎ ⟩
  z ∈ flatten (to-search-tree xs)
    ↔⟨ flatten-lemma (to-search-tree xs) z ⟩
  z ∈ to-search-tree xs
    ↔⟨ to-search-tree-lemma xs z ⟩
  z ∈ xs ∎
  where open Related.EquationalReasoning

--
