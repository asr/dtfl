------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Reasoning about of programs
------------------------------------------------------------------------------

module Lecture.ReasoningAboutPrograms where

open import Data.Bool
open import Data.Nat as Nat renaming (suc to succ)
open import Data.Product
open import Data.List as List
open import Data.Vec

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

infix 4 _≙_

------------------------------------------------------------------------------
-- Example: The append function

-- Weak specification.
appendL : {A : Set} → List A → List A → List A
appendL = List._++_

-- Strong specification.
appendV : {A : Set}(m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
appendV .0        n []             ys = ys
appendV .(succ m) n (_∷_ {m} x xs) ys = x ∷ appendV m n xs ys

------------------------------------------------------------------------------
-- Example: Sorting a list (using insert sort)

-- Weak specification

-- Insert an element in an already sorted list.
insert : ℕ → List ℕ → List ℕ
insert n []       = n ∷ []
insert n (x ∷ xs) with n ≤? x
... | yes _ = n ∷ x ∷ xs
... | no  _ = x ∷ insert n xs

-- The insert sort.
sortW : List ℕ → List ℕ
sortW []       = []
sortW (x ∷ xs) = insert x (sortW xs)

-- Strong specification

-- Adapted from: Yves Bertot and Pierre Castéran. Interactive Theorem
-- Proving and Program Development. Coq'Art: The Calculus of Inductive
-- Constructions. Springer, 2004.

-- To be a sorted list.
data Sorted : List ℕ → Set where
  sorted-[] :                                        Sorted []
  sorted-x  : ∀ n →                                  Sorted (n ∷ [])
  sorted-∷  : ∀ {m n xs} → m ≤ n → Sorted (n ∷ xs) → Sorted (m ∷ n ∷ xs)

-- Number of times that occurs a number in a list.
occ : ℕ → List ℕ → ℕ
occ n []       = 0
occ n (x ∷ xs) with Nat._≟_ n x
... | yes _ = 1 + occ n xs
... | no _  = occ n xs

-- The relation "to have the same elements".
_≙_ : List ℕ → List ℕ → Set
xs ≙ ys = (n : ℕ) → occ n xs ≡ occ n ys

-- The relation "to have the same elements" is a relation of equivalence.

≙-refl : ∀ xs → xs ≙ xs
≙-refl xs n = refl

≙-sym : ∀ xs ys → xs ≙ ys → ys ≙ xs
≙-sym xs ys xs≙ys n = sym (xs≙ys n)

≙-trans : ∀ xs ys zs → xs ≙ ys → ys ≙ zs → xs ≙ zs
≙-trans xs ys zs xs≙ys ys≙zs n = trans (xs≙ys n) (ys≙zs n)

-- Some properties of the relation "to have the same elements"

postulate
  ≙-∷ : ∀ n {xs ys} → xs ≙ ys → n ∷ xs ≙ n ∷ ys

-- Some properties of insert.

postulate
  insertSorted : ∀ {xs} n → Sorted xs → Sorted (insert n xs)
  insert-≙     : ∀ xs n → insert n xs ≙ n ∷ xs

-- The insert sort.
sortS : (xs : List ℕ) → Σ (List ℕ) (λ ys → Sorted ys × xs ≙ ys)
sortS []       = [] , sorted-[] , (λ _ → refl)
sortS (x ∷ xs) = l , l-Sorted , x∷xs≡l
  where
    -- From the IH.
    xs' : List ℕ
    xs' = proj₁ $ sortS xs

    xs'-Sorted : Sorted xs'
    xs'-Sorted = proj₁ $ proj₂ $ sortS xs

    xs≙xs' : xs ≙ xs'
    xs≙xs' = proj₂ $ proj₂ $ sortS xs

    -- The output list.
    l : List ℕ
    l = insert x xs'

    -- The output list is sorted.
    l-Sorted : Sorted l
    l-Sorted = insertSorted x xs'-Sorted

    -- The output list "have the same elements" than the original list
    x∷xs≙x∷xs' : x ∷ xs ≙ x ∷ xs'
    x∷xs≙x∷xs' = ≙-∷ x xs≙xs'

    x∷xs'≙l : x ∷ xs' ≙ l
    x∷xs'≙l = ≙-sym l (x ∷ xs') (insert-≙ xs' x)

    x∷xs≡l : x ∷ xs ≙ l
    x∷xs≡l = ≙-trans (x ∷ xs) (x ∷ xs') l x∷xs≙x∷xs' x∷xs'≙l

-- Testing
-- For example, using C-c C-n normalize sortW l₃ and sortS l₃
-- and see the difference.
l₁ : List ℕ
l₁ = []

l₂ : List ℕ
l₂ = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

l₃ : List ℕ
l₃ = 5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []

l₄ : List ℕ
l₄ = 4 ∷ 1 ∷ 3 ∷ 5 ∷ 2 ∷ []
