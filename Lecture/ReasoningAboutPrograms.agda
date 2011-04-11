------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Reasoning about of programs
------------------------------------------------------------------------------

module Lecture.ReasoningAboutPrograms where

open import Data.Bool hiding ( _≟_ )
open import Data.Empty
open import Data.Nat renaming (suc to succ)
open import Data.Product
open import Data.List as List
open import Data.Vec

open import Function

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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

-- Auxiliary properties

¬x≤y→y≤x : ∀ {m n}  → ¬ (m ≤ n) → n ≤ m
¬x≤y→y≤x {m}      {zero}     _     = z≤n
¬x≤y→y≤x {zero}   {succ n} ¬m≤Sn = ⊥-elim (¬m≤Sn z≤n)
¬x≤y→y≤x {succ m} {succ n} ¬m≤Sn = s≤s (¬x≤y→y≤x (λ m≤n → ¬m≤Sn (s≤s m≤n)))


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

-- Some properties of the relation Sorted.

tailSorted : ∀ {x} {xs} → Sorted (x ∷ xs) → Sorted xs
tailSorted {x} (sorted-x .x) = sorted-[]
tailSorted (sorted-∷ h₁ h₂)  = h₂

-- Number of times that occurs a number in a list.
occ : ℕ → List ℕ → ℕ
occ n []       = 0
occ n (x ∷ xs) with n ≟ x
... | yes _ = 1 + occ n xs
... | no _  = occ n xs

--- The relation "to have the same elements".
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

-- Version using pattern matching in z ≟ n
-- ≙-∷' : ∀ z {xs ys} → xs ≙ ys → z ∷ xs ≙ z ∷ ys
-- ≙-∷' z xs≙ys n with z ≟ n
-- ... | yes p = {!!}
-- ... | no ¬p = {!!}

≙-∷ : ∀ z {xs ys} → xs ≙ ys → z ∷ xs ≙ z ∷ ys
≙-∷ z xs≙ys n with n ≟ z
≙-∷ z xs≙ys n | yes _ = cong succ (xs≙ys n)
≙-∷ z xs≙ys n | no  _ = xs≙ys n

-- Some properties of insert.

insertSortedHelper : ∀ {n} {x} {xs} →
                     x ≤ n →
                     Sorted (x ∷ xs) →
                     Sorted (insert n xs) →
                     Sorted (x ∷ insert n xs)
insertSortedHelper {n} {x} {[]}      h₁ h₂ h₃ = sorted-∷ h₁ (sorted-x n)
insertSortedHelper {n} {x} {x' ∷ xs} h₁ h₂ h₃ with n ≤? x'
... | yes p = sorted-∷ h₁ h₃
insertSortedHelper {n} {x} {x' ∷ xs} h₁ (sorted-∷ x≤x' h₂) h₃ | no ¬p =
  sorted-∷ x≤x' h₃

insertSorted : ∀ {xs} n → Sorted xs → Sorted (insert n xs)
insertSorted {[]} n s = sorted-x n
insertSorted {(x ∷ xs)} n s with n ≤? x
... | yes p = sorted-∷ p s
... | no ¬p = insertSortedHelper (¬x≤y→y≤x ¬p) s (insertSorted n (tailSorted s))

postulate
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

-- Examples
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
