------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Example: Weak/strong specification of sorting a list (using insert sort)
------------------------------------------------------------------------------

module Lecture.ReasoningAboutPrograms.InsertSort where

open import Data.Empty
open import Data.Nat renaming (suc to succ)
open import Data.Product
open import Data.List

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Relation.Binary.PreorderReasoning as Pre

infix 4 _≙_

------------------------------------------------------------------------------
-- Weak specification

-- Insert an element in an already sorted list.
insert : ℕ → List ℕ → List ℕ
insert n []       = n ∷ []
insert n (x ∷ xs) with n ≤? x
... | yes _ = n ∷ x ∷ xs
... | no  _ = x ∷ insert n xs

insertEg₁ : List ℕ
insertEg₁ = insert 4 (2 ∷ 5 ∷ [])

insertEg₂ : List ℕ
insertEg₂ = insert 4 (24 ∷ 50 ∷ [])

-- The insert sort.
sortW : List ℕ → List ℕ
sortW []       = []
sortW (x ∷ xs) = insert x (sortW xs)

-- Strong specification

-- Adapted from: Yves Bertot and Pierre Castéran. Interactive Theorem
-- Proving and Program Development. Coq'Art: The Calculus of Inductive
-- Constructions. Springer, 2004.

-- Auxiliary properties

¬x≤y→y≤x : ∀ {m n}  → ¬ (m ≤ n) → n ≤ m
¬x≤y→y≤x {m}      {zero}     _     = z≤n
¬x≤y→y≤x {zero}   {succ n} ¬m≤Sn = ⊥-elim (¬m≤Sn z≤n)
¬x≤y→y≤x {succ m} {succ n} ¬m≤Sn = s≤s (¬x≤y→y≤x (λ m≤n → ¬m≤Sn (s≤s m≤n)))

-- To be a sorted list.
data Sorted : List ℕ → Set where
  sorted-[] :                                        Sorted []
  sorted-x  : ∀ n →                                  Sorted (n ∷ [])
  sorted-∷  : ∀ {m n xs} → m ≤ n → Sorted (n ∷ xs) → Sorted (m ∷ n ∷ xs)

2357-sorted : Sorted (2 ∷ 3 ∷ 5 ∷ 7 ∷ []) -- Via Agsy.
2357-sorted = sorted-∷ (s≤s (s≤s z≤n))
                (sorted-∷ (s≤s (s≤s (s≤s z≤n)))
                 (sorted-∷ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
                  (sorted-x (succ (succ (succ (succ (succ (succ (succ zero))))))))))

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

occEg₁ : ℕ
occEg₁ = occ 3 (3 ∷ 7 ∷ 3 ∷ [])

occEg₂ : ℕ
occEg₂ = occ 36725 (3 ∷ 7 ∷ 3 ∷ [])

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

≙-isEquivalance : IsEquivalence _≙_
≙-isEquivalance = record
  { refl  = λ {xs}           → ≙-refl xs
  ; sym   = λ {xs} {ys}      → ≙-sym xs ys
  ; trans = λ {xs} {ys} {zs} → ≙-trans xs ys zs
  }

-- The relation "to have the same elements" is a preorder.

≙-isPreorder : IsPreorder _≙_ _≙_
≙-isPreorder = record
  { isEquivalence = ≙-isEquivalance
  ; reflexive     = id
  ; trans         = λ {xs} {ys} {zs} → ≙-trans xs ys zs
  }

≙-Preorder : Preorder _ _ _
≙-Preorder = record
  { Carrier    = List ℕ
  ;  _≈_       = _≙_
  ;  _∼_       = _≙_
  ; isPreorder = ≙-isPreorder
  }

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

≙-perm : ∀ n₁ n₂ {xs} {ys} → xs ≙ ys → n₁ ∷ n₂ ∷ xs ≙ n₂ ∷ n₁ ∷ ys
≙-perm n₁  n₂ h n   with n ≟ n₁ | n ≟ n₂
≙-perm .n₂ n₂ h .n₂ | yes refl | yes refl = cong succ (≙-∷ n₂ h n₂)
≙-perm n₁  n₂ h .n₁ | yes refl | no  ¬p   with n₁ ≟ n₂
≙-perm n₂  _  h .n₂ | yes refl | no  ¬p   | yes p = ⊥-elim (¬p p)
≙-perm n₂  _  h .n₂ | yes refl | no  ¬p'  | no  ¬p  with n₂ ≟ n₂
≙-perm n₂  _  h .n₂ | yes refl | no  ¬p'  | no  ¬p  | yes refl = cong succ (h n₂)
≙-perm n₂  _  h .n₂ | yes refl | no  ¬p0  | no  ¬p' | no  ¬p   = ⊥-elim (¬p refl)
≙-perm n₁  n₂ h .n₂ | no  ¬p   | yes refl with n₂ ≟ n₂
≙-perm n₂  n₃ h ._  | no  ¬p   | yes refl | yes refl with n₃ ≟ n₂
≙-perm n₃  _  h ._  | no  ¬p   | yes refl | yes refl | yes p  = ⊥-elim (¬p p)
≙-perm n₃  n₄ h ._  | no  ¬p'  | yes refl | yes refl | no  ¬p = cong succ (h n₄)
≙-perm n₂  _  h ._  | no  ¬p'  | yes refl | no  ¬p = ⊥-elim (¬p refl)
≙-perm n₁  n₂ h n   | no  ¬p   | no  ¬p'  with n ≟ n₂
≙-perm n₁  n₂ h .n₂ | no  ¬p   | no  ¬p'  | yes refl = ⊥-elim (¬p' refl)
≙-perm n₁  n₂ h n   | no  ¬p'  | no  ¬p0  | no  ¬p  with n ≟ n₁
≙-perm n₁  n₂ h .n₁ | no  ¬p'  | no  ¬p0  | no  ¬p  | yes refl = ⊥-elim (¬p' refl)
≙-perm n₁  n₂ h n   | no  ¬p0  | no  ¬p1  | no  ¬p' | no  ¬p   = h n

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

insert-≙ : ∀ xs n → insert n xs ≙ n ∷ xs
insert-≙ []       n = λ _ → refl
insert-≙ (x ∷ xs) n with n ≤? x
... | yes p = λ _ → refl
... | no ¬p = prf
  where
    prf : x ∷ insert n xs ≙ n ∷ x ∷ xs
    prf =
      begin
        x ∷ insert n xs
          ≈⟨ ≙-∷ x (insert-≙ xs n) ⟩
        x ∷ n ∷ xs
          ≈⟨ ≙-perm x n (≙-refl xs) ⟩
        n ∷ x ∷ xs
      ∎
      where open Pre ≙-Preorder

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
