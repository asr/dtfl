------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Induction and recursion
------------------------------------------------------------------------------

module Lecture.InductionRecursion where

open import Lib.Data.List
open import Lib.Data.List.Induction

open import Lib.Data.Nat
open import Lib.Data.Nat.Properties
open import Lib.Data.Nat.Induction.MathematicalInduction
open import Lib.Data.Nat.Induction.WellFounded

open import Lib.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Mathematical induction

-- See Lib.Data.Nat.Induction.MathematicalInduction.indℕ

-- Example: x + 0 = x
-- How to represent 'x + 0 = x'?
-- A. Using an equality on natural numbers (e.g. ℕ → ℕ → Set)
-- B. Using the identity type (see Lib.Relation.Binary.PropositionalEquality).

-- Example: x + 0 = x using mathematical induction.
+-rightIdentity₁ : ∀ n → n + 0 ≡ n
+-rightIdentity₁ n = indℕ P P0 is n
  where
    P : ℕ → Set
    P i = i + 0 ≡ i

    P0 : P 0
    P0 = refl

    is : ∀ i → P i → P (succ i)
    is i Pi = cong succ Pi

-- Example: x + 0 = x using pattern matching.
-- See Lib.Data.Nat.Properties.+-rightIdentity

-- Theoretical remark: Is there some difference?

-- Example: associativy of addition using mathematical induction.
-- Key: Properly choosing the parameter on which to make the induction.
+-assoc₁ : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc₁ m n o = indℕ P P0 is m
  where
    P : ℕ → Set
    P i = i + n + o ≡ i + (n + o)

    P0 : P 0
    P0 = refl

    is : ∀ i → P i → P (succ i)
    is i Pi = cong succ Pi

-- Example: associativy of addition using pattern matching.
-- See Lib.Data.Nat.Properties.+-assoc.

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers

-- See Lib.Data.Nat.Induction.WellFounded.wfIndℕ

-- Example: x + 0 = x using mathematical induction.
+-rightIdentity₂ : ∀ n → n + 0 ≡ n
+-rightIdentity₂ n = wfIndℕ P ih n
  where
    P : ℕ → Set
    P x = x + 0 ≡ x

    ih : ∀ y → (∀ x → x < y → P x) → P y
    ih zero     _ = refl
    ih (succ y) h = cong succ (h y (s≤s (≤-refl y)))

------------------------------------------------------------------------------
-- Induction on lists

-- See Lib.Data.List

-- See Lib.Data.List.Induction.indList

-- Example: ++-assoc using induction.
++-assoc₁ : {A : Set}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc₁ {A} xs ys zs = indList P P[] ih xs
  where
    P : List A → Set
    P is = (is ++ ys) ++ zs ≡ is ++ (ys ++ zs)

    P[] : P []
    P[] = refl

    ih : ∀ i → (is : List A) → P is → P (i ∷ is)
    ih i is Pis = cong₂ _∷_ refl Pis

-- Example: ++-assoc using pattern matching.
-- See Lib.Data.List.Properties.++-assoc.

-- Example: length-++
-- See Lib.Data.List.Properties.length-++
