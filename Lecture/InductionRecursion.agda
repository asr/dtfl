------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Induction and recursion
------------------------------------------------------------------------------

-- Common options
{-# OPTIONS --double-check   #-}
{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}

-- Other options
-- {-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --safe      #-}
{-# OPTIONS --without-K #-}

module Lecture.InductionRecursion where

open import Data.Nat renaming (suc to succ)
open import Data.List

open import Extra.Data.List.Induction

open import Extra.Data.Nat.Properties
open import Extra.Data.Nat.Induction.MathematicalInduction
open import Extra.Data.Nat.Induction.WellFounded

open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Mathematical induction

-- See Extra.Data.Nat.Induction.MathematicalInduction.indℕ

-- Example: x + 0 = x
-- How to represent 'x + 0 = x'?
-- A. Using an equality on natural numbers (e.g. ℕ → ℕ → Set)
-- B. Using the identity type (see Extra.Relation.Binary.PropositionalEquality).

-- Example: x + 0 = x using mathematical induction.
+-rightIdentity₁ : ∀ n → n + zero ≡ n
+-rightIdentity₁ n = ℕ-ind P P0 is n
  where
  P : ℕ → Set
  P i = i + zero ≡ i

  P0 : P zero
  P0 = refl

  is : ∀ i → P i → P (succ i)
  is i Pi = cong succ Pi

-- Example: x + 0 = x using pattern matching.
-- See Extra.Data.Nat.Properties.+-rightIdentity

-- Theoretical remark: Is there some difference?

-- Example: associativy of addition using mathematical induction.
-- Key: Properly choosing the parameter on which to make the induction.
+-assoc₁ : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc₁ m n o = ℕ-ind P P0 is m
  where
  P : ℕ → Set
  P i = i + n + o ≡ i + (n + o)

  P0 : P zero
  P0 = refl

  is : ∀ i → P i → P (succ i)
  is i Pi = cong succ Pi

-- Example: associativy of addition using pattern matching.
-- See Extra.Data.Nat.Properties.+-assoc.

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers

-- See Extra.Data.Nat.Induction.WellFounded.wfIndℕ

-- Example: x + 0 = x using mathematical induction.
+-rightIdentity₂ : ∀ n → n + zero ≡ n
+-rightIdentity₂ n = <-wfind P ih n
  where
  P : ℕ → Set
  P x = x + zero ≡ x

  ih : ∀ y → (∀ x → x < y → P x) → P y
  ih zero     _ = refl
  ih (succ y) h = cong succ (h y (s≤s (≤-refl y)))

------------------------------------------------------------------------------
-- Induction on lists

-- See Data.List

-- See Extra.Data.List.Induction.indList

-- Example: ++-assoc using induction.
++-assoc₁ : {A : Set}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc₁ {A} xs ys zs = List-ind P P[] ih xs
  where
  P : List A → Set
  P is = (is ++ ys) ++ zs ≡ is ++ (ys ++ zs)

  P[] : P []
  P[] = refl

  ih : ∀ i → (is : List A) → P is → P (i ∷ is)
  ih i is Pis = cong₂ _∷_ refl Pis

-- Example: ++-assoc using pattern matching.
-- See Extra.Data.List.Properties.++-assoc.

-- Example: length-++
-- See Extra.Data.List.Properties.length-++
