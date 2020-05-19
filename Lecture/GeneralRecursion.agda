------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- General recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}

-- We cannot use the `safe` option because we are using the
-- `TERMINATING` flag.
-- {-# OPTIONS --safe #-}

{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Lecture.GeneralRecursion where

open import Data.List
open import Data.Nat renaming (suc to succ) hiding (_≤′?_ )
open import Data.Nat.Properties hiding (_≤′?_ ; ≤′-trans )
open import Data.Product

open import Extra.Data.Nat.Properties
open import Extra.Data.Nat.Induction.Lexicographic
open import Extra.Data.Nat.Induction.WellFounded

open import Relation.Nullary

------------------------------------------------------------------------------
-- A structural recursive function.
fac : ℕ → ℕ
fac zero     = 1
fac (succ n) = succ n * fac n

------------------------------------------------------------------------------
-- A generalization of structural recursion: The termination checker

swap' : ℕ → ℕ → ℕ
swap' 0       _       = 0
{-# CATCHALL #-}
swap' _        0        = 0
swap' (succ m) (succ n) = swap' n m

ack : ℕ → ℕ → ℕ
ack zero     n        = succ n
ack (succ m) zero     = ack m (succ zero)
ack (succ m) (succ n) = ack m (ack (succ m) n)

------------------------------------------------------------------------------
-- The with issue

-- (See http://code.google.com/p/agda/issues/detail?id=59)

-- The non-terminating original function.
-- The function is structurally recursive, but the function is not
-- accepted by the termination checker due to the use of the with.
{-# TERMINATING #-}
merge : List ℕ → List ℕ → List ℕ
merge []       l₂ = l₂
{-# CATCHALL #-}
merge l₁       [] = l₁
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes _ = x ∷ merge xs       (y ∷ ys)
... | no  _ = y ∷ merge (x ∷ xs) ys

-- The merge-trick: Nested withs with the recursive calls.
merge' :  List ℕ → List ℕ → List ℕ
merge' []       l₂ = l₂
{-# CATCHALL #-}
merge' l₁       [] = l₁
merge' (x ∷ xs) (y ∷ ys) with x ≤? y | merge' xs (y ∷ ys) | merge' (x ∷ xs) ys
... | yes p  | aux | _   = x ∷ aux
... | no  ¬p | _   | aux = y ∷ aux

------------------------------------------------------------------------------
-- A non-structural recursive function: simple general recursion

{-# TERMINATING #-}
gcd : ℕ → ℕ → ℕ
gcd 0        0        = 0
gcd (succ m) 0        = succ m
gcd 0        (succ n) = succ n
gcd (succ m) (succ n) with (succ m ≤? succ n)
-- The argument `sucn n ∸ succ m` is not structurally smaller than the
-- argument `succ n`.
... | yes p = gcd (succ m) (succ n ∸ succ m)
-- The argument `succ m ∸ succ n` is not structurally smaller than the
-- argument `succ n`.
... | no ¬p = gcd (succ m ∸ succ n) (succ n)

-- Can we apply the merge-trick?

-- The Bove-Capretta method: The domain predicate

-- (See: Bove, Ana and Capretta, Venanzio (2005a). Modelling General
-- Recursion in Type Theory)

-- Domain predicate for the gcd: GCDDom

--                                 m : ℕ                    n : ℕ
-------------------      ------------------------   ------------------------
--  GCDDom 0 0               GCDDom (suc m) 0           GCDDom 0 (suc n)


--    m n : ℕ      suc m ≤ suc n      GCDDom (suc m) (suc n ∸ suc m)
------------------------------------------------------------------------
--                         GCDDom (suc m) (suc n)


--    m n : ℕ      suc m > suc n      GCDDom (suc m ∸ suc n) (suc n)
------------------------------------------------------------------------
--                         GCDDom (suc m) (suc n)


data GCDDom : ℕ → ℕ → Set where
  gcdDom₁ : GCDDom 0 0
  gcdDom₂ : ∀ {m} → GCDDom (succ m) 0
  gcdDom₃ : ∀ {n} → GCDDom 0 (succ n)
  gcdDom₄ : ∀ {m n} →
            succ m ≤′ succ n →
            GCDDom (succ m) (succ n ∸ succ m) →
            GCDDom (succ m) (succ n)
  gcdDom₅ : ∀ {m n} →
            succ m >′ succ n →
            GCDDom (succ m ∸ succ n) (succ n) →
            GCDDom (succ m) (succ n)

-- The gcd function by structural recursion on the domain predicate.
gcdD : ∀ m n → GCDDom m n → ℕ
gcdD .0        .0        gcdDom₁               = 0
gcdD .(succ m) .0        (gcdDom₂ {m})         = succ m
gcdD .0        .(succ n) (gcdDom₃ {n})         = succ n
gcdD .(succ m) .(succ n) (gcdDom₄ {m} {n} _ h) = gcdD (succ m) (succ n ∸ succ m) h
gcdD .(succ m) .(succ n) (gcdDom₅ {m} {n} _ h) = gcdD (succ m ∸ succ n) (succ n) h

-- The gcd function is total.
allGCDDom : ∀ m n → GCDDom m n
allGCDDom m n = <′₂-ind P ih m n
  where
  P : ℕ → ℕ → Set
  P m n = GCDDom m n

  helper : ∀ a b → succ (a ∸ b) ≤′ succ a
  helper a b = ≤⇒≤′ (s≤s (m∸n≤m a b))

  ih : ∀ x y → (∀ x' y' → (x' , y') <′₂ (x , y) → P x' y') → P x y
  ih zero     zero     h = gcdDom₁
  ih zero     (succ y) h = gcdDom₃
  ih (succ x) zero     h = gcdDom₂
  ih (succ x) (succ y) h with succ x ≤′? succ y
  ... | yes p = gcdDom₄ p (h (succ x) (succ y ∸ succ x) (<′₂-y (helper y x)))
  ... | no ¬p = gcdDom₅ (x≰′y→x>′y ¬p) (h (succ x ∸ succ y) (succ y)
                                         (<′₂-x (helper x y)))

-- The final version of the gcd.
gcd' : ℕ → ℕ → ℕ
gcd' m n = gcdD m n (allGCDDom m n)

------------------------------------------------------------------------------
-- A non-structural recursive function: nested recursion

-- The function is not accepted by the termination checker due to the
-- nested recursive call.
{-# TERMINATING #-}
nest : ℕ → ℕ
nest 0        = 0
nest (succ n) = nest (nest n)

-- The Bove-Capretta method: The domain predicate

-- (See: Bove, Ana and Capretta, Venanzio (2001). Nested General
-- Recursion and Partiality in Type Theory)

-- Domain predicate for the nest: NestDom

-----------------
--  NestDom 0


--    n : ℕ      NestDom n      NestDom (nest n)
-------------------------------------------------------
--                  NestDom (succ n)

-- Problem: We want to use the domain predicate to define the function
-- nest, but it requires the function.

-- Solution: Mutual block for the definition of the domain predicate
-- and the function.

mutual
  -- The domain predicate of the nest function.
  data NestDom : ℕ → Set where
    nestDom0 : NestDom 0
    nestDomS : ∀ {n} →
               (h₁ : NestDom n) →
               (h₂ : NestDom (nestD n h₁)) →
               NestDom (succ n)

  -- The nest function by structural recursion on the domain predicate.
  nestD : ∀ n → NestDom n → ℕ
  nestD .0        nestDom0             = 0
  nestD .(succ n) (nestDomS {n} h₁ h₂) = nestD (nestD n h₁) h₂

nestD-≤′ : ∀ n → (h : NestDom n) → nestD n h ≤′ n
nestD-≤′ .0        nestDom0             = ≤′-refl
nestD-≤′ .(succ n) (nestDomS {n} h₁ h₂) =
  ≤′-trans (≤′-trans (nestD-≤′ (nestD n h₁) h₂) (nestD-≤′ n h₁))
           (≤′-step ≤′-refl)

-- The nest function is total.
allNestDom : ∀ n → NestDom n
allNestDom = <′-wfind P ih
  where
  P : ℕ → Set
  P = NestDom

  ih : ∀ y → (∀ x → x <′ y → P x) → P y
  ih zero     rec = nestDom0
  ih (succ y) rec = nestDomS nd-y (rec (nestD y nd-y) (s≤′s (nestD-≤′ y nd-y)))
    where
    helper : ∀ x → x <′ y → P x
    helper x Sx≤′y = rec x (≤′-step Sx≤′y)

    nd-y : NestDom y
    nd-y = ih y helper

-- The final version of the nest function.
nest' : ℕ → ℕ
nest' n = nestD n (allNestDom n)
