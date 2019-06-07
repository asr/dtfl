------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- General recursion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split          #-}
{-# OPTIONS --guardedness          #-}
{-# OPTIONS --no-sized-types       #-}
{-# OPTIONS --no-termination-check #-}
-- {-# OPTIONS --safe                 #-}
{-# OPTIONS --warning=all          #-}
{-# OPTIONS --warning=error        #-}
{-# OPTIONS --without-K            #-}

module Lecture.GeneralRecursion where

open import Data.List
open import Data.Nat hiding (_≤′?_ )
open import Data.Nat.Properties hiding (_≤′?_ ; ≤′-trans )
open import Data.Product

open import Extra.Data.Nat.Properties
open import Extra.Data.Nat.Induction.Lexicographic
open import Extra.Data.Nat.Induction.WellFounded

open import Relation.Nullary

------------------------------------------------------------------------------
-- A structural recursive function.
fac : ℕ → ℕ
fac zero    = 1
fac (suc n) = suc n * fac n

------------------------------------------------------------------------------
-- A generalization of structural recursion: The termination checker

swap' : ℕ → ℕ → ℕ
swap' 0       _       = 0
{-# CATCHALL #-}
swap' _       0       = 0
swap' (suc m) (suc n) = swap' n m

ack : ℕ → ℕ → ℕ
ack zero     n      = suc n
ack (suc m) zero    = ack m (suc zero)
ack (suc m) (suc n) = ack m (ack (suc m) n)

------------------------------------------------------------------------------
-- The with issue

-- (See http://code.google.com/p/agda/issues/detail?id=59)

-- The non-terminating original function.
-- The function is structurally recursive, but the function is not
-- accepted by the termination checker due to the use of the with.
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

gcd : ℕ → ℕ → ℕ
gcd 0       0       = 0
gcd (suc m) 0       = suc m
gcd 0       (suc n) = suc n
gcd (suc m) (suc n) with (suc m ≤? suc n)
-- The argument suc n ∸ suc m is not structurally smaller than the
-- argument suc n.
... | yes p = gcd (suc m) (suc n ∸ suc m)
-- The argument suc m ∸ suc n is not structurally smaller than the
-- argument suc n.
... | no ¬p = gcd (suc m ∸ suc n) (suc n)

-- Can we apply the merge-trick?

-- The Bove-Capretta method: The domain predicate

-- (See Ana Bove and Venanzio Capretta. Modelling general recursion in
-- type theory. Math. Struct. in Comp. Science, 15:671–708, 2005.)

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
  gcdDom₂ : ∀ {m} → GCDDom (suc m) 0
  gcdDom₃ : ∀ {n} → GCDDom 0 (suc n)
  gcdDom₄ : ∀ {m n} →
            suc m ≤′ suc n →
            GCDDom (suc m) (suc n ∸ suc m) →
            GCDDom (suc m) (suc n)
  gcdDom₅ : ∀ {m n} →
            suc m >′ suc n →
            GCDDom (suc m ∸ suc n) (suc n) →
            GCDDom (suc m) (suc n)

-- The gcd function by structural recursion on the domain predicate.
gcdD : ∀ m n → GCDDom m n → ℕ
gcdD .0       .0        gcdDom₁              = 0
gcdD .(suc m) .0       (gcdDom₂ {m})         = suc m
gcdD .0       .(suc n) (gcdDom₃ {n})         = suc n
gcdD .(suc m) .(suc n) (gcdDom₄ {m} {n} _ h) = gcdD (suc m) (suc n ∸ suc m) h
gcdD .(suc m) .(suc n) (gcdDom₅ {m} {n} _ h) = gcdD (suc m ∸ suc n) (suc n) h

-- The gcd function is total.
allGCDDom : ∀ m n → GCDDom m n
allGCDDom m n = ℕ-lexi P ih m n
  where
  P : ℕ → ℕ → Set
  P m n = GCDDom m n

  helper : ∀ a b → suc (a ∸ b) ≤′ suc a
  helper a b = ≤⇒≤′ (s≤s (n∸m≤n b a))

  ih : ∀ x y → (∀ x' y' → (x' , y') <₂ (x , y) → P x' y') → P x y
  ih zero zero    h = gcdDom₁
  ih zero (suc y) h = gcdDom₃
  ih (suc x) zero h = gcdDom₂

  ih (suc x) (suc y) h with suc x ≤′? suc y
  ... | yes p = gcdDom₄ p (h (suc x) (suc y ∸ suc x) (<₂-y (helper y x)))

  ... | no ¬p = gcdDom₅ (x≰′y→x>′y ¬p) (h (suc x ∸ suc y) (suc y)
                                          (<₂-x (helper x y)))

-- The final version of the gcd.
gcd' : ℕ → ℕ → ℕ
gcd' m n = gcdD m n (allGCDDom m n)

------------------------------------------------------------------------------
-- A non-structural recursive function: nested recursion

-- The function is not accepted by the termination checker due to the
-- nested recursive call.
nest : ℕ → ℕ
nest 0       = 0
nest (suc n) = nest (nest n)

-- The Bove-Capretta method: The domain predicate

-- (See Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.)

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
               NestDom (suc n)

  -- The nest function by structural recursion on the domain predicate.
  nestD : ∀ n → NestDom n → ℕ
  nestD .0       nestDom0             = 0
  nestD .(suc n) (nestDomS {n} h₁ h₂) = nestD (nestD n h₁) h₂

nestD-≤′ : ∀ n → (h : NestDom n) → nestD n h ≤′ n
nestD-≤′ .0       nestDom0             = ≤′-refl
nestD-≤′ .(suc n) (nestDomS {n} h₁ h₂) =
  ≤′-trans (≤′-trans (nestD-≤′ (nestD n h₁) h₂) (nestD-≤′ n h₁))
           (≤′-step ≤′-refl)

-- The nest function is total.
allNestDom : ∀ n → NestDom n
allNestDom = wfIndℕ-<′ P ih
  where
  P : ℕ → Set
  P = NestDom

  ih : ∀ y → (∀ x → x <′ y → P x) → P y
  ih zero    rec = nestDom0
  ih (suc y) rec = nestDomS nd-y (rec (nestD y nd-y) (s≤′s (nestD-≤′ y nd-y)))
    where
    helper : ∀ x → x <′ y → P x
    helper x Sx≤′y = rec x (≤′-step Sx≤′y)

    nd-y : NestDom y
    nd-y = ih y helper

-- The final version of the nest function.
nest' : ℕ → ℕ
nest' n = nestD n (allNestDom n)
