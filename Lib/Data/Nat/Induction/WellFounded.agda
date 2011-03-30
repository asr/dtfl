------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

module Lib.Data.Nat.Induction.WellFounded where

open import Lib.Data.Nat
open import Lib.Data.Nat.Properties

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers

-- Let P be an predicate

--            ∀ x. (∀ y. y < x  → P y) → P x
-----------------------------------------------
--              ∀ x. P x

-- From http://code.haskell.org/~dolio/agda-share/induction/.
wfIndℕ : (P : ℕ → Set) →
         (∀ n → (∀ m → m < n → P m) → P n) →
         ∀ n → P n
wfIndℕ P ih n = ih n (helper n)
  where
    helper : ∀ n m → m < n → P m
    helper zero     m        ()
    helper (succ n) zero     _          = ih zero (λ _ ())
    helper (succ n) (succ m) (s≤s Sm≤n) =
      ih (succ m) (λ m' Sm'≤Sm → helper n m' (≤-trans Sm'≤Sm Sm≤n))
