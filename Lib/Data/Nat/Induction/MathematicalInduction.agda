------------------------------------------------------------------------------
-- Mathematical induction
------------------------------------------------------------------------------

module Lib.Data.Nat.Induction.MathematicalInduction where

open import Lib.Data.Nat

------------------------------------------------------------------------------
-- Induction principle on natural numbers (mathematical induction)

-- Let P be an predicate, then

--   P 0             ∀ x. P x → P (succ x)
-----------------------------------------------
--           ∀ x. P x

-- Agda formalization:
-- * Higher-order function
-- * Dependent types
-- * We have a proof of mathematical induction!

indℕ : (P : ℕ → Set) →
       P 0 →
       (∀ n → P n → P (succ n)) →
       ∀ n → P n
indℕ P P0 istep zero     = P0
indℕ P P0 istep (succ n) = istep n (indℕ P P0 istep n)
