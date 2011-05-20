------------------------------------------------------------------------------
-- Mathematical induction
------------------------------------------------------------------------------

module Extra.Data.Nat.Induction.MathematicalInduction where

open import Data.Nat

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
       P zero →
       (∀ n → P n → P (suc n)) →
       ∀ n → P n
indℕ P P0 istep zero    = P0
indℕ P P0 istep (suc n) = istep n (indℕ P P0 istep n)
