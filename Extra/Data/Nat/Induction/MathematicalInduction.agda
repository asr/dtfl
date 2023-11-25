------------------------------------------------------------------------------
-- Mathematical induction
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


module Extra.Data.Nat.Induction.MathematicalInduction where

open import Data.Nat renaming (suc to succ)

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

ℕ-ind : (P : ℕ → Set) →
        P zero →
        (∀ n → P n → P (succ n)) →
        ∀ n → P n
ℕ-ind P P0 istep zero     = P0
ℕ-ind P P0 istep (succ n) = istep n (ℕ-ind P P0 istep n)
