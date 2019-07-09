------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Equational reasoning
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Lecture.EquationalReasoning where

open import Data.Nat renaming (suc to succ)

open import Extra.Data.Nat.Properties
open import Extra.Relation.Binary.PreorderReasoning
open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Equational reasoning

-- From: Graham Hutton. Programming in Haskell. Cambridge University
-- Press, 2007.

-- At school we learn basic algebraic properties of numbers, such as the
-- fact that multiplication is commutative, addition is associative, and
-- multiplication distributes over addition on both the left-hand
-- right-hand sides:

--     xy          =  yx             *-comm
--     x + (y + z) =  (x + y) + z    +-assoc
--     x (y + z)   =  xy + xz        +*-leftDistributivity
--     (x + y) z   =  xz + yz        +*-rightDistributivity

-- For example, using these properties we can show that a product of the form
-- (x + a) (x + b) can be expanded to a summation x^2 + (a + b) x + a b:

--         (x + a) (x + b)
--     =        { +*-leftDistributivity }
--         (x + a) x + (x + a) b
--     =        { +*-rightDistributivity }
--         xx + ax + xb + ab
--     =        { squaring }
--         x^2 + ax + xb + ab
--     =        { *-comm }
--         x^2 + ax + bx + ab
--     =        { +*-rightDistributivity }
--         x^2 + (a + b) x + ab

-- Example: +-comm
+-comm₁ : ∀ m n → m + n ≡ n + m
+-comm₁ zero     n = sym (+-rightIdentity n)
+-comm₁ (succ m) n =
  begin
    succ m + n   ≡⟨ refl ⟩
    succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + succ m
  ∎

-- Agda equational reasoning
-- See Extra.Relation.Binary.PreorderReasoning
