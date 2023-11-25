------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Reasoning about of programs
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

module Lecture.ReasoningAboutPrograms where

open import Data.List
open import Data.Nat renaming (suc to succ)
open import Data.Vec

------------------------------------------------------------------------------
-- Example: The append function

-- Weak specification.
appendL : {A : Set} → List A → List A → List A
appendL = Data.List._++_

-- Strong specification.
appendV : {A : Set}(m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
appendV .zero     n []             ys = ys
appendV .(succ m) n (_∷_ {m} x xs) ys = x ∷ appendV m n xs ys

------------------------------------------------------------------------------
-- Example: Sorting a list (using insert sort)
-- See Lecture.ReasoningAboutPrograms.InsertSort
