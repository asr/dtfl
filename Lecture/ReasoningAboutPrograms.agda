------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Reasoning about of programs
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

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
