------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Reasoning about of programs
------------------------------------------------------------------------------

module Lecture.ReasoningAboutPrograms where

open import Lib.Data.Nat
open import Lib.Data.List
open import Lib.Data.Vec

------------------------------------------------------------------------------
-- Example: The append function

-- Weak specification.
appendL : {A : Set} → List A → List A → List A
appendL = _++_

-- Strong specification.
appendV : {A : Set}(m n : ℕ) → Vec A m → Vec A n → Vec A (m + n)
appendV .zero     n []             ys = ys
appendV .(succ m) n (_∷_ {m} x xs) ys = x ∷ appendV m n xs ys

------------------------------------------------------------------------------
-- Example: Sorting a list (using insert sort)
-- See Lecture.ReasoningAboutPrograms.Sort
