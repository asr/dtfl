------------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------------

module Lib.Data.List where

open import Lib.Data.Nat

infixr 5 _∷_ _++_

------------------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = (succ zero) + length xs
