------------------------------------------------------------------------------
-- Natural numbers
------------------------------------------------------------------------------

module Lib.Data.Nat where

infixl 6 _+_
infix  4 _≤_ _<_

------------------------------------------------------------------------------

-- Tha natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ     #-}
{-# BUILTIN ZERO    zero  #-}
{-# BUILTIN SUC     succ  #-}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} →           zero   ≤ n
  s≤s : ∀ {m n} → m ≤ n → succ m ≤ succ n

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

-- Addition by recursion on the 1st argument
_+_ : ℕ → ℕ → ℕ
zero     + n = n
succ m + n = succ (m + n)
