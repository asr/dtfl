------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Inductive families (datatype families, inductively defined family of sets)
------------------------------------------------------------------------------

-- References:

-- [1] Ana Bove and Peter Dybjer. Dependent types at work. In Ana Bove
--     et al., editors. LerNet ALFA Summer School 2008, volume 5520 of
--     LNCS, 2009. pp. 57-99.

-- [2] Ulf Norell. Dependently typed programming in Agda. In Koopman
--     et al., editors. Advanced Functional Programming 6th
--     International School, AFP 2008, volume 5832 of
--     LNCS. Springer-Verlag, 2009. pp. 230-266.

module Lecture.InductiveFamilies where

open import Data.Nat

open import Extra.Data.Unit
open import Extra.Data.Product

------------------------------------------------------------------------------

-- Motivation: Problems in the definition of some Haskell functions
-- (from Data.List (GHC 7.0.3))

-- | Extract the first element of a list, which must be non-empty.
-- head                    :: [a] -> a
-- head (x:_)              =  x
-- head []                 =  badHead

-- | Extract the elements after the head of a list, which must be non-empty.
-- tail                    :: [a] -> [a]
-- tail (_:xs)             =  xs
-- tail []                 =  errorEmptyList "tail"

-- | 'zip' takes two lists and returns a list of corresponding pairs.
-- If one input list is short, excess elements of the longer list are
-- discarded.
-- zip :: [a] -> [b] -> [(a,b)]
-- zip (a:as) (b:bs) = (a,b) : zip as bs
-- zip _      _      = []

------------------------------------------------------------------------------
-- Vectors: Types of lists of a certain length

-- Inductive family definition:

data Vec (A : Set) : ℕ → Set where
  []  :                         Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- The type of vectors.
-- Vec A : ℕ → Set, i.e. Vec A is an inductive family parametrized by
-- A and indexed by the natural numbers.

-- The data constructors:
-- [] : It generates a vector of length 0.

-- _∷_ : It generates a vector of length (n + 1) from a vector of
--       length n and an element of A.

-- Parameters: They remain the same throughout the definition.

-- Indexes: They vary in types of the data constructors.

-- Examples

-- Using the inductive familiy of vectors we can express the type of
-- non-empty lists.

head : {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : {A : Set}{n : ℕ} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

-- Using the inductive familiy of vectors we can express that two list
-- are the same length.
zip : {A B : Set}(n : ℕ) → Vec A n → Vec B n → Vec (A × B) n
zip .zero     []            []       = []
zip .(suc n) (_∷_ {n} x xs) (y ∷ ys) = (x , y) ∷ zip n xs ys

------------------------------------------------------------------------------
-- Alternative definition of vectors: Recursive definition by
-- induction on the length

-- Mathematical definition
-- A⁰      = 1
-- A^(n+1) = A x A^n

VecR : Set → ℕ → Set
VecR A zero    = ⊤
VecR A (suc n) = A × (VecR A n)

-- Examples

-- Using the recursive definition of vectors we can express the type
-- of non-empty lists.
headR : {A : Set}{n : ℕ} → VecR A (suc n) → A
headR (x , xs) = x

-- Using the recursive definition of vectors we can express that two
-- list are the same length.
zipR : {A B : Set}(n : ℕ) → VecR A n → VecR B n → VecR (A × B) n
zipR zero     xs       ys      = _
zipR (suc n) (x , xs) (y , ys) = (x , y) , (zipR n xs ys)

------------------------------------------------------------------------------
-- Inductive families or recursive definitions?

-- "In the remainder of the notes we will, however, mostly use
-- inductive families. This should not be taken as a statement that
-- inductive families are always more convenient than recursive
-- ones. When both methods are applicable, one needs to carefully
-- consider how they will be used before choosing the one or the
-- other". [1, p. 70]
