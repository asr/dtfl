------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Some non-dependent types used in functional languages
------------------------------------------------------------------------------

-- References:
-- 1. Benjamin C. Pierce. Types and programming languages. The MIT
--    Press, 2002.
-- 2. Wikipedia article on algebraic data types.

-- To process an Agda file use C-c C-l.

-- To find out how to write a given character, position the cursor over
-- the character and press C-u C-x =.

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --guardedness              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --safe                     #-}
{-# OPTIONS --warning=all              #-}
{-# OPTIONS --warning=error            #-}
{-# OPTIONS --without-K                #-}

module Lecture.NonDependentTypes where

------------------------------------------------------------------------------

infixr 6 _,_
infixr 5 _×_
infixr 4 _+_

-- Datatypes are introduced by a 'data' declaration, giving the name and
-- type of the datatype as well as the data constructors and their types.

-- What is in most programming languages called 'Type' is in Agda for
-- historic reasons called 'Set'.

-- The empty (bottom) type: It is the type that has no inhabitants.
data ⊥ : Set where -- to type ⊥ we type \bot

-- The unit (top) type: It is the type that allows only one value.
data ⊤ : Set where  -- to type ⊤ we type \top
  tt : ⊤

-- (Parameterized) polymorphic type: It is a type that takes another
-- type as its parameter.

-- Product type: The product of two types is the type inhabited by
-- pairs of terms whose first component is term of the first type and
-- whose second component is an term of the second type.
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

-- Tuple type: n-ary product type.

-- Record type: A tuple type where each type has an label by which it
-- can be accessed.
-- See:
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.Records

record R (A B C : Set) : Set where
  field
    f₁ : A
    f₂ : B
    f₃ : C

-- Sum type (disjoint union): A tagged union of types.
data _+_ (A B : Set) : Set where
  inj₁ : A → A + B
  inj₂ : B → A + B

-- Enumerated type: Generalized binary sums where the only type used
-- is the unit type.

data WeekDay : Set where
  monday    : WeekDay
  tuesday   : WeekDay
  wednesday : WeekDay
  thursday  : WeekDay
  friday    : WeekDay

-- Function types: If 'A B : Set' then 'A → B' is the type of
-- functions of A to B.

-- Algebraic data types: Sum of product types.

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

-- Recursive type: It is a type that is defined in terms of itself.

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Tree (A : Set) : Set where
  empty : Tree A
  leaf  : A → Tree A
  node  : Tree A → Tree A → Tree A
