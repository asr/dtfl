------------------------------------------------------------------------------
-- All the DTFL modules
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
-- {-# OPTIONS --safe                     #-}
-- {-# OPTIONS --without-K                #-}

module Everything where

-- Extra stuff
open import Extra.Data.List.Induction
open import Extra.Data.List.Properties
open import Extra.Data.Nat.Induction.MathematicalInduction
open import Extra.Data.Nat.Induction.Lexicographic
open import Extra.Data.Nat.Induction.WellFounded
open import Extra.Data.Nat.Properties
open import Extra.Data.Product
open import Extra.Data.Unit

open import Extra.Relation.Binary.PreorderReasoning
open import Extra.Relation.Binary.PropositionalEquality

-- Lectures
open import README
