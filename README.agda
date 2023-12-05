------------------------------------------------------------------------------
-- Agda code for the course dependently typed functional
-- languages - 2011-01

-- Course home page:
-- http://www1.eafit.edu.co/asr/courses/dependently-typed-functional-languages/index.html

------------------------------------------------------------------------------

-- The code has been tested with Agda 2.6.4.1 and the standard
-- library 1.7.3.

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

module README where

-- Lectures
open import Lecture.NonDependentTypes
open import Lecture.PropositionsAsTypes
open import Lecture.InductionRecursion
open import Lecture.EquationalReasoning
open import Lecture.AlgebraicStructures
open import Lecture.LeibnizEquality
open import Lecture.InductiveFamilies
open import Lecture.ReasoningAboutPrograms
open import Lecture.ReasoningAboutPrograms.InsertSort
open import Lecture.GeneralRecursion
