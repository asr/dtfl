------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Leibniz's equality
------------------------------------------------------------------------------

-- Common options
{-# OPTIONS --double-check   #-}
{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}

-- Other options
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --safe                     #-}
{-# OPTIONS --without-K                #-}

module Lecture.LeibnizEquality where

open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- Introduction

-- Leibniz's law:
-- 'Two objects of the same type are equal if and only if they cannot
-- be distinguished by any property.' [Zhaohui 1994, §5.1.3]

-- Indiscernible: Incapable of being discerned. Not recognizable as distinct
-- (Merrian Webster).

-- Two parts of Leibniz's law: [Forrest 2010]
-- A. The identity of indiscernibles: ∀P(P x ↔ P y) → x ≐ y.

-- B. The indiscernibility of identicals: x ≐ y → ∀P(P x ↔ P y)

-- Luo, Zhaohui (1994). Computation and Reasoning. A Type Theory for
-- Computer Science. Oxford University Press.

-- Forrest, Peter (2010). The Identity of Indiscernibles.
-- http://plato.stanford.edu/entries/identity-indiscernible/.

------------------------------------------------------------------------------
-- Leibniz's equality [Zhaohui 1994]

-- (From Agda/examples/lib/Logic/Leibniz.agda)

infix 4 _≐_

_≐_  : {A : Set} → A → A → Set1
x ≐ y = (P : _ → Set) → P x → P y

-- Properties
≐-refl : {A : Set}{x : A} → x ≐ x
≐-refl P Px = Px

≐-sym : {A : Set}(x y : A) → x ≐ y → y ≐ x
≐-sym x y x≐y P Py = x≐y (λ z → P z → P x) (λ Px → Px) Py

≐-trans : {A : Set}{x y z : A} → x ≐ y → y ≐ z → x ≐ z
≐-trans x≐y y≐z P Px = y≐z P (x≐y P Px)

≐-subst : {A : Set}(P : A → Set){x y : A} → x ≐ y → P x → P y
≐-subst P x≐y = x≐y P

------------------------------------------------------------------------------
-- Leibniz's equality and the identity type

≐→≡ : {A : Set}{x y : A} → x ≐ y → x ≡ y
≐→≡ {x = x} x≐y = x≐y (λ z → x ≡ z) refl

≡→≐ : {A : Set}{x y : A} → x ≡ y → x ≐ y
≡→≐ refl P Px = Px
