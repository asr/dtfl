------------------------------------------------------------------------------
-- Preorder reasoning
------------------------------------------------------------------------------

-- In Agda we can define combinators which can be used for presenting
-- equational proofs in a natural style. We define the combinators
-- begin_ which begins a proof, _≡⟨_⟩_, which performs one step of a
-- proof, and _∎, which ends a proof. In fact, these combinators work
-- for arbitrary preorders.

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

module Extra.Relation.Binary.PreorderReasoning where

open import Extra.Relation.Binary.PropositionalEquality

infix  4 _≃_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_

------------------------------------------------------------------------------
-- Adapted from the standard library (Relation.Binary.PreorderReasoning).
private
  data _≃_ {A : Set}(x y : A) : Set where
    prf : x ≡ y → x ≃ y

begin_ : {A : Set}{x y : A} → x ≃ y → x ≡ y
begin prf x≡y = x≡y

_≡⟨_⟩_ : {A : Set}(x : A){y z : A} → x ≡ y → y ≃ z → x ≃ z
_ ≡⟨ x≡y ⟩ prf y≡z = prf (trans x≡y y≡z)

_∎ : {A : Set}(x : A) → x ≃ x
_∎ _ = prf refl
