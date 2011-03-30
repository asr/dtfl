------------------------------------------------------------------------------
-- Preorder reasoning
------------------------------------------------------------------------------

-- In Agda we can define combinators which can be used for presenting
-- equational proofs in a natural style. We define the combinators
-- begin_ which begins a proof, _≡⟨_⟩_, which performs one step of a
-- proof, and _∎, which ends a proof. In fact, these combinators work
-- for arbitrary preorders.

module Lib.Relation.Binary.PreorderReasoning where

open import Lib.Relation.Binary.PropositionalEquality

-- We add 3 to the fixities of the standard library.
infix 7 _≃_
infix  4 begin_
infixr 5 _≡⟨_⟩_
infix  5 _∎

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
