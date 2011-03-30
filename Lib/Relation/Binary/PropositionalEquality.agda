------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

module Lib.Relation.Binary.PropositionalEquality where

infix 4 _≡_

------------------------------------------------------------------------------
-- The identity type

-- data _≡_ {A : Set} : A → A → Set where
--   refl : ∀ x → x ≡ x

data _≡_ {A : Set}(x : A) : A → Set where
 refl : x ≡ x

-- Identity properties

sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

subst : ∀ {A : Set}{x y} (P : A → Set) → x ≡ y → P x → P y
subst P refl Px = Px

cong : ∀ {A B : Set}{x y} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set}{x₁ x₂ y₁ y₂} (f : A → B → C) → x₁ ≡ y₁ → x₂ ≡ y₂ →
        f x₁ x₂ ≡ f y₁ y₂
cong₂ f refl refl = refl
