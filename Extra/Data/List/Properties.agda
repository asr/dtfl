------------------------------------------------------------------------------
-- Lists properties
------------------------------------------------------------------------------

module Extra.Data.List.Properties where

open import Data.Nat

open import Data.List

open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

++-assoc : {A : Set}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong₂ _∷_ refl (++-assoc xs ys zs)

length-++ : {A : Set}(xs ys : List A) →
            length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys       = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)
