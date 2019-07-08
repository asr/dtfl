------------------------------------------------------------------------------
-- Lists properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Extra.Data.List.Properties where

open import Data.Nat renaming (suc to succ)

open import Data.List

open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

++-assoc : {A : Set}(xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong₂ _∷_ refl (++-assoc xs ys zs)

length-++ : {A : Set}(xs ys : List A) →
            length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys       = refl
length-++ (x ∷ xs) ys = cong succ (length-++ xs ys)
