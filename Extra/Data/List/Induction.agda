------------------------------------------------------------------------------
-- Induction on lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Extra.Data.List.Induction where

open import Data.List

------------------------------------------------------------------------------
-- Induction principle on lists.
indList : {A : Set}(P : List A → Set) →
          P [] →
          (∀ x → (xs : List A) → P xs → P (x ∷ xs)) →
          (xs : List A) → P xs
indList P P[] is []       = P[]
indList P P[] is (x ∷ xs) = is x xs (indList P P[] is xs)
