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
List-ind : {A : Set}(P : List A → Set) →
           P [] →
           (∀ x → (xs : List A) → P xs → P (x ∷ xs)) →
           (xs : List A) → P xs
List-ind P P[] is []       = P[]
List-ind P P[] is (x ∷ xs) = is x xs (List-ind P P[] is xs)
