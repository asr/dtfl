------------------------------------------------------------------------------
-- Induction on lists
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
{-# OPTIONS --safe      #-}
{-# OPTIONS --without-K #-}

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
