------------------------------------------------------------------------------
-- Induction on lists
------------------------------------------------------------------------------

module Lib.Data.List.Induction where

open import Lib.Data.List

------------------------------------------------------------------------------
-- Induction principle on lists.
indList : {A : Set}(P : List A → Set) →
          P [] →
          (∀ x → (xs : List A) → P xs → P (x ∷ xs)) →
          (xs : List A) → P xs
indList P P[] is []       = P[]
indList P P[] is (x ∷ xs) = is x xs (indList P P[] is xs)
