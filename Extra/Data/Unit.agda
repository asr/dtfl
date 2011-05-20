------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

module Extra.Data.Unit where

-- The unit type.
-- N.B. The name of this type is "\top", not T.
record ⊤ : Set where
  constructor tt
