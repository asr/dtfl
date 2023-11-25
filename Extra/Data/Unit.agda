------------------------------------------------------------------------
-- The unit type
------------------------------------------------------------------------

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

module Extra.Data.Unit where

-- The unit type.
-- N.B. The name of this type is "\top", not T.
record ⊤ : Set where
  constructor tt
