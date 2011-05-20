------------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------------

module Extra.Data.Product where

infixr 4 _,_
infixr 2 _×_

------------------------------------------------------------------------------

-- The Sigma type.
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- The product type.
_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)
