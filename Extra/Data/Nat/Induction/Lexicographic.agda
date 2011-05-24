------------------------------------------------------------------------------
-- Lexicographic induction on the natural numbers
------------------------------------------------------------------------------

module Extra.Data.Nat.Induction.Lexicographic where

open import Data.Nat
open import Data.Product

------------------------------------------------------------------------------

data _⟪′_ : ℕ × ℕ → ℕ × ℕ → Set where
  ⟪′₁ : ∀ {x x'} y y' → x <′ x' → (x , y ) ⟪′ (x' , y')
  ⟪′₂ : ∀ x {y y'}    → y <′ y' → (x , y ) ⟪′ (x , y')

wf-⟪′ : (P : ℕ × ℕ → Set) →
        (∀ xy → (∀ x'y' → x'y' ⟪′ xy → P x'y') → P xy) →
        ∀ xy → P xy
wf-⟪′ P ih xs = ih xs (helper xs)
  where
    helper : ∀ xy x'y' → x'y' ⟪′ xy → P x'y'
    helper .(suc x , y) .(x , y') (⟪′₁ {x} y' y ≤′-refl) =
      ih (x , y') (helper (x , y'))
    helper .(suc x , y) .(x' , y') (⟪′₁ {x'} y' y (≤′-step {x} sx'≤′x)) =
      helper (x , x) (x' , y') (⟪′₁ y' x sx'≤′x)
    helper .(x' , suc y') .(x' , y') (⟪′₂ x' {y'} ≤′-refl) =
      ih (x' , y') (helper (x' , y'))
    helper .(x , suc y) .(x , y') (⟪′₂ x {y'} (≤′-step {y} sy'≤′y)) =
      helper (x , y) (x , y') (⟪′₂ x sy'≤′y)
