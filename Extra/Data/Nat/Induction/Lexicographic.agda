------------------------------------------------------------------------------
-- Lexicographic induction on the natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Extra.Data.Nat.Induction.Lexicographic where

open import Data.Nat renaming (suc to succ)
open import Data.Product

------------------------------------------------------------------------------

infix 4 _<₂_

data _<₂_ : ℕ × ℕ → ℕ × ℕ → Set where
  <₂-x : ∀ {x y x' y'} → x <′ x' → (x , y) <₂ (x' , y')
  <₂-y : ∀ {x y y'} → y <′ y' → (x , y) <₂ (x , y')

ℕ-lexi : (P : ℕ → ℕ → Set) →
         (∀ m n → (∀ m' n' → (m' , n') <₂ (m , n) → P m' n') → P m n) →
         ∀ m n → P m n
ℕ-lexi P h m n = h m n (helper m n)
  where
  helper : ∀ a b a' b' → (a' , b') <₂ (a , b) → P a' b'
  helper zero b zero b' (<₂-x ())
  helper zero zero zero b' (<₂-y ())
  helper zero (succ b) zero .b (<₂-y ≤′-refl) = h zero b (helper zero b)
  helper zero (succ b) zero zero (<₂-y (≤′-step x)) = helper zero b zero zero (<₂-y x)
  helper zero (succ b) zero (succ b') (<₂-y (≤′-step x)) = helper zero b zero (succ b') (<₂-y x)
  helper (succ .0) b zero b' (<₂-x ≤′-refl) = h zero b' (helper zero b')
  helper (succ a) b zero b' (<₂-x (≤′-step x)) = helper a b zero b' (<₂-x x)
  helper zero b (succ a') b' (<₂-x ())
  helper (succ .(succ a')) b (succ a') b' (<₂-x ≤′-refl) = h (succ a') b' (helper (succ a') b')
  helper (succ a) b (succ a') b' (<₂-x (≤′-step x)) = helper a b (succ a') b' (<₂-x x)
  helper (succ a) .(succ b') (succ .a) b' (<₂-y ≤′-refl) = h (succ a) b' (helper (succ a) b')
  helper (succ a) .(succ n₁) (succ .a) b' (<₂-y (≤′-step {n₁} x)) = helper (succ a) n₁ (succ a) b' (<₂-y x)
