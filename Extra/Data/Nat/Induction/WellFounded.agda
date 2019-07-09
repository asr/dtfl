------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Extra.Data.Nat.Induction.WellFounded where

open import Data.Nat renaming (suc to succ)

open import Extra.Data.Nat.Properties

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers

-- Let P be an predicate

--            ∀ x. (∀ y. y < x  → P y) → P x
-----------------------------------------------
--              ∀ x. P x

-- From http://code.haskell.org/~dolio/agda-share/induction/.
<-wfind : (P : ℕ → Set) →
          (∀ n → (∀ m → m < n → P m) → P n) →
          ∀ n → P n
<-wfind P ih n = ih n (helper n)
  where
  helper : ∀ n m → m < n → P m
  helper zero     m        ()
  helper (succ n) zero     _          = ih zero (λ _ ())
  helper (succ n) (succ m) (s≤s Sm≤n) =
    ih (succ m) (λ m' Sm'≤Sm → helper n m' (≤-trans Sm'≤Sm Sm≤n))

<′-wfind : (P : ℕ → Set) →
           (∀ n → (∀ m → m <′ n → P m) → P n) →
           ∀ n → P n
<′-wfind P ih n = ih n (helper n)
  where
  helper : ∀ n m → m <′ n → P m
  helper .(succ m) m ≤′-refl             = ih m (helper m)
  helper .(succ n) m (≤′-step {n} Sm≤′n) = helper n m Sm≤′n
