------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers
------------------------------------------------------------------------------

module Extra.Data.Nat.Induction.WellFounded where

open import Data.Nat

open import Extra.Data.Nat.Properties

------------------------------------------------------------------------------
-- Well-founded induction on the natural numbers

-- Let P be an predicate

--            ∀ x. (∀ y. y < x  → P y) → P x
-----------------------------------------------
--              ∀ x. P x

-- From http://code.haskell.org/~dolio/agda-share/induction/.
wfIndℕ-< : (P : ℕ → Set) →
           (∀ n → (∀ m → m < n → P m) → P n) →
           ∀ n → P n
wfIndℕ-< P ih n = ih n (helper n)
  where
  helper : ∀ n m → m < n → P m
  helper zero     m        ()
  helper (suc n) zero    _          = ih zero (λ _ ())
  helper (suc n) (suc m) (s≤s Sm≤n) =
    ih (suc m) (λ m' Sm'≤Sm → helper n m' (≤-trans Sm'≤Sm Sm≤n))

wfIndℕ-<′ : (P : ℕ → Set) →
            (∀ n → (∀ m → m <′ n → P m) → P n) →
            ∀ n → P n
wfIndℕ-<′ P ih n = ih n (helper n)
  where
  helper : ∀ n m → m <′ n → P m
  helper .(suc m) m ≤′-refl             = ih m (helper m)
  helper .(suc n) m (≤′-step {n} Sm≤′n) = helper n m Sm≤′n
