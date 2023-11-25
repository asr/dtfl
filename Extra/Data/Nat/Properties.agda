------------------------------------------------------------------------------
-- Natural numbers properties
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

module Extra.Data.Nat.Properties where

open import Data.Empty
open import Data.Nat renaming (suc to succ) hiding ( _≤′?_ )
open import Data.Nat.Properties
  hiding ( _≤′?_ ; ≤-refl ; ≤-trans ; ≤′-trans ; +-assoc ; +-comm )

open import Extra.Relation.Binary.PreorderReasoning
open import Extra.Relation.Binary.PropositionalEquality

open import Relation.Binary
open import Relation.Nullary

------------------------------------------------------------------------------

≤-refl : ∀ n → n ≤ n
≤-refl zero     = z≤n
≤-refl (succ n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≤′-trans : ∀ {m n o} → m ≤′ n → n ≤′ o → m ≤′ o
≤′-trans m≤′n n≤′o = ≤⇒≤′ (≤-trans (≤′⇒≤ m≤′n) (≤′⇒≤ n≤′o))

+-leftIdentity : (n : ℕ) → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = cong succ ( +-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero     n o   = refl
+-assoc (succ m) n o = cong succ (+-assoc m n o)

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero     n = refl
x+Sy≡S[x+y] (succ m) n = cong succ (x+Sy≡S[x+y] m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero     n = sym (+-rightIdentity n)
+-comm (succ m) n =
  begin
    succ m + n   ≡⟨ refl ⟩
    succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + succ m
  ∎

infix 4 _≤′?_

_≤′?_ : Decidable _≤′_
m ≤′? n with m ≤? n
... | yes p = yes (≤⇒≤′ p)
... | no ¬p = no (λ m≤′n → ¬p (≤′⇒≤ m≤′n))

x≰′y→x>′y : ∀ {m n} → ¬ (m ≤′ n) → m >′ n
x≰′y→x>′y {zero}   {n}      h = ⊥-elim (h z≤′n)
x≰′y→x>′y {succ m} {zero}   h = ≤⇒≤′ (s≤s z≤n)
x≰′y→x>′y {succ m} {succ n} h with m ≤′? n
... | yes p = ⊥-elim (h (s≤′s p))
... | no ¬p = ≤⇒≤′ (s≤s (≤′⇒≤ (x≰′y→x>′y ¬p)))
