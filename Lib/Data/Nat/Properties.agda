------------------------------------------------------------------------------
-- Natural numbers properties
------------------------------------------------------------------------------

module Lib.Data.Nat.Properties where

open import Lib.Data.Nat

open import Lib.Relation.Binary.PreorderReasoning
open import Lib.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

≤-refl : ∀ n → n ≤ n
≤-refl zero     = z≤n
≤-refl (succ n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

+-leftIdentity : (n : ℕ) → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = cong succ ( +-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero n o     = refl
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
