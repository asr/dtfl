------------------------------------------------------------------------------
-- Natural numbers properties
------------------------------------------------------------------------------

module Extra.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties

open import Extra.Relation.Binary.PreorderReasoning
open import Extra.Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

≤-refl : ∀ n → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≤′-trans : ∀ {m n o} → m ≤′ n → n ≤′ o → m ≤′ o
≤′-trans m≤′n n≤′o = ≤⇒≤′ (≤-trans (≤′⇒≤ m≤′n) (≤′⇒≤ n≤′o))

+-leftIdentity : (n : ℕ) → zero + n ≡ n
+-leftIdentity n = refl

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero    = refl
+-rightIdentity (suc n) = cong suc ( +-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero n o    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

x+Sy≡S[x+y] : ∀ m n → m + suc n ≡ suc (m + n)
x+Sy≡S[x+y] zero    n = refl
x+Sy≡S[x+y] (suc m) n = cong suc (x+Sy≡S[x+y] m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-rightIdentity n)
+-comm (suc m) n =
  begin
    suc m + n   ≡⟨ refl ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + suc m
  ∎
