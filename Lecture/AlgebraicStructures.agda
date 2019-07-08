------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Algebraic structures
------------------------------------------------------------------------------

{-# OPTIONS --exact-split    #-}
{-# OPTIONS --guardedness    #-}
{-# OPTIONS --no-sized-types #-}
{-# OPTIONS --safe           #-}
{-# OPTIONS --warning=all    #-}
{-# OPTIONS --warning=error  #-}
{-# OPTIONS --without-K      #-}

module Lecture.AlgebraicStructures where

open import Data.Nat renaming (suc to succ)
open import Function

open import Extra.Data.Nat.Properties
open import Extra.Relation.Binary.PropositionalEquality
open import Extra.Relation.Binary.PreorderReasoning

------------------------------------------------------------------------------
-- Semigroup (S,*) where

-- S : Set
-- * : Associative binary operation

record Semigroup : Set₁  where
  infixl 7 _∙_
  field
    Carrier : Set
    _∙_     : Carrier → Carrier → Carrier
    ∙-assoc : ∀ x y z → x ∙ y ∙ z ≡ x ∙ (y ∙ z)

-- Example: (ℕ,+) is a semigroup.
ℕ-+-semigroup : Semigroup
ℕ-+-semigroup = record
  { Carrier = ℕ
  ; _∙_     = _+_
  ; ∙-assoc = +-assoc
  }

------------------------------------------------------------------------------
-- Monoid (M,*,e) where

-- M : Set
-- * : Associative binary operation
-- e : Identity element

record Monoid : Set₁ where
  infixl 7 _∙_
  field
    Carrier       : Set
    _∙_           : Carrier → Carrier → Carrier
    ∙-assoc       : ∀ x y z → x ∙ y ∙ z ≡ x ∙ (y ∙ z)
    ε             : Carrier
    leftIdentity  : ∀ x → (ε ∙ x) ≡ x
    rightIdentity : ∀ x → (x ∙ ε) ≡ x

-- Example: (ℕ,+,0) is a monoid.
ℕ-+-monoid : Monoid
ℕ-+-monoid = record
  { Carrier       = ℕ
  ; _∙_           = _+_
  ; ∙-assoc       = +-assoc
  ; ε             = zero
  ; leftIdentity  = +-leftIdentity
  ; rightIdentity = +-rightIdentity
  }

------------------------------------------------------------------------------
-- Monoids properties

module MonoidsProperties (M : Monoid) where

  open Monoid M

  x≡y→xz≡yz : ∀ {a b c} → a ≡ b → a ∙ c ≡ b ∙ c
  x≡y→xz≡yz refl = refl

  -- If the square of every element is the identity, the system is
  -- commutative. From: TPTP (v5.0.0). File: Problems/GRP/GRP001-2.p
  x²≡ε→comm : (∀ a → a ∙ a ≡ ε) → ∀ {b c d} → b ∙ c ≡ d → c ∙ b ≡ d
  -- Paper proof:
  -- 1. d(bc)  = dd  (Hypothesis bc = d).
  -- 2. d(bc)  = ε   (Hypothesis dd = ε).
  -- 3. d(bc)c = c   (By 2).
  -- 4. db(cc) = c   (Associativity).
  -- 5. db     = c   (Hypothesis cc = ε).
  -- 6. (db)b  = cb  (By 5).
  -- 7. d(bb)  = cb  (Associativity).
  -- 6. d      = cb  (Hypothesis bb = ε).
  x²≡ε→comm h {b} {c} {d} bc≡d = sym d≡cb
    where
    db≡c : d ∙ b ≡ c
    db≡c =
      begin
        d ∙ b             ≡⟨ sym (rightIdentity (d ∙ b)) ⟩
        d ∙ b ∙ ε         ≡⟨ cong (_∙_ (d ∙ b)) (sym (h c)) ⟩
        d ∙ b ∙ (c ∙ c)   ≡⟨ ∙-assoc d b (c ∙ c) ⟩
        d ∙ (b ∙ (c ∙ c)) ≡⟨ cong (_∙_ d) (sym (∙-assoc b c c)) ⟩
        d ∙ ((b ∙ c) ∙ c) ≡⟨ cong (_∙_ d) (cong (flip _∙_ c) bc≡d) ⟩
        d ∙ (d ∙ c)       ≡⟨ sym (∙-assoc d d c) ⟩
        d ∙ d ∙ c         ≡⟨ cong (flip _∙_ c) (h d) ⟩
        ε ∙ c             ≡⟨ leftIdentity c ⟩
        c
      ∎

    d≡cb : d ≡ c ∙ b
    d≡cb =
      begin
        d           ≡⟨ sym (rightIdentity d) ⟩
        d ∙ ε       ≡⟨ cong (_∙_ d) (sym (h b)) ⟩
        d ∙ (b ∙ b) ≡⟨ sym (∙-assoc d b b) ⟩
        d ∙ b ∙ b   ≡⟨ x≡y→xz≡yz db≡c ⟩
        c ∙ b
      ∎
