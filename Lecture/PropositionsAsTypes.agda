------------------------------------------------------------------------------
-- Dependently typed functional languages - 2011-01

-- Propositions-as-types principle
------------------------------------------------------------------------------

-- References:

-- Ana Bove and Peter Dybjer. Dependent types at work. In Ana Bove et
-- al., editors. LerNet ALFA Summer School 2008, volume 5520 of LNCS,
-- 2009. pp. 57-99.

-- Morten-Heine Sørensen and Paul Urzyczyn. Lectures on the
-- Curry-Howard isomorphism, volume 149 of Studies in Logic and the
-- Foundations of Mathematics. Elsevier, 2006.

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --guardedness              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --warning=all              #-}
{-# OPTIONS --warning=error            #-}
{-# OPTIONS --without-K                #-}

module Lecture.PropositionsAsTypes where

infix  6 ¬_
infixr 6 _,_
infixr 5 _∧_
infixr 4 _∨_
infixr 2 _⇒_
infixr 2 _↔_

------------------------------------------------------------------------------
-- Propositional logic
------------------------------------------------------------------------------

-- Conjunction: Product type

--      Γ ⊢ A      Γ ⊢ B
--  --------------------------- (∧I)
--         Γ ⊢ A ∧ B

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

--        Γ ⊢ A ∧ B
--  --------------------------- (∧E₁)
--           Γ ⊢ A

--        Γ ⊢ A ∧ B
--  --------------------------- (∧E₂)
--           Γ ⊢ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (a , b) = a

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (a , b) = b

------------------------------------------------------------------------------
-- Disjunction: Sum type

--           Γ ⊢ A
--  --------------------------- (∨I₁)
--           Γ ⊢ A ∨ B

--           Γ ⊢ B
--  --------------------------- (∨I₂)
--           Γ ⊢ A ∨ B

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

--    Γ, A ⊢ C   Γ, B ⊢ C    Γ ⊢ A ∨ B
--  ------------------------------------- (∧E)
--           Γ ⊢ C

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
[_,_] f g (inj₁ a) = f a
[_,_] f g (inj₂ b) = g b

------------------------------------------------------------------------------
-- False: Bottom type

-- N.B. There is not introduction rule.

data ⊥ : Set where

--           Γ ⊢ ⊥
--  --------------------------- (⊥E)
--           Γ ⊢ A

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

------------------------------------------------------------------------------
-- True: Unit type

--  --------------------------- (⊤I)
--           Γ ⊢ ⊤

data ⊤ : Set where
  tt : ⊤

-- N.B. There is not elimination rule.

------------------------------------------------------------------------------
-- Implication: Function type

--           Γ, A ⊢ B
--  --------------------------- (→I)
--           Γ ⊢ A → B

data _⇒_ (A B : Set) : Set where
  fun : (A → B) → A ⇒ B

--    Γ ⊢ A       Γ ⊢ A → B
--  --------------------------- (→E)
--           Γ ⊢ B

app : {A B : Set} → A → (A ⇒ B) → B
app a (fun f) = f a

-- N.B. Because the function type is built-in in Agda we will use '→'
-- instead of '⇒'.

------------------------------------------------------------------------------
-- Negation: ¬ A ≡ A → ⊥

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------------
-- Bi-implication: A ↔ B ≡ (A → B) ∧ (B → A)

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

------------------------------------------------------------------------------
-- Examples

a→¬¬a : {A : Set} → A → ¬ ¬ A
a→¬¬a a a→⊥ = a→⊥ a

∧∨-dist : {A B C : Set} → A ∧ (B ∨ C) ↔ A ∧ B ∨ A ∧ C
∧∨-dist {A} {B} {C} = l→r , r→l
  where
  l→r : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C
  l→r (a , inj₁ b) = inj₁ (a , b)
  l→r (a , inj₂ c) = inj₂ (a , c)

  r→l : A ∧ B ∨ A ∧ C → A ∧ (B ∨ C)
  r→l (inj₁ (a , b)) = a , inj₁ b
  r→l (inj₂ (a , c)) = a , inj₂ c

------------------------------------------------------------------------------
-- Predicate logic
------------------------------------------------------------------------------

-- The existential quantifier: Sigma type

-- Notation:
-- FV(β)  : Free variables of a formula β.
-- β[x/t] : The substitution of a term t for every free occurrence of x in β.

--    Γ ⊢ β[x/t]
-- --------------- (∃I)
--    Γ ⊢ ∃x.β

data ∃ (A : Set)(B : A → Set) : Set where
  _,_ : (witness : A) → B witness → ∃ A B

-- Elimination rules
∃-proj₁ : {A : Set}{B : A → Set} → ∃ A B → A
∃-proj₁ (a , _) = a

∃-proj₂ : {A : Set}{B : A → Set}(p : ∃ A B) → B (∃-proj₁ p)
∃-proj₂ (_ , Ba) = Ba

--  Γ ⊢ ∃x.β   Γ, β ⊢ γ
-------------------------- (∃E) (x ∉ FV(Γ,β))
--        Γ ⊢ γ

∃E : {A : Set}{B : A → Set}{C : Set} → ∃ A B → ((a : A) → B a → C) → C
∃E (a , Ba) f = f a Ba

------------------------------------------------------------------------------
-- The universal quantifier: Pi types

--    Γ ⊢ β
-- --------------- (∀I) (x ∉ FV(Γ))
--    Γ ⊢ ∀x.β

data Forall (A : Set)(B : A → Set) : Set where
  dfun : ((x : A) → B x) → Forall A B

--    Γ ⊢ ∀x.β
-- --------------- (∀E)
--    Γ ⊢ β[x/t]

dapp : {A : Set}{B : A → Set} → Forall A B → (t : A) → B t
dapp (dfun f) t = f t

-- N.B. Because the Pi types are built-in in Agda we will use
-- '(x : A) → B x' instead of 'Forall'.

------------------------------------------------------------------------------
-- Examples

module Examples (A C : Set)(B : A → Set) where

  -- It is necessary postulate A ≠ ∅.
  postulate
    someA : A

  -- Generalization of a De Morgan's law.
  gDM : ¬ (∃ A B) ↔ ((x : A) → ¬ (B x))
  gDM = l→r , r→l
    where
    l→r : ¬ (∃ A B) → (x : A) → ¬ (B x)
    l→r f x bx = f (x , bx)

    r→l : ((x : A) → ¬ (B x)) → ¬ (∃ A B)
    r→l f ∃ab = f (∃-proj₁ ∃ab) (∃-proj₂ ∃ab)

  -- Forall to existential.
  ∀→∃ : ((x : A) → B x) → ∃ A B
  ∀→∃ f = someA , (f someA)

  -- Existential quantification over a variable that does not occur can
  -- be delete.
  ∃-erase₁ : ∃ A (λ _ → C) ↔ C
  ∃-erase₁ = l→r , r→l
    where
    l→r : ∃ A (λ _ → C) → C
    l→r (_ , c) = c

    r→l : C → ∃ A (λ _ → C)
    r→l c = someA , c

------------------------------------------------------------------------------
-- Multi-sorted logic, higher-order logic?

-- Example: The constructive axiom of choice
-- From: Simon Thompson. Type theory & functional programming. 1999, p. 236
-- (∀x:A)(∃y:B)P(x, y) → (∃f:A → B)(∀x:A)P(x, f x)

AC : {A B : Set}(P : A → B → Set) →
     ((a : A) → ∃ B λ b → P a b) →
     ∃ (A → B) λ f → (a : A) → P a (f a)
AC {A} {B} P h = f , prf
  where
    f : A → B
    f a = ∃-proj₁ (h a)

    prf : (a : A) → P a (f a)
    prf a = ∃-proj₂ (h a)
