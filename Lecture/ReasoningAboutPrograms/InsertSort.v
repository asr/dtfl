(****************************************************************************)
(* Dependently typed functional languages - CB0683/2011-01 *)

(* Example: Weak/strong specification of sorting a list (using insert sort) *)
(****************************************************************************)

(* Adapted from: *)
(* A sorting example : (C) Yves Bertot, Pierre Castéran *)
(* http://www.labri.fr/perso/casteran/CoqArt/index.html *)

(* Tested with Coq 8.3pl2 *)

Require Import Arith.Arith.
Require Import List.
Require Import Unicode.Utf8.

(****************************************************************************)

(* Weak specification *)

(* Insert an element in an already sorted list *)

Fixpoint insert (n : nat) (xs : list nat) {struct xs} : list nat :=
  match xs with
  | nil         => n :: nil
  | cons x' xs' =>
      match le_gt_dec n x' with
      | left _  => n :: x' :: xs'
      | right _ => x' :: (insert n xs')
      end
  end.

Eval compute in (insert 4 (2 :: 5 :: nil)).

Eval compute in (insert 4 (24 :: 50 ::nil)).

(* The insert sort *)
Fixpoint sortW (xs : list nat) : list nat :=
  match xs with
    | nil         => nil
    | (x' :: xs') => insert x' (sortW xs')
  end.

(* Strong specification *)

(* To be a sorted list *)
Inductive sorted : list nat → Prop :=
  | sorted0 :                                      sorted nil
  | sorted1 : ∀ n,                                 sorted (n :: nil)
  | sorted2 : ∀ m n xs, m ≤ n → sorted (n :: xs) → sorted (m :: n :: xs).

Hint Resolve sorted0 sorted1 sorted2 : sort.

Theorem sort_2357 : sorted (2 :: 3 :: 5 :: 7 :: nil).
Proof.
 auto with sort arith.
Qed.

(* Some properties of the relation sorted *)

Theorem tail_sorted :
 forall (x : nat) (xs : list nat), sorted (x :: xs) → sorted xs.
Proof.
 intros x l H.
 inversion H; auto with sort.
Qed.

(* Number of times that occurs a number in a list *)
Fixpoint occ (n : nat) (xs : list nat) {struct xs} : nat :=
  match xs with
  | nil         => 0%nat
  | (x' :: xs') =>
      match eq_nat_dec n x' with
      | left _  => S (occ n xs')
      | right _ => occ n xs'
      end
  end.

Eval compute in (occ 3 (3 :: 7 :: 3 :: nil)).

Eval compute in (occ 36725 (3 :: 7 :: 3 :: nil)).

(* The relation "to have the same elements" *)

Definition equiv (xs ys : list nat) :=
    forall n : nat, occ n xs = occ n ys.

(* The relation "to have the same elements" is a relation of equivalence *)

Lemma equiv_refl : ∀ xs, equiv xs xs.
Proof.
 unfold equiv; trivial.
Qed.

Lemma equiv_sym : ∀ xs ys, equiv xs ys → equiv ys xs.
Proof.
  unfold equiv; auto.
Qed.

Lemma equiv_trans : ∀ xs ys zs, equiv xs ys → equiv ys zs → equiv xs zs.
Proof.
 intros xs ys zs H H0 n.
 eapply trans_eq; eauto.
Qed.

(* Some properties of the relation "to have the same elements" *)

Lemma equiv_cons :
 forall (n : nat) (xs ys : list nat), equiv xs ys → equiv (n :: xs) (n :: ys).
Proof.
 intros n xs ys H n'.
 simpl; case (eq_nat_dec n' n); auto.
Qed.

Lemma equiv_perm :
 forall (n₁ n₂ : nat) (xs ys: list nat),
   equiv xs ys →
   equiv (n₁ :: n₂ :: xs) (n₂ :: n₁ :: ys).
Proof.
 intros n₁ n₂ xs ys H n; simpl.
 case (eq_nat_dec n n₁); case (eq_nat_dec n n₂);
  simpl; case (H n); auto.
Qed.

Hint Resolve equiv_cons equiv_refl equiv_perm : sort.

(* Some properties of insert *)

(* the insert function seems to be a good tool for sorting ... *)

Lemma insert_equiv : forall (xs : list nat) (n : nat),
                     equiv (n :: xs) (insert n xs).
Proof.
 induction xs as [|a xs' H]; simpl ; auto with sort.
 intros n; case (le_gt_dec n a);
   simpl; auto with sort.
 intro; apply equiv_trans with (a :: n :: xs');
   auto with sort.
Qed.

Lemma insert_sorted :
 forall (xs : list nat) (n : nat), sorted xs → sorted (insert n xs).
Proof.
 intros xs n H; elim H; simpl; auto with sort.
 intro n'; case (le_gt_dec n n'); simpl;
   auto with sort arith.
 intros n1 n2; case (le_gt_dec n n2); simpl; intros;
  case (le_gt_dec n n1); simpl; auto with sort arith.
Qed.

(* The insert sort *)
Definition sortS :
  forall xs : list nat, {ys : list nat | equiv xs ys ∧ sorted ys}.
 induction xs as [| a xs' IHl].
 exists (nil (A:=nat)); split; auto with sort.
 case IHl; intros ys' [H0 H1].
 exists (insert a ys'); split.
 apply equiv_trans with (a :: ys'); auto with sort.
 apply insert_equiv.
 apply insert_sorted; auto.
Defined.

(* The sortS proof term *)
Print sortS.

Eval compute in (sortS (4 :: 1 :: 3 :: 5 :: 2 :: nil)).

(* Code extraction *)
Extraction Language Haskell.
Extraction "InsertSort" insert sortS.
