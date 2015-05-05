Require Import Reals.
Require Import Sorting.
Require Import Relations.
Require Import Morphisms.
Require Import SetoidPermutation.
Import Permutation List.
Require Import Pactole.Preliminary.


Set Implicit Arguments.


(** *  Some result about sorting  *)

Import Mergesort.

Definition Rleb (x y : R) := if Rle_lt_dec x y then true else false.

Lemma Rleb_spec : forall x y, Rleb x y = true <-> Rle x y.
Proof.
intros x y; unfold Rleb; destruct (Rle_lt_dec x y); split; intro H; trivial. inversion H. elim (Rlt_not_le _ _ r H).
Qed.

Corollary Rleb_total : forall x y, Rleb x y = true \/ Rleb y x = true.
Proof.
intros x y. unfold Rleb. destruct (Rle_lt_dec x y).
  now left.
  right. destruct (Rle_lt_dec y x). reflexivity. elim (Rlt_irrefl x). now apply Rlt_trans with y.
Qed.
Local Coercion is_true : bool >-> Sortclass.

Corollary Rleb_trans : Transitive Rleb.
Proof. intros ? ? ?. unfold is_true. setoid_rewrite Rleb_spec. apply Rle_trans. Qed.

Module Rletot : Orders.TotalLeBool with Definition t := R
                                   with Definition leb := Rleb.
  Definition t := R.
  Definition leb := Rleb.
  Definition leb_total := Rleb_total.
End Rletot.

Import Sorted.
Module Rsort := Mergesort.Sort(Rletot).
Export Rsort.

Ltac Rle_dec :=
  match goal with
    | |- context[Rle_lt_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rle_lt_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Theorem StronglySorted_uniq :
  forall l l', StronglySorted Rleb l -> StronglySorted Rleb l' -> Permutation l l' -> l = l'.
Proof.
intros l l' Hl. revert l Hl l'.
apply (StronglySorted_ind (fun l => forall l' : list R, StronglySorted Rleb l' -> Permutation l l' -> l = l')).
+ intros l' _ Hperm. symmetry. now apply Permutation_nil.
+ intros a l Hl IHl Hle l' Hl' Hperm. destruct l' as [| b l'].
  - apply Permutation_nil. now symmetry.
  - assert (a = b).
    { destruct (Req_dec a b); trivial. apply Rle_antisym.
      - rewrite List.Forall_forall in Hle. rewrite <- Rleb_spec. apply Hle.
        cut (List.In b (a :: l)). now intros [|].
        rewrite Hperm. now left.
      - apply StronglySorted_inv in Hl'. destruct Hl' as [_ Hl'].
        rewrite List.Forall_forall in Hl'. rewrite <- Rleb_spec. apply Hl'.
        cut (List.In a (b :: l')). now intros [Hin | Hin]; try symmetry in Hin.
        rewrite <- Hperm. now left. }
    subst. f_equal. apply IHl. now apply StronglySorted_inv in Hl'.
    now apply Permutation_cons_inv with b.
Qed.

Instance sort_uniq : Proper (@Permutation R ==> eq) sort.
Proof.
intros l l' Hl. apply StronglySorted_uniq.
- apply StronglySorted_sort. exact Rleb_trans.
- apply StronglySorted_sort. exact Rleb_trans.
- transitivity l. symmetry. apply Permuted_sort. transitivity l'. assumption. apply Permuted_sort.
Qed.

Instance sort_uniqA : Proper (PermutationA eq ==> eq) sort.
Proof. intros ? ?. rewrite PermutationA_Leibniz. apply sort_uniq. Qed.

Corollary StronglySorted_sort_identity : forall l, StronglySorted Rleb l -> sort l = l.
Proof.
intros l Hl. apply StronglySorted_uniq.
apply StronglySorted_sort. apply Rleb_trans.
assumption.
symmetry. apply Permuted_sort.
Qed.

Corollary sort_idempotent : forall l, sort (sort l) = sort l.
Proof. intros l. apply StronglySorted_sort_identity. apply StronglySorted_sort. apply Rleb_trans. Qed.

Lemma StronglySorted_alls : forall x n, StronglySorted Rleb (alls x n).
Proof.
intros x n. induction n. constructor.
apply SSorted_cons. assumption.
rewrite List.Forall_forall. intros e Hin. apply alls_In in Hin. subst.
unfold is_true. rewrite Rleb_spec. apply Rle_refl.
Qed.

Lemma sort_alls : forall pt n, sort (alls pt n) = alls pt n.
Proof. intros. apply StronglySorted_sort_identity. apply StronglySorted_alls. Qed.

Open Scope R_scope.

Theorem sort_min : forall (s : list R) (d x : R), List.In x s ->
  (List.hd d (sort s) <= x)%R.
Proof.
intros s d x Hin.
assert (Hsort := StronglySorted_sort s Rleb_trans).
assert (Hperm := Permuted_sort s).
destruct (sort s).
- symmetry in Hperm. apply Permutation_nil in Hperm. subst. now inversion Hin.
- simpl. rewrite Hperm in Hin. destruct Hin. subst. apply Rle_refl.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort Hmin].
  rewrite List.Forall_forall in Hmin. rewrite <- Rleb_spec. now apply Hmin.
Qed.

Theorem sort_max : forall (s : list R) (d x : R), List.In x s ->
  (x <= List.last (sort s) d)%R.
Proof.
intros s d x Hin.
assert (Hsort := StronglySorted_sort s Rleb_trans).
assert (Hperm := Permuted_sort s).
rewrite Hperm in Hin. revert Hsort x Hin. clear Hperm. generalize (sort s).
apply (@StronglySorted_ind R _ (fun l => forall x : R, List.In x l -> x <= List.last l d)).
now intros ? [].
intros a l Hsorted HP Hle x Hin. destruct Hin.
- subst. destruct l. simpl. apply Rle_refl.
  apply Rle_trans with r. inversion_clear Hle. now rewrite <- Rleb_spec. apply HP. now left.
- destruct l. inversion H. now apply HP.
Qed.

(* Existing Instance Permutation_map_aux_Proper. *)

Lemma StronglySorted_map_increasing : forall A B (RA : relation A) (RB : relation B) f, Proper (RA ==> RB) f ->
  forall l, StronglySorted RA l -> StronglySorted RB (map f l).
Proof.
intros A B RA RB f Hf l Hl. induction Hl; simpl; constructor.
  assumption.
  induction H; simpl; constructor.
    now apply Hf.
    apply IHForall.
      now inversion_clear Hl.
      now inversion_clear IHHl.
Qed.

Corollary sort_map_increasing : forall f, Proper (Rleb ==> Rleb) f -> forall l, sort (map f l) = map f (sort l).
Proof.
intros f Hf l. rewrite (Permuted_sort l) at 1.
apply StronglySorted_sort_identity, (StronglySorted_map_increasing Hf), (StronglySorted_sort l Rleb_trans).
Qed.

Lemma StronglySorted_map_decreasing : forall A B (RA : relation A) (RB : relation B) f,
  Proper (RA --> RB) f -> Transitive RB ->
  forall l, StronglySorted RA l -> StronglySorted RB (rev (map f l)).
Proof.
intros A B RA RB f Hf HB l Hl. rewrite <- map_rev. induction Hl; simpl.
* now constructor.
* rewrite map_app. apply Sorted_StronglySorted. now apply HB. apply sort_app.
  + now apply StronglySorted_Sorted.
  + now repeat constructor.
  + intros x y Hx Hy. inversion_clear Hy.
    - subst y. rewrite (in_map_iff f _ _) in Hx.
        destruct Hx as [z [Heq Hin]]. subst x. rewrite <- (In_rev _) in Hin. apply Hf. unfold Basics.flip.
        rewrite Forall_forall in H. now apply H.
    - now inversion H0.
Qed.

Corollary sort_map_decreasing : forall f, Proper (Rleb --> Rleb) f ->
  forall l, sort (map f l) = rev (map f (sort l)).
Proof.
intros f Hf l. rewrite (Permuted_sort l) at 1. rewrite (Permutation_rev (map f (sort l))) at 1.
apply StronglySorted_sort_identity, (StronglySorted_map_decreasing Hf), (StronglySorted_sort l Rleb_trans).
apply Rleb_trans.
Qed.
