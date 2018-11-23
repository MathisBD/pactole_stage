(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Export Pactole.Spaces.RealVectorSpace.


Class RealMetricSpace (T : Type) {S : Setoid T} `{@EqDec T S} {VS : RealVectorSpace T} := {
  dist : T -> T -> R;
  
  dist_defined : forall u v, dist u v = 0%R <-> u == v;
  dist_sym : forall u v, dist v u = dist u v;
  triang_ineq : forall u v w, (dist u w <= dist u v + dist v w)%R}.

Arguments dist T%type _ _ _ _ u%VS v%VS.

Instance dist_compat `{RealMetricSpace} : Proper (equiv ==> equiv ==> Logic.eq) dist.
Proof.
intros x x' Hx y y' Hy. apply Rle_antisym.
+ replace (dist x' y') with (0 + dist x' y' + 0)%R by ring. symmetry in Hy.
  rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
  rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
  rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
+ replace (dist x y) with (0 + dist x y + 0)%R by ring. symmetry in Hx.
  rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
  rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
  rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
Qed.

Lemma dist_nonneg `{RealMetricSpace} : forall u v, (0 <= dist u v)%R.
Proof.
intros x y. apply Rmult_le_reg_l with 2%R.
+ apply Rlt_R0_R2.
+ do 2 rewrite double. rewrite Rplus_0_r.
  assert (Hx : equiv x x) by reflexivity. rewrite <- dist_defined in Hx. rewrite <- Hx.
  setoid_rewrite dist_sym at 3. apply triang_ineq.
Qed.

Lemma dist_same `{RealMetricSpace} : forall u, (dist u u = 0)%R.
Proof. intro. rewrite dist_defined. reflexivity. Qed.

Section MaxDist.
Context `{RealMetricSpace}.

(** Maximum distance of a list of points to a point. *)
Definition max_dist_pt_list pt := max_list (fun pt' => dist pt pt').

Lemma max_dist_pt_list_nonneg : forall pt l, 0 <= max_dist_pt_list pt l.
Proof. intros. apply max_list_aux_min. Qed.

Lemma max_dist_pt_list_app : forall pt l1 l2,
  max_dist_pt_list pt (l1 ++ l2) = Rmax (max_dist_pt_list pt l1) (max_dist_pt_list pt l2).
Proof. intros. apply max_list_app. Qed.

Global Instance max_dist_pt_list_compat : Proper (equiv ==> equivlistA equiv ==> eq) max_dist_pt_list.
Proof. intros ? ? Heq1. apply max_list_compat. intros ? ? Heq2. now rewrite Heq1, Heq2. Qed.

Lemma max_dist_pt_list_le : forall pt l pt1,
  InA equiv pt1 l -> dist pt pt1 <= max_dist_pt_list pt l.
Proof. intros. apply max_list_le; trivial; now apply dist_compat. Qed.

Lemma max_dist_pt_list_ex : forall pt l, l <> nil ->
  exists pt1, InA equiv pt1 l /\ dist pt pt1 = max_dist_pt_list pt l.
Proof.
intros pt l Hl. destruct (max_list_ex (dist pt) Hl) as [pt' [Hin Heq]].
rewrite Rmax_left in Heq; try apply dist_nonneg; [].
eauto.
Qed.

Lemma max_dist_pt_list_eq_0 : forall pt l,
  max_dist_pt_list pt l = 0%R <-> forall x, InA equiv x l -> x == pt.
Proof.
intros pt l. unfold max_dist_pt_list.
rewrite (max_list_eq_0 (dist_compat _ _ (reflexivity pt)) (dist_nonneg pt)).
setoid_rewrite dist_sym. setoid_rewrite dist_defined.
reflexivity.
Qed.

(** Maximum distance of between lists of points. *)
Definition max_dist_list_list l1 l2 : R :=
  max_list (fun pt => max_dist_pt_list pt l2) l1.

Global Instance max_dist_list_list_compat : Proper (equivlistA equiv ==> equivlistA equiv ==> eq) max_dist_list_list.
Proof.
repeat intro. apply max_list_compat; trivial; [].
repeat intro. now apply max_dist_pt_list_compat.
Qed.

Lemma max_dist_list_list_le : forall pt1 l1 pt2 l2,
  InA equiv pt1 l1 -> InA equiv pt2 l2 -> dist pt1 pt2 <= max_dist_list_list l1 l2.
Proof.
intros. transitivity (max_dist_pt_list pt1 l2).
- now apply max_dist_pt_list_le.
- now apply (max_list_le (fun x y Hxy => max_dist_pt_list_compat x y Hxy _ _ (reflexivity l2))).
Qed.

Lemma max_dist_list_list_ex : forall l1 l2, l1 <> nil -> l2 <> nil ->
  exists pt1 pt2, InA equiv pt1 l1 /\ InA equiv pt2 l2 /\ dist pt1 pt2 = max_dist_list_list l1 l2.
Proof.
intros l1 l2 Hl1 Hl2.
destruct (max_list_ex (fun pt => max_dist_pt_list pt l2) Hl1) as [pt1 [Hin1 Heq1]].
destruct (max_dist_pt_list_ex pt1 _ Hl2) as [pt2 [Hin2 Heq2]].
exists pt1, pt2. repeat split; auto.
unfold max_dist_list_list. rewrite Heq1, Heq2.
rewrite Rmax_left; trivial; [].
transitivity (dist pt1 pt2).
- apply dist_nonneg.
- now apply max_dist_pt_list_le.
Qed.

Lemma max_dist_list_list_cons_le : forall pt l,
  max_dist_list_list l l <= max_dist_list_list (pt :: l) (pt :: l).
Proof.
intros pt [| pt' l].
- cbn. repeat rewrite Rmax_left; apply dist_nonneg.
- destruct (@max_dist_list_list_ex (pt' :: l) (pt' :: l))
    as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]]; try discriminate; [].
  rewrite <- Heq. apply max_dist_list_list_le; now right.
Qed.

End MaxDist.
