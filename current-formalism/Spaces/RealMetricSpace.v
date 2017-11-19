(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.


(** This module signature represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)

Class RealMetricSpace (T : Type) {S : Setoid T} `{@EqDec T S} := {
  origin : T;
  dist : T -> T -> R;
  
  add : T -> T -> T;
  mul : R -> T -> T;
  opp : T -> T;
  
  add_compat : Proper (equiv ==> equiv ==> equiv) add;
  mul_compat : Proper (Logic.eq ==> equiv ==> equiv) mul;
  opp_compat : Proper (equiv ==> equiv) opp;
  
  dist_defined : forall x y, dist x y = 0%R <-> equiv x y;
  dist_sym : forall x y, dist y x = dist x y;
  triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%R;
  
  add_assoc : forall u v w, add u (add v w) == add (add u v) w;
  add_comm : forall u v, add u v == add v u;
  add_origin : forall u, add u origin == u;
  add_opp : forall u, add u (opp u) == origin;
  mul_distr_add : forall a u v, mul a (add u v) == add (mul a u) (mul a v);
  mul_morph : forall a b u, mul a (mul b u) == mul (a * b) u;
  add_morph : forall a b u, add (mul a u) (mul b u) == mul (a + b) u;
  
  mul_1 : forall u, mul 1 u == u;
  unit : T; (* TODO: is it really a good name? *)
  non_trivial : unit =/= origin}.

Global Arguments origin : simpl never.

Global Existing Instance add_compat.
Global Existing Instance mul_compat.
Global Existing Instance opp_compat.

(** ***  Proofs of derivable properties about MetricSpace  **)

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

Lemma dist_pos `{RealMetricSpace} : forall x y, (0 <= dist x y)%R.
Proof.
intros x y. apply Rmult_le_reg_l with 2%R.
+ apply Rlt_R0_R2.
+ do 2 rewrite double. rewrite Rplus_0_r.
  assert (Hx : equiv x x) by reflexivity. rewrite <- dist_defined in Hx. rewrite <- Hx.
  setoid_rewrite dist_sym at 3. apply triang_ineq.
Qed.

Lemma add_reg_r `{RealMetricSpace} : forall w u v, add u w == add v w -> u == v.
Proof.
intros w u v Heq. setoid_rewrite <- add_origin.
now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
Qed.

Lemma add_reg_l `{RealMetricSpace} : forall w u v, add w u == add w v -> u == v.
Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.

Lemma opp_origin `{RealMetricSpace} : opp origin == origin.
Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.

Lemma opp_reg `{RealMetricSpace} : forall u v, opp u == opp v -> u == v.
Proof. intros u v Heq. apply (add_reg_r (opp u)). rewrite add_opp, Heq, add_opp. reflexivity. Qed.

Lemma opp_opp `{RealMetricSpace} : forall u, opp (opp u) == u.
Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.

Lemma opp_distr_add `{RealMetricSpace} : forall u v, opp (add u v) == add (opp u) (opp v).
Proof.
intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
Qed.

Lemma mul_0 `{RealMetricSpace} : forall u, mul 0 u == origin.
Proof.
intro u. apply (add_reg_l u).
rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
ring_simplify (1 + 0)%R. now rewrite mul_1.
Qed.

Lemma minus_morph `{RealMetricSpace} : forall k u, mul (-k) u == opp (mul k u).
Proof.
intros k u. apply (add_reg_l (mul k u)).
rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%R.
apply mul_0.
Qed.

Lemma mul_origin `{RealMetricSpace} : forall k, mul k origin == origin.
Proof.
intro k. apply add_reg_l with (mul k origin).
rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
Qed.

Lemma mul_opp `{RealMetricSpace} : forall a u, mul a (opp u) == opp (mul a u).
Proof.
intros a u. apply (add_reg_l (mul a u)). rewrite <- mul_distr_add.
setoid_rewrite add_opp. now rewrite mul_origin.
Qed.

Lemma mul_reg_l `{RealMetricSpace} : forall k u v, k <> 0%R -> mul k u == mul k v -> u == v.
Proof.
intros k u v Hk Heq. setoid_rewrite <- mul_1.
replace 1%R with (/k * k)%R by now field.
setoid_rewrite <- mul_morph. rewrite Heq.
reflexivity.
Qed.

Lemma mul_reg_r `{RealMetricSpace} : forall k k' u, ~u == origin -> mul k u == mul k' u -> k = k'.
Proof.
intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
assert (Heq0 : equiv (mul (k -k') u)  origin).
{ unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
elim Hu. rewrite <- (mul_1 u). rewrite <- (Rinv_l (k - k')).
- rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
- intro Habs. apply Hneq. now apply Rminus_diag_uniq.
Qed.

Definition middle `{RealMetricSpace} u v := mul (1/2)%R (add u v).

Lemma mul_integral `{RealMetricSpace} : forall k u, mul k u == origin -> k = 0%R \/ u == origin.
Proof.
intros k u Heq. destruct (Rdec k 0%R).
- now left.
- right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
Qed.

(** In a real metric space, we can define straight paths as trajectories. *)
Require Import Pactole.Util.Ratio.
Program Definition straight_path {T} `{RealMetricSpace T} (pt pt' : T) : path T :=
  Build_path _ _ (fun x => add pt (mul x (add pt' (opp pt)))) _.
Next Obligation.
abstract (intros x y Hxy; apply add_compat; auto; []; apply mul_compat; try apply Hxy; [];
          apply add_compat, opp_compat; reflexivity).
Defined.

(** We can simplify this definition in the local frame. *)
Definition local_straight_path {T} `{RMS : RealMetricSpace T} (pt : T) : path T.
Proof.
refine (Build_path _ _ (fun x => @mul _ _ _ RMS x pt) _).
abstract (intros x y Hxy; apply mul_compat; reflexivity || apply Hxy).
Defined.
