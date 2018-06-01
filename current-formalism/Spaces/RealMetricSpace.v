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
