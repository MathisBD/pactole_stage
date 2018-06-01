(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import Lra.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Export Pactole.Spaces.RealMetricSpace.
Open Scope R_scope.
Open Scope VectorSpace_scope.


Class RealNormedSpace (T : Type) {S : Setoid T} {EQ : @EqDec T S} {VS : RealVectorSpace T} := {
  norm : T -> R;
  
  norm_compat : Proper (equiv ==> Logic.eq) norm; (* maybe this is provable? *)
  
  norm_mul : forall a u, norm (mul a u) == (Rabs a * norm u)%R;
  norm_defined : forall u, norm u = 0%R <-> u == origin;
  triang_ineq : forall u v, (norm (add u v) <= norm u + norm v)%R}.

Global Existing Instance norm_compat.
Arguments norm T%type _ _ _ _ u%VS.
Notation "∥ u ∥" := (norm u) :  VectorSpace_scope.

(** ***  Proofs of derivable properties about RealNormedSpace  **)

Lemma norm_opp `{RealNormedSpace} : forall u, norm (- u) = norm u.
Proof. intro u. rewrite <- (mul_1 u) at 1. now rewrite <- minus_morph, norm_mul, Rabs_Ropp, Rabs_R1, Rmult_1_l. Qed.

(** The metric space induced by the norm. *)
Instance Normed2Metric {T} `{RealNormedSpace T} : RealMetricSpace T := {
  dist := fun u v => norm (u - v)}.
Proof.
+ intros u v. rewrite norm_defined. split; intro Heq.
  - apply (add_reg_r (- v)). now rewrite add_opp.
  - now rewrite Heq, add_opp.
+ intros u v. now rewrite <- (opp_opp (v - u)), opp_distr_add, norm_opp, opp_opp, add_comm.
+ intros u v w. rewrite <- add_origin, <-(add_opp v), <- add_assoc, (add_assoc (- w)),
                          (add_comm (- w)), (add_comm _ (- v)), add_assoc.
  apply triang_ineq.
Defined.

Lemma dist_translation {T} `{RealNormedSpace T} : forall w u v : T, dist (u + w) (v + w) = dist u v.
Proof.
intros w u v. simpl.
now rewrite opp_distr_add, (add_comm (opp v)), <- add_assoc, (add_assoc w), add_opp, add_assoc, add_origin.
Qed.

Lemma dist_homothecy {T} `{RealNormedSpace T} : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R.
Proof. intros. simpl. now rewrite <- norm_mul, mul_distr_add, mul_opp. Qed.

(** The above two properties are enough to characterize a normed space. *)
Definition Metric2Normed {T} `{rmsT : RealMetricSpace T}
                         (translation_prop : forall w u v : T, dist (u + w) (v + w) = dist u v)
                         (homothecy_prop : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R)
  : RealNormedSpace T.
simple refine {| norm := fun x => @dist _ _ _ _ rmsT x (@origin _ _ _ _) |}; autoclass.
Proof.
+ abstract (intros ? ? Heq; now rewrite Heq).
+ abstract (intros ρ u; simpl; rewrite <- (mul_origin ρ) at 1; now rewrite homothecy_prop).
+ abstract (intro; apply dist_defined).
+ abstract (intros u v; rewrite Rplus_comm, <- (translation_prop u v origin), 2 (add_comm _ u), add_origin;
            apply RealMetricSpace.triang_ineq).
Defined.

(* These space transformations are inverse of each other. *)
Lemma Normed2Normed {T} `{rnsT : RealNormedSpace T} :
  forall u, @norm _ _ _ _ (Metric2Normed dist_translation dist_homothecy) u = norm u.
Proof. intro. simpl. now rewrite opp_origin, add_origin. Qed.

Lemma Metric2Metric {T} `{rmsT : RealMetricSpace T}
                    (translation_prop : forall w u v : T, dist (u + w) (v + w) = dist u v)
                    (homothecy_prop : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R) :
  forall u v, @dist _ _ _ _ (@Normed2Metric _ _ _ _ (Metric2Normed translation_prop homothecy_prop)) u v = dist u v.
Proof.
intros. simpl. now rewrite <- (translation_prop v), <- add_assoc,
                           (add_comm _ v), add_opp, (add_comm _ v), 2 add_origin.
Qed.

Lemma dist_subadditive `{RealNormedSpace} : forall u u' v v', dist (u + v) (u' + v') <= dist u u' + dist v v'.
Proof.
intros. etransitivity; [now apply (RealMetricSpace.triang_ineq _ (u' + v)) |].
rewrite dist_translation. setoid_rewrite add_comm. rewrite dist_translation. reflexivity.
Qed.

Lemma dist_opp `{RealNormedSpace} : forall u v, dist (-u) (-v) = dist u v.
Proof.
intros u v. simpl. rewrite <- (norm_opp (u - v)).
apply norm_compat. now rewrite opp_distr_add.
Qed.

Section NormedResults.
  Context {T : Type}.
  Context `{RealNormedSpace T}.
  
  Lemma norm_origin : norm 0 = 0%R.
  Proof. now rewrite norm_defined. Qed.
  
  Lemma triang_ineq_bis : forall u v, (Rabs (norm u - norm v) <= norm (u - v))%R.
  Proof.
  intros u v.
  assert (Hle_u := triang_ineq (u - v) v).
  assert (Hle_v := triang_ineq (v - u) u).
  rewrite <- add_assoc, (add_comm _ v), add_opp, add_origin in Hle_u.
  rewrite <- add_assoc, (add_comm _ u), add_opp, add_origin in Hle_v.
  unfold Rabs. destruct (Rcase_abs (norm u - norm v)).
  + rewrite <- (opp_opp (u - v)), opp_distr_add, opp_opp, norm_opp, add_comm. lra.
  + lra.
  Qed.
  
  Lemma norm_nonneg : forall x, 0 <= norm x.
  Proof.
  intro x. transitivity (Rabs (norm x)).
  + apply Rabs_pos.
  + rewrite <- add_origin at 2. rewrite <- opp_origin.
    replace (norm x) with (norm x - 0)%R by ring.
    rewrite <- norm_origin.
    apply triang_ineq_bis.
  Qed.
  
  Lemma norm_dist : forall u v, dist u v = norm (u - v).
  Proof. intros. reflexivity. Qed.
  
  Lemma square_norm_equiv : forall u k, 0 <= k -> (norm u = k <-> (norm u)² = k²).
  Proof. intros u k Hk. split; intro Heq; try congruence; []. apply pos_Rsqr_eq; trivial; apply norm_nonneg. Qed.
  
  Corollary squared_norm : forall u v, norm u = norm v <-> (norm u)² = (norm v)².
  Proof. intros u v. apply square_norm_equiv. apply norm_nonneg. Qed.
  
  (* Unitary vector in a given direction *)
  Definition unitary u := /(norm u) * u.
  
  (* could be strengthened with [colinear] (up to sign) *)
  Global Instance unitary_compat : Proper (equiv ==> equiv) unitary.
  Proof. intros u v Heq. unfold unitary. now rewrite Heq. Qed.
  
  Lemma norm_unitary : forall u, u =/= origin -> norm (unitary u) = 1.
  Proof.
  intros u Hnull.
  assert (norm u <> 0%R). { now rewrite norm_defined. }
  unfold unitary. rewrite norm_mul, Rabs_pos_eq.
  - now apply Rinv_l.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply norm_nonneg.
  Qed.
  
  Lemma unitary_origin : unitary origin == origin.
  Proof. unfold unitary. apply mul_origin. Qed.
  
  Lemma unitary_is_origin : forall u, unitary u == 0 <-> u == 0.
  Proof.
  intro u. split; intro Heq.
  - null u; try reflexivity; [].
    apply norm_unitary in Hnull. rewrite Heq, norm_origin in Hnull.
    exfalso. now apply R1_neq_R0.
  - now rewrite Heq, unitary_origin.
  Qed.
  
  Lemma unitary_opp : forall u, unitary (- u) == - unitary u.
  Proof. intro u. unfold unitary. now rewrite norm_opp, mul_opp. Qed.
  
  Lemma unitary_mul : forall k u, 0 < k -> unitary (k * u) == unitary u.
  Proof.
  intros k u Hk. null u.
  - now rewrite mul_origin.
  - unfold unitary. rewrite norm_mul. rewrite Rabs_pos_eq; try lra; [].
    rewrite mul_morph. replace (/ (k * norm u) * k)%R with (/norm u)%R; try reflexivity; [].
    field. rewrite norm_defined. split; auto with real.
  Qed.
  
  Lemma unitary_id : forall u, u == (norm u) * unitary u.
  Proof.
  intro u. unfold unitary. rewrite mul_morph. null u.
  - now rewrite mul_origin.
  - rewrite Rinv_r, mul_1; try easy; []. now rewrite norm_defined.
  Qed.
  
  Corollary unitary_is_id : forall u, norm u = 1 -> unitary u == u.
  Proof. intros u Hu. rewrite (unitary_id u) at 2. now rewrite Hu, mul_1. Qed.
  
  Lemma unitary_idempotent : forall u, unitary (unitary u) == unitary u.
  Proof.
  intro u. null u.
  - now rewrite unitary_origin at 1.
  - unfold unitary at 1. rewrite norm_unitary; trivial; []. replace (/1) with 1 by field. apply mul_1.
  Qed.
  
End NormedResults.

Arguments unitary {T%type} {_} {_} {_} {_} u%VS.
