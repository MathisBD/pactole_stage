(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import Lia.
Require Import Lra.
Require Import SetoidList.
Require Import SetoidDec.
Require Import RelationPairs.
Require Import Pactole.Util.Coqlib.
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

Section NormedResults.
  Context {T : Type}.
  Context `{RealNormedSpace T}.
  
  Lemma norm_opp `{RealNormedSpace} : forall u, norm (- u) = norm u.
  Proof using .
  intro u. rewrite <- (mul_1 u) at 1.
  now rewrite <- minus_morph, norm_mul, Rabs_Ropp, Rabs_R1, Rmult_1_l.
  Qed.
  
  Lemma norm_origin : norm 0 = 0%R.
  Proof using . now rewrite norm_defined. Qed.
  
  Lemma triang_ineq_bis : forall u v, (Rabs (norm u - norm v) <= norm (u - v))%R.
  Proof using .
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
  Proof using .
  intro x. transitivity (Rabs (norm x)).
  + apply Rabs_pos.
  + rewrite <- add_origin at 2. rewrite <- opp_origin.
    replace (norm x) with (norm x - 0)%R by ring.
    rewrite <- norm_origin.
    apply triang_ineq_bis.
  Qed.
  
  Lemma square_norm_equiv : forall u k, 0 <= k -> (norm u = k <-> (norm u)² = k²).
  Proof using .
  intros u k Hk. split; intro Heq; try congruence; [].
  apply pos_Rsqr_eq; trivial; apply norm_nonneg.
  Qed.
  
  Corollary squared_norm : forall u v, norm u = norm v <-> (norm u)² = (norm v)².
  Proof using . intros u v. apply square_norm_equiv. apply norm_nonneg. Qed.
  
  (* Unitary vector in a given direction *)
  Definition unitary u := /(norm u) * u.
  
  (* could be strengthened with [colinear] (up to sign) *)
  Global Instance unitary_compat : Proper (equiv ==> equiv) unitary.
  Proof using . intros u v Heq. unfold unitary. now rewrite Heq. Qed.
  
  Lemma norm_unitary : forall u, u =/= origin -> norm (unitary u) = 1.
  Proof using .
  intros u Hnull.
  assert (norm u <> 0%R). { now rewrite norm_defined. }
  unfold unitary. rewrite norm_mul, Rabs_pos_eq.
  - now apply Rinv_l.
  - apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply norm_nonneg.
  Qed.
  
  Lemma unitary_origin : unitary origin == origin.
  Proof using . unfold unitary. apply mul_origin. Qed.
  
  Lemma unitary_is_origin : forall u, unitary u == 0 <-> u == 0.
  Proof using .
  intro u. split; intro Heq.
  - null u; try reflexivity; [].
    apply norm_unitary in Hnull. rewrite Heq, norm_origin in Hnull.
    exfalso. now apply R1_neq_R0.
  - now rewrite Heq, unitary_origin.
  Qed.
  
  Lemma unitary_opp : forall u, unitary (- u) == - unitary u.
  Proof using . intro u. unfold unitary. now rewrite norm_opp, mul_opp. Qed.
  
  Lemma unitary_mul : forall k u, 0 < k -> unitary (k * u) == unitary u.
  Proof using .
  intros k u Hk. null u.
  - now rewrite mul_origin.
  - unfold unitary. rewrite norm_mul. rewrite Rabs_pos_eq; try lra; [].
    rewrite mul_morph. replace (/ (k * norm u) * k)%R with (/norm u)%R; try reflexivity; [].
    field. rewrite norm_defined. split; auto with real.
  Qed.
  
  Lemma unitary_id : forall u, u == (norm u) * unitary u.
  Proof using .
  intro u. unfold unitary. rewrite mul_morph. null u.
  - now rewrite mul_origin.
  - rewrite Rinv_r, mul_1; try easy; []. now rewrite norm_defined.
  Qed.
  
  Corollary unitary_is_id : forall u, norm u = 1 -> unitary u == u.
  Proof using . intros u Hu. rewrite (unitary_id u) at 2. now rewrite Hu, mul_1. Qed.
  
  Lemma unitary_idempotent : forall u, unitary (unitary u) == unitary u.
  Proof using .
  intro u. null u.
  - now rewrite unitary_origin at 1.
  - unfold unitary at 1. rewrite norm_unitary; trivial; [].
    replace (/1) with 1 by field. apply mul_1.
  Qed.
  
  (** ***  Normed and Metric Spaces  **)
  
  (** The metric space induced by the norm. *)
  Global Instance Normed2Metric : RealMetricSpace T.
  refine {| dist := fun u v => norm (u - v) |}.
  Proof.
  + intros u v. rewrite norm_defined. split; intro Heq.
    - apply (add_reg_r (- v)). now rewrite add_opp.
    - now rewrite Heq, add_opp.
  + intros u v. now rewrite <- (opp_opp (v - u)), opp_distr_add, norm_opp, opp_opp, add_comm.
  + intros u v w. rewrite <- add_origin, <-(add_opp v), <- add_assoc, (add_assoc (- w)),
                            (add_comm (- w)), (add_comm _ (- v)), add_assoc.
    apply triang_ineq.
  Defined.
  
  Lemma dist_translation : forall w u v, dist (u + w) (v + w) = dist u v.
  Proof using .
  intros w u v. simpl.
  now rewrite opp_distr_add, (add_comm (opp v)),
              <- add_assoc, (add_assoc w), add_opp, add_assoc, add_origin.
  Qed.
  
  Lemma dist_homothecy : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R.
  Proof using . intros. simpl. now rewrite <- norm_mul, mul_distr_add, mul_opp. Qed.
  
  Lemma dist_subadditive : forall u u' v v', dist (u + v) (u' + v') <= dist u u' + dist v v'.
  Proof using .
  intros. etransitivity; [now apply (RealMetricSpace.triang_ineq _ (u' + v)) |].
  rewrite dist_translation. setoid_rewrite add_comm. rewrite dist_translation. reflexivity.
  Qed.
  
  Lemma dist_opp : forall u v, dist (-u) (-v) = dist u v.
  Proof using .
  intros u v. simpl. rewrite <- (norm_opp (u - v)).
  apply norm_compat. now rewrite opp_distr_add.
  Qed.
  
  Lemma norm_dist : forall u v, dist u v = norm (u - v).
  Proof using . intros. reflexivity. Qed.
  
End NormedResults.

(** Building a normed space from a metric one. *)
Definition Metric2Normed {T} `{rmsT : RealMetricSpace T}
  (translation_prop : forall w u v : T, dist (u + w) (v + w) = dist u v)
  (homothecy_prop : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R)
  : RealNormedSpace T.
simple refine {| norm := fun x => @dist _ _ _ _ rmsT x (@origin _ _ _ _) |}; autoclass.
Proof.
+ abstract (intros ? ? Heq; now rewrite Heq).
+ abstract (intros ρ u; simpl; rewrite <- (mul_origin ρ) at 1; now rewrite homothecy_prop).
+ abstract (intro; apply dist_defined).
+ abstract (intros u v; rewrite Rplus_comm, <- (translation_prop u v origin), 2 (add_comm _ u),
                                add_origin; apply RealMetricSpace.triang_ineq).
Defined.

(* These space transformations are inverse of each other. *)
Lemma Normed2Normed {T} `{rnsT : RealNormedSpace T} :
  forall u, @norm _ _ _ _ (Metric2Normed dist_translation dist_homothecy) u = norm u.
Proof using . intro. simpl. now rewrite opp_origin, add_origin. Qed.

Lemma Metric2Metric {T} `{rmsT : RealMetricSpace T}
                    (trans_prop : forall w u v : T, dist (u + w) (v + w) = dist u v)
                    (homothecy_prop : forall ρ u v, dist (ρ * u) (ρ * v) = (Rabs ρ * dist u v)%R) :
  forall u v, @dist _ _ _ _ (@Normed2Metric _ _ _ _ (Metric2Normed trans_prop homothecy_prop)) u v
              = dist u v.
Proof using .
intros. simpl. now rewrite <- (trans_prop v), <- add_assoc,
                           (add_comm _ v), add_opp, (add_comm _ v), 2 add_origin.
Qed.

(** ***  Results about barycenters  **)

Section BarycenterResults.
  Context {T : Type}.
  Context `{RealNormedSpace T}.
  
  (* Let W be the sum of all weights,
         PT the weighted sum of all points,
     and dm the diameter of the configuration (= max distance between two points).
     Then, we have:
        forall pt, dist(W pt, PT) = R2norm(W pt - PT)
                                  = R2norm(Sum[i=0..n](w_i pt) - Sum[i=0..n](w_i p_i))
                                  = R2norm(Sum[i=0..n](w_i (pt - p_i)))
                                 <= Sum[i=0..n](w_i R2norm(pt - p_i))     by triangular inequality
                                 <= Sum[i=0..n](w_i dm))                  by definition of diameter
                                  = dm Sum[i=0..n](w_i)
                                  = dm W *)
  Definition weighted_sqr_dist_sum (pt: T) (E: list (T * R)) : R :=
    List.fold_left (fun acc pt' => acc + snd pt' * (dist pt (fst pt'))²)%R E 0%R.
  (*
  Axiom barycenter_n_spec :
    forall (E: list (R2.t * R)),
      forall p,
        weighted_sqr_dist_sum (barycenter E) E <= weighted_sqr_dist_sum p E.
  *)
  Definition is_barycenter_n (E : list (T * R)) (B: T) : Prop :=
    forall p, weighted_sqr_dist_sum B E <= weighted_sqr_dist_sum p E.
  
  Axiom barycenter_n_spec : forall (E: list (T * R)),
      is_barycenter_n E (barycenter E).
  Axiom barycenter_n_unique: forall E a b,
      is_barycenter_n E a -> is_barycenter_n E b -> a == b.
  
  Lemma weighted_sqr_dist_sum_compat :
    Proper (equiv ==> PermutationA (equiv * eq) ==> eq) weighted_sqr_dist_sum.
  Proof using .
  intros u v Hpt E1 E2 Hperm.
  unfold weighted_sqr_dist_sum.
  assert (Heq : (eq ==> equiv * eq ==> eq)%signature
                  (fun (acc : R) (pt' : T * R) => (acc + snd pt' * (dist u (fst pt'))²)%R)
                  (fun (acc : R) (pt' : T * R) => (acc + snd pt' * (dist v (fst pt'))²)%R)).
  { intros ? acc ? [u1 k1] [u2 k2] [Heq1 Heq2].
    compute in Heq1, Heq2. subst. simpl. rewrite Heq1, Hpt. ring. }
  rewrite (fold_left_compat Heq (reflexivity E1) _ _ (reflexivity 0%R)). clear u Hpt Heq.
  generalize (eq_refl 0%R).
  generalize 0%R at 2 4. generalize 0%R.
  revert E1 E2 Hperm.
  change (Proper (PermutationA (equiv * eq) ==> eq ==> eq)
                 (List.fold_left (fun acc pt'  => acc + snd pt' * (dist v (fst pt'))²))%R).
  apply fold_left_symmetry_PermutationA; autoclass.
  + intros ? ? ? [] [] [Heq ?]. hnf in *; cbn -[dist] in *; subst.
    do 3 f_equal. now apply dist_compat.
  + intros [] [] ?. hnf; simpl in *; ring || f_equal; ring.
  Qed.
  
  Lemma barycenter_dist_decrease_aux : forall dm E pt sumR,
    0 <= sumR ->
    (forall p, InA (equiv@@1)%signature p E -> dist (sumR * (fst p)) pt <= sumR * dm) ->
    (forall p, InA (equiv * eq)%signature p E -> 0 < snd p) ->
    (forall p1 p2, InA (equiv@@1)%signature p1 E -> InA (equiv@@1)%signature p2 E ->
                   dist (fst p1) (fst p2) <= dm) ->
    let '(sum_pt, sum_coeff) := barycenter_aux E (pt, sumR) in
    forall p, InA (equiv@@1)%signature p E -> dist (sum_coeff * (fst p)) sum_pt <= sum_coeff * dm.
  Proof using .
  intros dm E.
  assert (Hincl : inclA (equiv * eq)%signature E E) by easy.
  revert Hincl. generalize E at 1 7. intro E'.
  induction E' as [| [pt1 w1] E']; intros Hincl pt sum Hsum Hbase Hpos Hdm.
  * simpl. intros ? Habs. now apply Hbase.
  * assert (Hincl' : inclA (equiv * eq)%signature E' E). { intros ? ?. apply Hincl. now right. }
    assert (0 < w1). { change w1 with (snd (pt1, w1)). apply Hpos, Hincl; now left. }
    specialize (IHE' Hincl' (w1 * pt1 + pt) (w1 + sum)%R). simpl.
    destruct (barycenter_aux E' (w1 * pt1 + pt, (w1 + sum)%R)) as [bary coeff] eqn:Hbary.
    intros [pt' w'] Hptw'. simpl.
    assert (Hin : exists w, InA (equiv * eq)%signature (pt', w) E).
    { setoid_rewrite InA_alt. rewrite InA_alt in Hptw'. destruct Hptw' as [y [Heq Hin]].
      exists (snd y), y. split; trivial; []. destruct y. split; try reflexivity; []. apply Heq. }
    clear Hptw' w'. destruct Hin as [w' Hptw'].
    change pt' with (fst (pt', w')). apply IHE'.
    + lra.
    + intros pw Hin. simpl.
      rewrite <- add_morph. etransitivity; try apply dist_subadditive; [].
      rewrite Rmult_plus_distr_r. apply Rplus_le_compat.
      - rewrite dist_homothecy, Rabs_right; try lra; []. apply Rmult_le_compat_l; try lra; [].
        change pt1 with (fst (pt1, w1)). apply Hdm; trivial; [].
        cut (InA (equiv * eq)%signature (pt1, w1) E);
        try (now apply InA_impl_compat; reflexivity || apply FstRel_sub); [].
        apply Hincl. now left.
      - now apply Hbase.
    + repeat intro. now apply Hpos.
    + repeat intro. now apply Hdm.
    + revert Hptw'. apply InA_impl_compat; try reflexivity; []. apply FstRel_sub.
  Qed.
  
  (* NB: This lemma requires a normed space for [dist_homothecy],
         everything else can be done in a metric space. *)
  Lemma barycenter_dist_decrease : forall (E : list (T * R)) (dm : R),
    (forall p, InA (equiv * eq)%signature p E -> 0 < snd p) ->
    (forall p1 p2, InA equiv p1 (List.map fst E) -> InA equiv p2 (List.map fst E) ->
                   dist p1 p2 <= dm) ->
    forall p : T, InA equiv p (List.map fst E) -> dist p (barycenter E) <= dm.
  Proof using .
  intros E dm Hweight Hdist p Hin.
  assert (Proper (equiv ==> equiv) (@fst T R)). { intros [] [] [Heq _]. apply Heq. }
  assert (Hdist' : forall p1 p2, InA (equiv@@1)%signature p1 E ->
                                 InA (equiv@@1)%signature p2 E -> dist (fst p1) (fst p2) <= dm).
  { intros [] [] Hin1 Hin2. cbn -[dist].
    apply Hdist; rewrite (@InA_map_iff _ _ (equiv@@1)%signature); autoclass; try easy; [|];
    (eexists; now split; [| apply Hin1 + apply Hin2]; eauto). }
  assert (Hbase' : forall p, InA (equiv @@1)%signature p E -> dist (0 * fst p) 0 <= 0 * dm).
  { clear. intros p _. rewrite mul_0, dist_same. lra. }
  assert (Hrec := @barycenter_dist_decrease_aux dm E origin 0 (Rle_refl 0) Hbase' Hweight Hdist').
  unfold barycenter.
  destruct (barycenter_aux E (origin, 0%R)) as [sum weight] eqn:Heq.
  rewrite (@InA_map_iff _ _ (equiv * eq)%signature) in Hin; autoclass; [].
  destruct Hin as [xn [Heq' Hin]]. specialize (Hrec xn).
  assert (Hpos : 0 < weight).
  { replace weight with (snd (barycenter_aux E (origin, 0%R))) by now rewrite Heq.
    apply barycenter_aux_snd_pos.
    - reflexivity.
    - destruct E; discriminate || rewrite InA_nil in Hin; tauto.
    - rewrite Forall_forall. intros. apply Hweight. apply In_InA; autoclass. }
  rewrite <- (mul_1 sum) in Hrec.
  replace 1 with (weight * (1 / weight))%R in Hrec by now field; apply Rgt_not_eq.
  rewrite <- mul_morph, dist_homothecy, Rabs_pos_eq in Hrec; try lra; [].
  apply Rmult_le_reg_l in Hrec; trivial.
  - now rewrite <- Heq'.
  - revert Hin. apply InA_impl_compat; autoclass.
  Qed.
  
  (** Same results about the isobarycenter *)
  Definition sqr_dist_sum_aux (init: R) (pt: T) (E: list T) : R :=
    List.fold_left (fun acc pt' => acc + (dist pt pt')²)%R E init.
  
  Definition sqr_dist_sum := sqr_dist_sum_aux 0.
  
  Definition is_isobarycenter_n E B : Prop :=
    forall p, sqr_dist_sum B E <= sqr_dist_sum p E.
  
  Axiom isobarycenter_n_spec : forall E,
      is_isobarycenter_n E (isobarycenter E).
  Axiom isobarycenter_n_unique: forall E a b,
      is_isobarycenter_n E a -> is_isobarycenter_n E b -> a == b.
  
  Lemma sqr_dist_sum_aux_compat :
    Proper (Logic.eq ==> equiv ==> PermutationA equiv ==> Logic.eq) sqr_dist_sum_aux.
  Proof using .
  intros i1 i2 Heqi pt1 pt2 Heqpt E1 E2 Hperm.
  unfold sqr_dist_sum_aux.
  assert (Heq : (eq ==> equiv ==> eq)%signature
                  (fun (acc : R) (pt' : T) => (acc + (dist pt1 pt')²)%R)
                  (fun (acc : R) (pt' : T) => (acc + (dist pt2 pt')²)%R)).
  { intros ? ? ? ? ? Heq. subst. now rewrite Heq, Heqpt. }
  rewrite (fold_left_compat Heq (reflexivity E1) _ _ Heqi). clear Heq Heqi i1.
  apply fold_left_symmetry_PermutationA; trivial.
  + intros ? ? ? ? ? Heq. subst. now rewrite Heq.
  + intros. ring.
  Qed.
  
  Global Instance sqr_dist_sum_compat :
    Proper (equiv ==> PermutationA equiv ==> Logic.eq) sqr_dist_sum.
  Proof using . now apply sqr_dist_sum_aux_compat. Qed.
  
  Lemma isobarycenter_dist_decrease_aux : forall E dm,
      E <> nil ->
      (forall p1 p2, InA equiv p1 E -> InA equiv p2 E -> dist p1 p2 <= dm) ->
      forall p, (forall q, InA equiv q E -> dist p q <= dm) ->
                dist p (isobarycenter E) <= dm.
  Proof using .
  intros E dm Hnotempty Hdm p Hp.
  assert (Hlength_pos: 0 < INR (List.length E)).
  { apply lt_0_INR. destruct E; try (now elim Hnotempty); []. simpl. lia. }
  rewrite norm_dist. subst. unfold isobarycenter.
  setoid_replace p%VS with (- / INR (length E) * (- INR (length E) * p))%VS
    by (rewrite mul_morph, Ropp_inv_permute, <- Rinv_l_sym, mul_1; lra || reflexivity).
  rewrite <- minus_morph, <- mul_distr_add, norm_mul, Rabs_Ropp, Rabs_right;
  try (now apply Rle_ge, Rlt_le, Rinv_0_lt_compat); [].
  apply Rmult_le_reg_l with (r := INR (length E)); trivial; [].
  rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l; try lra; [].
  induction E as [| a [| b E]].
  + now elim Hnotempty.
  + specialize (Hp a ltac:(now left)). cbn -[mul add norm].
    setoid_replace ((-(1) * p) + (0 + a))%VS with (a - p)%VS
      by now rewrite add_origin_l, add_comm, minus_morph, mul_1.
    now rewrite Rmult_1_l, <- norm_dist, dist_sym.
  + clear Hlength_pos Hnotempty.
    set (F := b :: E). fold F in IHE, Hdm, Hp.
    set (lF := length F). fold lF in IHE.
    replace (length (a :: F)) with (1 + lF)%nat; [ | simpl; reflexivity ].
    rewrite add_comm, S_INR, Ropp_plus_distr, <- add_morph, Rmult_plus_distr_r, Rmult_1_l.
    cbn [fold_left].
    rewrite fold_add_acc, <- add_assoc, (add_comm a), <- add_assoc, add_assoc.
    setoid_replace ((-(1) * p) + a)%VS with (a - p)%VS by now rewrite add_comm, minus_morph, mul_1.
    rewrite triang_ineq.
    apply Rplus_le_compat.
    - rewrite add_comm. apply IHE; intuition; unfold lF, F; try discriminate; [].
      cbn [length]. rewrite S_INR.
      apply Rplus_le_lt_0_compat; apply pos_INR || apply Rlt_0_1.
    - rewrite <- norm_dist, dist_sym. apply Hp. now left.
  Qed.
  
  Lemma isobarycenter_dist_decrease : forall E dm,
      E <> nil ->
      (forall p1 p2, InA equiv p1 E -> InA equiv p2 E -> dist p1 p2 <= dm) ->
      forall p, InA equiv p E -> dist p (isobarycenter E) <= dm.
  Proof using .
  intros E dm Hnotempty Hdm p Hp.
  apply (isobarycenter_dist_decrease_aux _ _ Hnotempty Hdm).
  intros q Hq. now apply Hdm.
  Qed.
  
End BarycenterResults.

Arguments unitary {T%type} {_} {_} {_} {_} u%VS.
