(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
(* Require Import Equalities. *)
(* Require Import Morphisms. *)
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
(* Require Import SetoidList. *)
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Pactole.Models.Flexible.
Require Pactole.Models.Rigid.


Section RigidEquivalence.

Context {loc info : Type}.
Context {Sloc : Setoid loc} {Eloc : EqDec Sloc}.
Context {Sinfo : Setoid info} {Einfo : EqDec Sinfo}.
Context {N : Names}.
Context {Info : Information loc info}.
Context {Spect : Spectrum loc info}.
Context {RMS : RealMetricSpace loc}.

Notation robogram := (@robogram loc info Sloc Eloc Sinfo Einfo Info N Spect).
Notation configuration := (@configuration loc info Sloc Eloc Sinfo Einfo Info N).
Notation Rda := (@Rigid.demonic_action loc info Sloc Eloc RMS N).
Notation Fda := (@Rigid.demonic_action loc info Sloc Eloc RMS N).


Lemma both_branches : forall (test : bool) (A : loc), (if test then mul 1 A else A) == A.
Proof. intros test A. destruct test; now try rewrite mul_1. Qed.


Definition is_rigid (da : @Flexible.demonic_action loc info _ _ _ _) :=
  forall id sim r, da.(Flexible.step) id = Some (sim, r) -> r = 1%R.

Definition rigid_demon d := Stream.forever (Stream.instant is_rigid) d.

(*
Lemma rigid_demon_head : forall d, rigid_demon d -> rigid_da (Stream.hd d).
Proof. intros ? []. auto. Qed.

Lemma rigid_demon_tail : forall d, rigid_demon d -> drigid (Streams.tl d).
Proof. intros ? []. auto. Qed.
*)

(** **  Conversion at the level of demonic_actions  **)

(* TODO: take the proof outside (or make them abstract) to have a cleaner proofterm. *)
Definition R2F_da (rda : @Rigid.demonic_action loc info _ _ _ _) : @Flexible.demonic_action loc info _ _ _ _.
Proof.
refine (@Flexible.Build_demonic_action _ _ _ _ _ _
          rda.(Rigid.relocate_byz)
          (fun id => match rda.(Rigid.step) id with None => None | Some f => Some (f, 1%R) end)
          _ _ _ _).
+ intros ? id ?; subst; destruct (Rigid.step rda id) eqn:Hstep; split; try reflexivity; [].
  intros x y Hxy. simpl. assert (Heq := rda.(Rigid.step_compat) (reflexivity id)).
  rewrite Hstep in Heq. now apply Heq.
+ intros id [sim r] c Heq. destruct (Rigid.step rda id) as [s |] eqn:Hstep.
  - inversion Heq. subst. simpl. eapply Rigid.step_zoom; eassumption.
  - discriminate.
+ intros id [sim r] c Heq. destruct (Rigid.step rda id) as [s |] eqn:Hstep.
  - inversion Heq. subst. simpl. eapply Rigid.step_center; eassumption.
  - discriminate.
+ intros id [sim r] Heq. destruct (Rigid.step rda id) as [s |] eqn:Hstep.
  - inversion Heq. subst. simpl. lra.
  - discriminate.
Defined.

Definition F2R_da (fda : @Flexible.demonic_action loc info _ _ _ _) : @Rigid.demonic_action loc info _ _ _ _.
Proof.
refine (@Rigid.Build_demonic_action _ _ _ _ _ _
          fda.(Flexible.relocate_byz)
          (fun id => match fda.(Flexible.step) id with None => None | Some f => Some (fst f) end)
          _ _ _).
+ intros ? id ?; subst; destruct (Flexible.step fda id) as [[f r] |] eqn:Hstep; try reflexivity.
  intros x y Hxy. simpl. assert (Heq := fda.(Flexible.step_compat) (reflexivity id)).
  rewrite Hstep in Heq. now apply Heq.
+ intros id sim c Heq. destruct (Flexible.step fda id) eqn:Hstep.
  - inversion Heq. subst. eapply Flexible.step_zoom; eassumption.
  - discriminate.
+ intros id sim c Heq. destruct (Flexible.step fda id) eqn:Hstep.
  - inversion Heq. subst. simpl. eapply Flexible.step_center; eassumption.
  - discriminate.
Defined.

Lemma R2F2R_da : forall da, F2R_da (R2F_da da) == da.
Proof.
intro da.
assert (Hstep := Rigid.step_compat da).
destruct da. split; reflexivity || simpl in *; [].
intro id. destruct (step id) eqn:Heq; simpl; trivial.
intros x y Hxy. specialize (Hstep _ _ (reflexivity id)).
rewrite Heq in Hstep. apply Hstep, Hxy.
Qed.

Lemma F2R2F_da : forall da, is_rigid da -> R2F_da (F2R_da da) == da.
Proof.
intros da Hda. unfold is_rigid in Hda.
assert (Hstep := Flexible.step_compat da).
destruct da. split; reflexivity || simpl in *; [].
intro id. destruct (step id) as [[sim r] |] eqn:Heq; simpl; trivial.
split.
- intros x y Hxy. specialize (Hstep _ _ (reflexivity id)).
  rewrite Heq in Hstep. apply Hstep, Hxy.
- compute. now apply Hda in Heq.
Qed.

Lemma R2F_da_rigid : forall da, is_rigid (R2F_da da).
Proof. unfold is_rigid. intros [] * Heq; simpl in *. destruct step; now inversion Heq. Qed.

(** **  Conversion at the level of demons  **)

Definition R2F_d (d : Rigid.demon) : Flexible.demon := Stream.map R2F_da d.
Definition F2R_d (d : Flexible.demon) : Rigid.demon := Stream.map F2R_da d.

Lemma R2F_head : forall d, R2F_da (Stream.hd d) == Stream.hd (R2F_d d).
Proof. intro d. now destruct d. Qed.

Lemma F2R_head : forall d, F2R_da (Stream.hd d) == Stream.hd (F2R_d d).
Proof. intro d. now destruct d. Qed.

Lemma R2F_tail : forall d, R2F_d (Stream.tl d) == Stream.tl (R2F_d d).
Proof. coinduction next_tail. unfold R2F_d. rewrite Stream.map_tl. reflexivity. Qed.

Lemma Flex_Rigid_tail : forall d, F2R_d (Stream.tl d) == Stream.tl (F2R_d d).
Proof. coinduction next_tail. unfold F2R_d. rewrite Stream.map_tl. reflexivity. Qed.

(** **  Equalities on one round  **)

Lemma R2F_round : forall (δ : R) (r : robogram) (rda : Rigid.demonic_action) (config : configuration),
  Rigid.round r rda config == Flexible.round δ r (R2F_da rda) config.
Proof.
unfold R2F_da, Rigid.round, Flexible.round.
intros δ r [] conf [g | b]; simpl.
+ destruct (step (Good g)).
  - now rewrite both_branches; autoclass.
  - now split.
+ now destruct (step (Byz b)).
Qed.

Lemma F2R_round : forall δ r (fda : Flexible.demonic_action) config, is_rigid fda ->
  Flexible.round δ r fda config == Rigid.round r (F2R_da fda) config.
Proof.
unfold F2R_da, Rigid.round, Flexible.round, is_rigid.
intros δ r [] conf Hda [g | b]; simpl in *.
+ specialize (Hda (Good g)). destruct (step (Good g)) as [[sim ρ] |] eqn:Heq.
  - specialize (Hda _ _ (reflexivity _)). subst. now rewrite both_branches; autoclass.
  - now split.
+ now destruct (step (Byz b)) as [[] |].
Qed.

(** **  Equalities on full executions  **)

(** A rigid demon can be turned into a flexible one (that satifties the [rigid] predicate). *)
Theorem R2F_preserves_eq : forall δ r config1 config2 (rd : Rigid.demon),
  config1 == config2 -> Rigid.execute r rd config1 == Flexible.execute δ r (R2F_d rd) config2.
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 rd. constructor; trivial; [].
rewrite Rigid.execute_tail, Flexible.execute_tail. simpl.
apply next_exec. rewrite R2F_round. now apply Flexible.round_compat.
Qed.

Corollary R2F : forall δ r config (rd : Rigid.demon),
  Rigid.execute r rd config == Flexible.execute δ r (R2F_d rd) config.
Proof. intros. now apply R2F_preserves_eq. Qed.

(** A flexible demon that satisfies the [rigid] predicate can be turned into a rigid one. *)
Theorem F2R_preserves_eq : forall δ r config1 config2 (fd : Flexible.demon), rigid_demon fd ->
  config1 == config2 -> Flexible.execute δ r fd config1 == Rigid.execute r (F2R_d fd) config2.
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 fd Hfd. constructor; trivial.
rewrite Rigid.execute_tail, Flexible.execute_tail. simpl.
destruct Hfd. apply next_exec; trivial; [].
rewrite F2R_round; trivial. now apply Rigid.round_compat.
Qed.

Corollary Flex_Rigid : forall δ r config (fd : Flexible.demon), rigid_demon fd ->
  Flexible.execute δ r fd config == Rigid.execute r (F2R_d fd) config.
Proof. intros. now apply F2R_preserves_eq. Qed.

End RigidEquivalence.
