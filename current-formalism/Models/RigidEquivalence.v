(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


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

Context {loc : Type}.
Context {Sloc : Setoid loc}.
Context {ESloc : EqDec Sloc}.
Context {RMS : @RealMetricSpace loc Sloc ESloc}.
Context {Ndef : NamesDef}.
Context {N : Names}.
Context {Spect : @Spectrum loc Sloc ESloc Ndef N}.


Definition rigid da := forall id sim r, da.(Flexible.step) id = Some (sim, r) -> r = 1%R.

CoInductive drigid d :=
  | Drigid : rigid (Streams.hd d) -> drigid (Streams.tl d) -> drigid d.

Lemma drigid_head : forall d, drigid d -> rigid (Streams.hd d).
Proof. intros ? []. auto. Qed.

Lemma drigid_tail : forall d, drigid d -> drigid (Streams.tl d).
Proof. intros ? []. auto. Qed.

Lemma the_chosen_one {A} eqA (HeqA : Reflexive eqA) :
  forall f : loc -> A, Proper (equiv ==> eqA) f ->
  forall δ conf local_target,
  let chosen_target := mul 1%R local_target in
  eqA (f (if Rle_bool δ (dist chosen_target conf) then chosen_target else local_target))
      (f local_target).
Proof. intros f Hf ? ? ?. simpl. destruct Rle_bool; apply Hf; try rewrite mul_1; reflexivity. Qed.

(** **  Conversion at the level of demonic_actions  **)

(* TODO: take the proof outside (or make them abstract) to have a cleaner proofterm. *)
Definition Rigid_Flex_da (rda : Rigid.demonic_action) : Flexible.demonic_action.
Proof.
refine (@Flexible.Build_demonic_action _ _ _ _ _
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

Definition Flex_Rigid_da (fda : Flexible.demonic_action) : Rigid.demonic_action.
Proof.
refine (@Rigid.Build_demonic_action _ _ _ _ _
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

Lemma Rigid_Flex_Rigid_da : forall da, @equiv _ Rigid.da_Setoid (Flex_Rigid_da (Rigid_Flex_da da)) da.
Proof.
intro da.
assert (Hstep := Rigid.step_compat da).
destruct da. split; reflexivity || simpl in *; [].
intro id. destruct (step id) eqn:Heq; simpl; trivial.
intros x y Hxy. specialize (Hstep _ _ (reflexivity id)).
rewrite Heq in Hstep. apply Hstep, Hxy.
Qed.

Lemma Flex_Rigid_Flex_da : forall da, rigid da -> @equiv _ Flexible.da_Setoid (Rigid_Flex_da (Flex_Rigid_da da)) da.
Proof.
intros da Hda. unfold rigid in Hda.
assert (Hstep := Flexible.step_compat da).
destruct da. split; reflexivity || simpl in *; [].
intro id. destruct (step id) as [[sim r] |] eqn:Heq; simpl; trivial.
split.
- intros x y Hxy. specialize (Hstep _ _ (reflexivity id)).
  rewrite Heq in Hstep. apply Hstep, Hxy.
- compute. now apply Hda in Heq.
Qed.

Lemma Rigid_Flex_da_rigid : forall da, rigid (Rigid_Flex_da da).
Proof. unfold rigid. intros [] * H; simpl in *. destruct step; now inversion H. Qed.

(** **  Conversion at the level of demons  **)

CoFixpoint Rigid_Flex_d (d : Rigid.demon) : Flexible.demon :=
  Streams.cons (Rigid_Flex_da (Streams.hd d)) (Rigid_Flex_d (Streams.tl d)).

CoFixpoint Flex_Rigid_d (d : Flexible.demon) : Rigid.demon :=
  Streams.cons (Flex_Rigid_da (Streams.hd d)) (Flex_Rigid_d (Streams.tl d)).

Lemma Rigid_Flex_head : forall d,
  @equiv _ Flexible.da_Setoid (Rigid_Flex_da (Streams.hd d)) (Streams.hd (Rigid_Flex_d d)).
Proof. intro d. now destruct d. Qed.

Lemma Flex_Rigid_head : forall d,
  @equiv _ Rigid.da_Setoid (Flex_Rigid_da (Streams.hd d)) (Streams.hd (Flex_Rigid_d d)).
Proof. intro d. now destruct d. Qed.

Lemma Rigid_Flex_tail : forall d,
  @equiv _ Flexible.demon_Setoid (Rigid_Flex_d (Streams.tl d)) (Streams.tl (Rigid_Flex_d d)).
Proof. coinduction next_tail. now destruct d as [da1 [da2 d]]. Qed.

Lemma Flex_Rigid_tail : forall d,
  @equiv _ Rigid.demon_Setoid (Flex_Rigid_d (Streams.tl d)) (Streams.tl (Flex_Rigid_d d)).
Proof. coinduction next_tail. now destruct d as [da1 [da2 d]]. Qed.

(** **  Equalities on one round  **)

Lemma Rigid_Flex_round : forall δ (r : robogram) rda conf,
   Rigid.round r rda conf == Flexible.round δ r (Rigid_Flex_da rda) conf.
Proof.
unfold Rigid_Flex_da, Rigid.round, Flexible.round.
intros δ r [] conf [g | b]; simpl.
+ destruct (step (Good g)).
  - now rewrite the_chosen_one; autoclass.
  - reflexivity.
+ now destruct (step (Byz b)).
Qed.

Lemma Flex_Rigid_round : forall δ r fda conf, rigid fda ->
  Flexible.round δ r fda conf == Rigid.round r (Flex_Rigid_da fda) conf.
Proof.
unfold Flex_Rigid_da, Rigid.round, Flexible.round, rigid.
intros δ r [] conf Hda [g | b]; simpl in *.
+ specialize (Hda (Good g)). destruct (step (Good g)) as [[sim ρ] |] eqn:Heq.
  - specialize (Hda _ _ (reflexivity _)). subst. now rewrite the_chosen_one; autoclass.
  - reflexivity.
+ now destruct (step (Byz b)) as [[] |].
Qed.

(** **  Equalities on full executions  **)

(** A rigid demon can be turned into a flexible one (that satifties the [rigid] predicate). *)
Theorem Rigid_Flex_preserves_eq : forall δ r conf1 conf2 (rd : Rigid.demon),
  conf1 == conf2 -> Rigid.execute r rd conf1 == Flexible.execute δ r (Rigid_Flex_d rd) conf2.
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 rd. constructor; trivial.
rewrite Rigid.execute_tail, Flexible.execute_tail. simpl.
apply next_exec. rewrite Rigid_Flex_round. now apply Flexible.round_compat.
Qed.

Corollary Rigid_Flex : forall δ r conf (rd : Rigid.demon),
  Rigid.execute r rd conf == Flexible.execute δ r (Rigid_Flex_d rd) conf.
Proof. intros. now apply Rigid_Flex_preserves_eq. Qed.

(** A flexible demon that satisfies the [rigid] predicate can be turned into a rigid one. *)
Theorem Flex_Rigid_preserves_eq : forall δ r conf1 conf2 (fd : Flexible.demon), drigid fd ->
  conf1 == conf2 -> Flexible.execute δ r fd conf1 == Rigid.execute r (Flex_Rigid_d fd) conf2.
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 fd Hfd. constructor; trivial.
rewrite Rigid.execute_tail, Flexible.execute_tail. simpl.
destruct Hfd. apply next_exec; trivial.
rewrite Flex_Rigid_round; trivial. now apply Rigid.round_compat.
Qed.

Corollary Flex_Rigid : forall δ r conf (fd : Flexible.demon), drigid fd ->
  Flexible.execute δ r fd conf == Rigid.execute r (Flex_Rigid_d fd) conf.
Proof. intros. now apply Flex_Rigid_preserves_eq. Qed.

End RigidEquivalence.
