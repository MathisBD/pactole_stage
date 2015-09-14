Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.FlexibleFormalism.
Require Import Pactole.RigidFormalism.


Module RigidEquivalence (Location : RealMetricSpace)(N : Size)(Spect : Spectrum(Location)(N)).

Module Common := CommonRealFormalism.Make(Location)(N)(Spect).
Module Flex := FlexibleFormalism.Make(Location)(N)(Spect)(Common).
Module Rigid := RigidFormalism.Make(Location)(N)(Spect)(Common).

Definition rigid da := forall id sim r, da.(Flex.step) id = Some (sim, r) -> r = 1%R.

CoInductive drigid d :=
  | Drigid : rigid (Flex.demon_head d) -> drigid (Flex.demon_tail d) -> drigid d.

Lemma drigid_head : forall d, drigid d -> rigid (Flex.demon_head d).
Proof. intros ? []. auto. Qed.

Lemma drigid_tail : forall d, drigid d -> drigid (Flex.demon_tail d).
Proof. intros ? []. auto. Qed.

Import Common.

Lemma the_chosen_one {A} eqA (HeqA : Reflexive eqA) :
  forall f : Location.t -> A, Proper (Location.eq ==> eqA) f ->
  forall δ conf local_target,
  let chosen_target := Location.mul 1%R local_target in
  eqA (f (if Rle_bool δ (Location.dist chosen_target conf) then chosen_target else local_target))
      (f local_target).
Proof. intros f Hf ? ? ?. simpl. destruct Rle_bool; apply Hf; try rewrite Location.mul_1; reflexivity. Qed.

(** **  Conversion at the level of demonic_actions  **)

(* TODO: take the proof outside (or make them abstract) to have a cleaner proofterm. *)
Definition Rigid_Flex_da (rda : Rigid.demonic_action) : Flex.demonic_action.
Proof.
refine (@Flex.Build_demonic_action
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

Definition Flex_Rigid_da (fda : Flex.demonic_action) : Rigid.demonic_action.
Proof.
refine (@Rigid.Build_demonic_action
          fda.(Flex.relocate_byz)
          (fun id => match fda.(Flex.step) id with None => None | Some f => Some (fst f) end)
          _ _ _).
+ intros ? id ?; subst; destruct (Flex.step fda id) as [[f r] |] eqn:Hstep; try reflexivity.
  intros x y Hxy. simpl. assert (Heq := fda.(Flex.step_compat) (reflexivity id)).
  rewrite Hstep in Heq. now apply Heq.
+ intros id sim c Heq. destruct (Flex.step fda id) eqn:Hstep.
  - inversion Heq. subst. eapply Flex.step_zoom; eassumption.
  - discriminate.
+ intros id sim c Heq. destruct (Flex.step fda id) eqn:Hstep.
  - inversion Heq. subst. simpl. eapply Flex.step_center; eassumption.
  - discriminate.
Defined.

Lemma Rigid_Flex_Rigid_da : forall da, Rigid.da_eq (Flex_Rigid_da (Rigid_Flex_da da)) da.
Proof.
intro da.
assert (Hstep := Rigid.step_compat da).
destruct da. split; reflexivity || simpl in *; [].
intro id. destruct (step id) eqn:Heq; simpl; trivial.
intros x y Hxy. specialize (Hstep _ _ (reflexivity id)).
rewrite Heq in Hstep. apply Hstep, Hxy.
Qed.

Lemma Flex_Rigid_Flex_da : forall da, rigid da -> Flex.da_eq (Rigid_Flex_da (Flex_Rigid_da da)) da.
Proof.
intros da Hda. unfold rigid in Hda.
assert (Hstep := Flex.step_compat da).
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

CoFixpoint Rigid_Flex_d (d : Rigid.demon) : Flex.demon :=
  Flex.NextDemon (Rigid_Flex_da (Rigid.demon_head d)) (Rigid_Flex_d (Rigid.demon_tail d)).

CoFixpoint Flex_Rigid_d (d : Flex.demon) : Rigid.demon :=
  Rigid.NextDemon (Flex_Rigid_da (Flex.demon_head d)) (Flex_Rigid_d (Flex.demon_tail d)).

Lemma Rigid_Flex_head : forall d,
  Flex.da_eq (Rigid_Flex_da (Rigid.demon_head d)) (Flex.demon_head (Rigid_Flex_d d)).
Proof. intro d. now destruct d. Qed.

Lemma Flex_Rigid_head : forall d,
  Rigid.da_eq (Flex_Rigid_da (Flex.demon_head d)) (Rigid.demon_head (Flex_Rigid_d d)).
Proof. intro d. now destruct d. Qed.

Lemma Rigid_Flex_tail : forall d, Flex.deq (Rigid_Flex_d (Rigid.demon_tail d)) (Flex.demon_tail (Rigid_Flex_d d)).
Proof. coinduction next_tail. now destruct d as [da1 [da2 d]]. Qed.

Lemma Flex_Rigid_tail : forall d, Rigid.deq (Flex_Rigid_d (Flex.demon_tail d)) (Rigid.demon_tail (Flex_Rigid_d d)).
Proof. coinduction next_tail. now destruct d as [da1 [da2 d]]. Qed.

(** **  Equalities on one round  **)

Lemma Rigid_Flex_round : forall δ r rda conf,
  Config.eq (Rigid.round r rda conf) (Flex.round δ r (Rigid_Flex_da rda) conf).
Proof.
unfold Rigid_Flex_da, Rigid.round, Flex.round.
intros δ r [] conf [g | b]; simpl.
+ destruct (step (Good g)).
  - rewrite the_chosen_one; try reflexivity. refine _. refine _.
  - reflexivity.
+ now destruct (step (Byz b)).
Qed.

Lemma Flex_Rigid_round : forall δ r fda conf, rigid fda ->
  Config.eq (Flex.round δ r fda conf) (Rigid.round r (Flex_Rigid_da fda) conf).
Proof.
unfold Flex_Rigid_da, Rigid.round, Flex.round, rigid.
intros δ r [] conf Hda [g | b]; simpl in *.
+ specialize (Hda (Good g)). destruct (step (Good g)) as [[sim ρ] |] eqn:Heq.
  - specialize (Hda _ _ (reflexivity _)). subst. rewrite the_chosen_one; try reflexivity. refine _. refine _.
  - reflexivity.
+ now destruct (step (Byz b)) as [[] |].
Qed.

(** **  Equalities on full executions  **)

(** A rigid demon can be turned into a flexible one (that satifties the [rigid] predicate). *)
Theorem Rigid_Flex_preserves_eq : forall δ r conf1 conf2 (rd : Rigid.demon),
  Config.eq conf1 conf2 -> Common.eeq (Rigid.execute r rd conf1) (Flex.execute δ r (Rigid_Flex_d rd) conf2).
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 rd. constructor; trivial.
rewrite Rigid.execute_tail, Flex.execute_tail. simpl.
apply next_exec. rewrite Rigid_Flex_round. now f_equiv.
Qed.

Corollary Rigid_Flex : forall δ r conf (rd : Rigid.demon),
  Common.eeq (Rigid.execute r rd conf) (Flex.execute δ r (Rigid_Flex_d rd) conf).
Proof. intros. now apply Rigid_Flex_preserves_eq. Qed.

(** A flexible demon that satisfies the [rigid] predicate can be turned into a rigid one. *)
Theorem Flex_Rigid_preserves_eq : forall δ r conf1 conf2 (fd : Flex.demon), drigid fd ->
  Config.eq conf1 conf2 -> Common.eeq (Flex.execute δ r fd conf1) (Rigid.execute r (Flex_Rigid_d fd) conf2).
Proof.
intros δ r. cofix next_exec. intros conf1 conf2 fd Hfd. constructor; trivial.
rewrite Rigid.execute_tail, Flex.execute_tail. simpl.
destruct Hfd. apply next_exec; trivial.
rewrite Flex_Rigid_round; trivial. now f_equiv.
Qed.

Corollary Flex_Rigid : forall δ r conf (fd : Flex.demon), drigid fd ->
  Common.eeq (Flex.execute δ r fd conf) (Rigid.execute r (Flex_Rigid_d fd) conf).
Proof. intros. now apply Flex_Rigid_preserves_eq. Qed.

End RigidEquivalence.
