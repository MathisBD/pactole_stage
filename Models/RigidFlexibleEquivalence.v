(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals Psatz.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.
Require Pactole.Models.Rigid.
Require Pactole.Models.Flexible.


Section RigidFlexibleEquivalence.

Context `{Observation}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Instance Frame : frame_choice (similarity location) := Similarity.FrameChoiceSimilarity.
Context {Tinactive : Type}.
Context `{inactive_choice Tinactive}.
Context {Ina : inactive_function Tinactive}.

(** Flexible demons. *)
Context (Tflex : Type) (delta : R).
Context `{update_choice Tflex}.
Instance FRobot : robot_choice (path location) := { robot_choice_Setoid := path_Setoid location }.
Context {FlexUpdateFun : update_function (path location) (similarity location) Tflex}.
Context `{@Flexible.FlexibleChoice Tflex _}.

Context (Flex : Flexible.FlexibleSetting delta).
Notation flex_da := (@demonic_action _ _ _ _ (path location) (similarity location) Tflex _ _ _).
Notation flex_demon := (@demon _ _ _ _ (path location) (similarity location) Tflex _ _ _).

(** Rigid demons. *)
Context (Trigid : Type).
Context `{update_choice Trigid}.
Instance RRobot : robot_choice location := { robot_choice_Setoid := location_Setoid }.
Context {RigidUpdateFun : update_function location (similarity location) Trigid}.

Context (Rigid : Rigid.RigidSetting).
Notation rigid_da := (@demonic_action _ _ _ _ location (similarity location) Trigid _ _ _).
Notation rigid_demon := (@demon _ _ _ _ location (similarity location) Trigid _ _ _).

(** **  Characterization of flexible demons that act rigidly  **)

(** A flexible choice is rigid if its [move_ratio] is 1. *)
Definition is_rigid choice := Flexible.move_ratio choice == ratio_1.
Definition is_rigid_da (fda : flex_da) :=
  forall config g target, is_rigid (choose_update fda config g target).
Definition is_rigid_demon : flex_demon -> Prop := Stream.forever (Stream.instant is_rigid_da).

Global Instance is_rigid_compat : Proper (equiv ==> iff) is_rigid.
Proof using . intros ? ? Heq. unfold is_rigid. now rewrite Heq. Qed.

Global Instance is_rigid_da_compat : Proper (equiv ==> iff) is_rigid_da.
Proof using . intros ? ? Heq. unfold is_rigid_da. now setoid_rewrite Heq. Qed.

Global Instance is_rigid_demon_compat : Proper (equiv ==> iff) is_rigid_demon.
Proof using . intros ? ? Heq. unfold is_rigid_demon. now rewrite Heq. Qed.

Lemma is_rigid_da_update : forall da : flex_da, is_rigid_da da ->
  forall config g target frame,
  get_location (update config g frame target (choose_update da config g target))
  == target ratio_1.
Proof using Flex.
intros da Hda config g target frame.
destruct (Flexible.ratio_spec config g frame target (choose_update da config g target))
  as [| [Hdist _]]; trivial; [].
specialize (Hda config g target). unfold is_rigid in Hda. rewrite <- Hda. apply Hdist.
Qed.

(** **  Conversions between [demonic_choice]s  **)

(** We assume a way to convert demon choices back and forth. *)
Variable R2F_choice : Trigid -> Tflex.
Variable F2R_choice : Tflex -> Trigid.
Context (F2R_choice_compat : Proper (equiv ==> equiv) F2R_choice).
Context (R2F_choice_compat : Proper (equiv ==> equiv) R2F_choice).
Hypothesis R2F2R_choice : forall choice, F2R_choice (R2F_choice choice) == choice.
Hypothesis F2R2F_choice : forall choice,
  is_rigid choice -> R2F_choice (F2R_choice choice) == choice.
Hypothesis R2F_choice_rigid : forall choice, is_rigid (R2F_choice choice).

(** **  Conversions between [demonic_action]s  **)

Definition R2F_da (rda : rigid_da) : flex_da.
simple refine {|
  activate := rda.(activate);
  relocate_byz := rda.(relocate_byz);
  change_frame := rda.(change_frame);
  choose_update := fun config g target => R2F_choice (rda.(choose_update) config g _);
  choose_inactive := rda.(choose_inactive) |}.
Proof.
+ apply (target ratio_1). (* FIXME: why do we have to go through a "_" in the refine? *)
+ apply precondition_satisfied.
+ apply precondition_satisfied_inv.
+ abstract (repeat intro; apply R2F_choice_compat; now f_equiv).
Defined.

Definition F2R_da (fda : flex_da) : rigid_da.
simple refine {|
  activate := fda.(activate);
  relocate_byz := fda.(relocate_byz);
  change_frame := fda.(change_frame);
  choose_update := fun config g target =>
    F2R_choice (fda.(choose_update) config g (local_straight_path target));
  choose_inactive := fda.(choose_inactive) |}; autoclass.
Proof.
+ apply precondition_satisfied.
+ apply precondition_satisfied_inv.
+ repeat intro. apply F2R_choice_compat.
  f_equiv; trivial; [].
  now apply local_straight_path_compat.
Defined.

Lemma R2F2R_da : forall rda : rigid_da, F2R_da (R2F_da rda) == rda.
Proof using R2F2R_choice.
intro rda. repeat split; try reflexivity; [].
repeat intro. simpl. rewrite mul_1. apply R2F2R_choice.
Qed.

Lemma F2R2F_da : forall fda : flex_da, is_rigid_da fda -> R2F_da (F2R_da fda) == fda.
Proof.
intros fda Hrigid. repeat split; try reflexivity; [].
intros config g target. simpl. rewrite F2R2F_choice; auto; []. f_equiv.
intro r.
(* the demon should only depend on the final target, not the path *)
Abort.

Lemma R2F_da_is_rigid : forall rda, is_rigid_da (R2F_da rda).
Proof using R2F_choice_rigid. intro. hnf. intros. simpl. apply R2F_choice_rigid. Qed.

(** **  Conversions between [demon]s  **)

Definition F2R_demon : flex_demon -> rigid_demon := Stream.map F2R_da.
Definition R2F_demon : rigid_demon -> flex_demon := Stream.map R2F_da.

Lemma R2F2R_demon : forall d, F2R_demon (R2F_demon d) == d.
Proof using R2F2R_choice. coinduction Hcorec. apply R2F2R_da. Qed.

Lemma F2R2F_demon : forall d, is_rigid_demon d -> R2F_demon (F2R_demon d) == d.
Proof.
coinduction Hcorec; match goal with H : is_rigid_demon _ |- _ => destruct H end.
- (* now apply F2R2F_da. *) admit.
- assumption.
Abort.

(** **  Conversions between [robogram]s  **)

Notation flex_robogram := (@robogram _ _ _ _ _ (path location) _).
Notation rigid_robogram := (@robogram _ _ _ _ _ location _).

Instance pgm_R2F_compat : forall r : rigid_robogram,
  Proper (equiv ==> equiv) (fun s => local_straight_path (r s)).
Proof using . intros r s1 s2 Hs. now rewrite Hs. Qed.

Instance pgm_F2R_compat : forall r : flex_robogram,
  Proper (equiv ==> equiv) (fun s => r s ratio_1).
Proof using . intros r s1 s2 Hs. now rewrite Hs. Qed.

Definition R2F_robogram (r : rigid_robogram) : flex_robogram := {|
  pgm := fun s => local_straight_path (r s) |}.

Definition F2R_robogram (r : flex_robogram) : rigid_robogram := {| pgm := fun s => r s ratio_1 |}.

Lemma R2F2R_robogram : forall r : rigid_robogram, F2R_robogram (R2F_robogram r) == r.
Proof using . intros r s. simpl. now rewrite mul_1. Qed.

(** We don't have equality of paths,
    only of the target point as rigid robograms use straight paths. *)
Lemma F2R2F_robogram : forall r : flex_robogram,
  forall s, R2F_robogram (F2R_robogram r) s ratio_1 == r s ratio_1.
Proof using . intros r s. simpl. now rewrite mul_1. Qed.


(** **  Equivalence between [round]s  **)

(** If the location part of the update is the same, then the rest is also the same. *)
Hypothesis update_only_location :
  forall g config frame target1 target2 (choice1 : Tflex) (choice2 : Trigid),
  get_location (update config g frame target1 choice1)
  == get_location (update config g frame target2 choice2) ->
  update config g frame target1 choice1 == update config g frame target2 choice2.

Lemma R2F_round : forall (r : robogram) (rda : rigid_da),
  forall config, round (R2F_robogram r) (R2F_da rda) config == round r rda config.
Proof using Flex R2F_choice_rigid Rigid update_only_location.
intros r rda config id. unfold round.
simpl activate. simpl change_frame. simpl precondition_satisfied. simpl choose_inactive.
repeat destruct_match; try reflexivity ; [].
remember (lift (existT precondition
                       (Bijection.section (frame_choice_bijection (change_frame rda config g)))
                       (precondition_satisfied rda config g))) as sim.
apply lift_compat; try (now intros x y Hxy; simpl; now rewrite Hxy); [].
apply update_only_location.
rewrite Rigid.rigid_update, is_rigid_da_update.
- simpl. now rewrite mul_1.
- apply R2F_da_is_rigid.
Qed.

Lemma F2R_round : forall (r : robogram) (fda : flex_da), is_rigid_da fda ->
  forall config, round (F2R_robogram r) (F2R_da fda) config == round r fda config.
Proof using Flex Rigid update_only_location.
intros r fda Hrigid config id. unfold round.
simpl activate. simpl change_frame. simpl precondition_satisfied. simpl choose_inactive.
repeat destruct_match; try reflexivity; [].
remember (lift (existT precondition
                       (Bijection.section (frame_choice_bijection (change_frame fda config g)))
                       (precondition_satisfied fda config g))) as sim.
apply lift_compat; try (now intros x y Hxy; simpl; now rewrite Hxy); [].
symmetry. apply update_only_location.
rewrite Rigid.rigid_update, is_rigid_da_update.
- reflexivity.
- assumption.
Qed.

(** **  Equivalence between [execution]s  **)

(** A rigid demon can be turned into a flexible one (that satifties the [rigid] predicate). *)
Theorem R2F_preserves_eq : forall r config1 config2 (rd : rigid_demon),
  config1 == config2 -> execute r rd config1 == execute (R2F_robogram r) (R2F_demon rd) config2.
Proof using Flex R2F_choice_rigid Rigid update_only_location.
intro r. cofix next_exec. intros conf1 conf2 d Heq.
constructor; trivial; []. rewrite 2 execute_tail. simpl.
apply next_exec. rewrite R2F_round. now apply round_compat.
Qed.

Corollary R2F : forall r config (d : rigid_demon),
  execute r d config == execute (R2F_robogram r) (R2F_demon d) config.
Proof using Flex R2F_choice_rigid Rigid update_only_location. intros. now apply R2F_preserves_eq. Qed.

(** A flexible demon that satisfies the [rigid] predicate can be turned into a rigid one. *)
Theorem F2R_preserves_eq : forall r config1 config2 (d : flex_demon), is_rigid_demon d ->
  config1 == config2 -> execute r d config1 == execute (F2R_robogram r) (F2R_demon d) config2.
Proof using Flex Rigid update_only_location.
intro r. cofix next_exec. intros conf1 conf2 fd Hfd Heq.
constructor; trivial; []. rewrite 2 execute_tail. simpl.
destruct Hfd. apply next_exec; trivial; [].
rewrite F2R_round; trivial; []. now apply round_compat.
Qed.

Corollary Flex_Rigid : forall r config (d : flex_demon), is_rigid_demon d ->
  execute r d config == execute (F2R_robogram r) (F2R_demon d) config.
Proof using Flex Rigid update_only_location. intros. now apply F2R_preserves_eq. Qed.

End RigidFlexibleEquivalence.

Print Assumptions Flex_Rigid.
