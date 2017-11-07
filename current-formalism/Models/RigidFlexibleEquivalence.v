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


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
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

Context {loc info T : Type}.
Context `{IsLocation loc info}.
Context {RMS : RealMetricSpace loc}.
Context `{Names}.
Context {Spect : Spectrum loc info}.
Context `{@frame_choice loc info T _ _ _ _ _}.

(** Flexible demons. *)
Context (Tflex : Type) (delta : R).
Context `{update_choice Tflex}.
Context {FlexUpdateFun : @update_function loc info Tflex _ _ _ _ _ _ _}.
Context `{@Flexible.FlexibleChoice Tflex _}.

Context (Flex : @Flexible.FlexibleUpdate loc info _ Tflex _ _ _ _ _ _ _ _ _ _ _ delta).
Notation flex_da := (@demonic_action loc info _ Tflex _ _ _ _).
Notation flex_demon := (@demon loc info _ Tflex _ _ _ _).

(** Rigid demons. *)
Context (Trigid : Type).
Context `{update_choice Trigid}.
Context {RigidUpdateFun : @update_function loc info Trigid _ _ _ _ _ _ _}.
Context {Rigid : @Rigid.RigidUpdate loc info _ Trigid _ _ _ _ _ _ _ _ _}.
Notation rigid_da := (@demonic_action loc info _ Trigid _ _ _ _).
Notation rigid_demon := (@demon loc info _ Trigid _ _ _ _).

(** **  Characterization of flexible demons that acts rigidly  **)

(** A flexible choice is rigid if its [move_ratio] is 1. *)
Definition is_rigid choice := (Flexible.move_ratio choice : R) = 1.
Definition is_rigid_da (fda : flex_da) :=
  forall config g target, is_rigid (choose_update fda config g target).
Definition is_rigid_demon : flex_demon -> Prop := Stream.forever (Stream.instant is_rigid_da).

Global Instance is_rigid_compat : Proper (equiv ==> iff) is_rigid.
Proof. intros ? ? Heq. unfold is_rigid. now rewrite Heq. Qed.

Global Instance is_rigid_da_compat : Proper (equiv ==> iff) is_rigid_da.
Proof. intros ? ? Heq. unfold is_rigid_da. now setoid_rewrite Heq. Qed.

Global Instance is_rigid_demon_compat : Proper (equiv ==> iff) is_rigid_demon.
Proof. intros ? ? Heq. unfold is_rigid_demon. now rewrite Heq. Qed.

Lemma is_rigid_da_update : forall da, is_rigid_da da ->
  forall config g target, get_location (update config g target (choose_update da config g target)) == target.
Proof.
intros da Hda config g target.
destruct (Flexible.flexible_update da config g target) as [| [Hdist _]]; trivial; [].
assert (Hratio := Flexible.ratio_spec da config g target). simpl in Hratio.
rewrite Hratio in Hdist. rewrite Hda in Hdist.
rewrite <- dist_defined. lra.
Qed.

(** **  Conversions between [demonic_choice]s  **)

(** We assume a way to convert demon choices back and forth. *)
Parameter R2F_choice : Trigid -> Tflex.
Parameter F2R_choice : Tflex -> Trigid.
Declare Instance F2R_choice_compat : Proper (equiv ==> equiv) F2R_choice.
Declare Instance R2F_choice_compat : Proper (equiv ==> equiv) R2F_choice.
Axiom R2F2R_choice : forall choice, F2R_choice (R2F_choice choice) == choice.
Axiom F2R2F_choice : forall choice, is_rigid choice -> R2F_choice (F2R_choice choice) == choice.
Axiom R2F_choice_rigid : forall choice, is_rigid (R2F_choice choice).

(** **  Conversions between [demonic_action]s  **)

Definition R2F_da (rda : rigid_da) : flex_da.
refine {|
  activate := rda.(activate);
  relocate_byz := rda.(relocate_byz);
  change_frame := rda.(change_frame);
  choose_update := fun config g target => R2F_choice (rda.(choose_update) config g target) |}.
Proof. abstract (repeat intro; apply R2F_choice_compat; now f_equiv). Defined.

Definition F2R_da (fda : flex_da) : rigid_da.
refine {|
  activate := fda.(activate);
  relocate_byz := fda.(relocate_byz);
  change_frame := fda.(change_frame);
  choose_update := fun config g target => F2R_choice (fda.(choose_update) config g target) |}.
Proof. abstract (repeat intro; apply F2R_choice_compat; now f_equiv). Defined.

Lemma R2F2R_da : forall rda : rigid_da, F2R_da (R2F_da rda) == rda.
Proof.
intro rda. repeat split; try reflexivity; [].
repeat intro. simpl. apply R2F2R_choice.
Qed.

Lemma F2R2F_da : forall fda : flex_da, is_rigid_da fda -> R2F_da (F2R_da fda) == fda.
Proof.
intros fda Hrigid. repeat split; try reflexivity; [].
repeat intro. simpl. rewrite F2R2F_choice; auto.
Qed.

Lemma R2F_da_is_rigid : forall rda, is_rigid_da (R2F_da rda).
Proof. intro. hnf. intros. simpl. apply R2F_choice_rigid. Qed.

(** **  Conversions between [demon]s  **)

Definition F2R_demon : flex_demon -> rigid_demon := Stream.map F2R_da.
Definition R2F_demon : rigid_demon -> flex_demon := Stream.map R2F_da.

Lemma R2F2R_demon : forall d, F2R_demon (R2F_demon d) == d.
Proof. coinduction Hcorec. apply R2F2R_da. Qed.

Lemma F2R2F_demon : forall d, is_rigid_demon d -> R2F_demon (F2R_demon d) == d.
Proof.
coinduction Hcorec; match goal with H : is_rigid_demon _ |- _ => destruct H end.
- now apply F2R2F_da.
- assumption.
Qed.

(** **  Equivalence between [round]s  **)

(** If the location part of the update is the same, then the rest is also the same. *)
Axiom update_only_location : forall g config1 config2 target1 target2 (choice1 : Tflex) (choice2 : Trigid),
  get_location (update config1 g target1 choice1) == get_location (update config2 g target2 choice2) ->
  update config1 g target1 choice1 == update config2 g target2 choice2.

Lemma R2F_round : forall (r : robogram) (rda : rigid_da),
  forall config, round r (R2F_da rda) config == round r rda config.
Proof.
intros r rda config id. unfold round. cbn -[choose_update].
repeat destruct_match; try reflexivity; [].
apply update_only_location.
rewrite (@Rigid.rigid_update loc info _ Trigid); autoclass.
rewrite is_rigid_da_update.
- reflexivity.
- apply R2F_da_is_rigid.
Qed.

Lemma F2R_round : forall (r : robogram) (fda : flex_da), is_rigid_da fda ->
  forall config, round r (F2R_da fda) config == round r fda config.
Proof.
intros r fda Hrigid config id. unfold round. cbn -[choose_update].
repeat destruct_match; try reflexivity; [].
symmetry. apply update_only_location.
rewrite (@Rigid.rigid_update loc info _ Trigid); autoclass.
rewrite is_rigid_da_update.
- reflexivity.
- assumption.
Qed.

(** **  Equivalence between [execution]s  **)

(** A rigid demon can be turned into a flexible one (that satifties the [rigid] predicate). *)
Theorem R2F_preserves_eq : forall r config1 config2 (rd : rigid_demon),
  config1 == config2 -> execute r rd config1 == execute r (R2F_demon rd) config2.
Proof.
intro r. cofix next_exec. intros conf1 conf2 d Heq.
constructor; trivial; []. rewrite 2 execute_tail. simpl.
apply next_exec. rewrite R2F_round. now apply round_compat.
Qed.

Corollary R2F : forall r config (d : rigid_demon),
  execute r d config == execute r (R2F_demon d) config.
Proof. intros. now apply R2F_preserves_eq. Qed.

(** A flexible demon that satisfies the [rigid] predicate can be turned into a rigid one. *)
Theorem F2R_preserves_eq : forall r config1 config2 (d : flex_demon), is_rigid_demon d ->
  config1 == config2 -> execute r d config1 == execute r (F2R_demon d) config2.
Proof.
intro r. cofix next_exec. intros conf1 conf2 fd Hfd Heq.
constructor; trivial; []. rewrite 2 execute_tail. simpl.
destruct Hfd. apply next_exec; trivial; [].
rewrite F2R_round; trivial; []. now apply round_compat.
Qed.

Corollary Flex_Rigid : forall r config (d : flex_demon), is_rigid_demon d ->
  execute r d config == execute r (F2R_demon d) config.
Proof. intros. now apply F2R_preserves_eq. Qed.

End RigidFlexibleEquivalence.

Print Assumptions Flex_Rigid.