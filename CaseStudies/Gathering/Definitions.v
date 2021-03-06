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


Require Import Arith.Div2.
Require Import Lia.
Require Export SetoidDec.
Require Export Pactole.Util.Preliminary.
Require Export Pactole.Setting.
Require Export Pactole.Spaces.RealMetricSpace.
Require Export Pactole.Spaces.Similarity.
Require Export Pactole.Models.Similarity.
Close Scope R_scope.
Set Implicit Arguments.


Section GatheringDefinitions.

(** Everything is arbitrary, except that we assume that the space is a real metric space. *)
Context `{Observation}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}.

Context `{robot_choice}.
Context `{update_choice}.
Context `{inactive_choice}.
Context {UpdFun : update_function _ _ _}.
Context {InaFun : inactive_function _}.

Notation "!!" := (fun config => obs_from_config config origin).

(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : location) (config : configuration) := forall g, get_location (config (Good g)) == pt.

(** [Gather pt e] means that at all rounds of (infinite) execution [e],
    robots are gathered at the same position [pt]. *)
Definition Gather (pt: location) (e : execution) : Prop := Stream.forever (Stream.instant (gathered_at pt)) e.

(** [WillGather e] means that the (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition WillGather (e : execution) : Prop :=
  Stream.eventually (fun e => exists pt, Gather pt e) e.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)

Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config : configuration, WillGather (execute r d config).

(** Compatibility properties *)
Global Instance gathered_at_compat : Proper (equiv ==> equiv ==> iff) gathered_at.
Proof using .
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at.
setoid_rewrite Hconfig. setoid_rewrite Hpt. reflexivity.
Qed.

Global Instance Gather_compat : Proper (equiv ==> equiv ==> iff) Gather.
Proof using .
intros pt1 pt2 Hpt. apply Stream.forever_compat, Stream.instant_compat.
intros config1 config2 Hconfig. now rewrite Hpt, Hconfig.
Qed.

Global Instance WillGather_compat : Proper (equiv ==> iff) WillGather.
Proof using . apply Stream.eventually_compat. intros ? ? Hpt. now setoid_rewrite Hpt. Qed.

Global Instance FullSolGathering_compat : Proper (equiv ==> equiv ==> iff) FullSolGathering.
Proof using .
intros r1 r2 Hr d1 d2 Hd. unfold FullSolGathering.
setoid_rewrite Hr. setoid_rewrite Hd. reflexivity.
Qed.

Lemma gathered_at_dec : forall config pt, {gathered_at pt config} + {~gathered_at pt config}.
Proof using .
intros config pt.
destruct (List.forallb (fun g => if get_location (config (Good g)) =?= pt then true else false)
                       Gnames) eqn:Hall.
+ left. rewrite List.forallb_forall in Hall. intro g.
  specialize (Hall g (In_Gnames _)). revert Hall. destruct_match; tauto || discriminate.
+ right. rewrite <- Bool.negb_true_iff, existsb_forallb, List.existsb_exists in Hall.
  destruct Hall as [g [Hin Heq]].
  revert Heq. destruct_match; simpl; discriminate || intros _.
  intros Habs. specialize (Habs g). contradiction.
Qed.

End GatheringDefinitions.
