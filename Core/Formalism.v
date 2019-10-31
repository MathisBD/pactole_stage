(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.    *)
(**************************************************************************)

Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Util.Ratio.
Require Pactole.Util.Stream.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Core.Configurations.
Require Import Pactole.Observations.Definition.


Typeclasses eauto := 5.
Remove Hints eq_setoid.


Section Formalism.
(* We use explicit names instead of simply `{Observation}
   in order to get meaningful names for implicit arguments. *)
Context {info : Type}.
Context {Loc : Location}.
Context {St : State info}.
Context `{Names}.
Context {Obs : Observation}.
Variables Trobot Tframe Tactive Tinactive : Type.

(** **  Robograms and Executions  **)

(** Executions are simply streams of configurations. *)
Definition execution := Stream.t configuration.

(** Good robots have a common program, which we call a [robogram].
    It returns some piece of information (e.g. target location) which must form a setoid. *)
Class robot_choice := { robot_choice_Setoid :> Setoid Trobot }.

Record robogram `{robot_choice} := {
  pgm :> observation -> Trobot;
  pgm_compat :> Proper (equiv ==> equiv) pgm}.

Global Instance robogram_Setoid `{robot_choice} : Setoid robogram := {|
  equiv := fun r1 r2 => forall s, pgm r1 s == pgm r2 s |}.
Proof. split.
+ intros ? ?. reflexivity.
+ intros ? ? ? ?. now symmetry.
+ intros ? ? ? ? ? ?. etransitivity; eauto.
Defined.

Global Instance pgm_full_compat `{robot_choice} : Proper (equiv ==> equiv ==> equiv) pgm.
Proof. intros r1 r2 Hr s1 s2 Hs. rewrite (Hr s1). now apply pgm_compat. Qed.

(** ** Demonic schedulers *)

(** A [demonic_action] performs four things:
    - it selects which robots are activated,
    - it moves all activated byzantine robots as it wishes,
    - in the look phase, it sets the referential of all activated good robots,
    - in the move phase, it makes some choices about how the robots' states should be updated.
    
    Therefore, it can make choices at two places: while computing the local frame of reference for a robot
    and while updating robot states.  These choice points will be represented explicitely as demon choices. *)

(** A [frame_choice] represents the choices made by the demon to compute the observation.
    It must at least contain a bijection to compute the change of frame of reference.  *)
Class frame_choice := {
  frame_choice_bijection :> Tframe -> bijection location;
  frame_choice_Setoid :> Setoid Tframe;
  frame_choice_bijection_compat :> Proper (equiv ==> equiv) frame_choice_bijection }.
Global Existing Instance frame_choice_bijection_compat.

(** An [update_choice] represents the choices the demon makes after a robot decides where it wants to go. *)
Class update_choice := {
  update_choice_Setoid :> Setoid Tactive;
  update_choice_EqDec :> EqDec update_choice_Setoid }.

(** An [inactive_choice] represents the choices the demon makes when a robot is not activated. *)
Class inactive_choice := {
  inactive_choice_Setoid :> Setoid Tinactive;
  inactive_choice_EqDec :> EqDec inactive_choice_Setoid }.

(** These choices are then used by update functions that depend on the model. *)
(* RMK: we cannot combine them toghether otherwise we get spurious dependencies on the unused parameters. *)
Class update_function `{robot_choice} `{frame_choice} `{update_choice} := {
  update :> configuration -> G -> Tframe -> Trobot -> Tactive -> info;
  update_compat :> Proper (equiv ==> Logic.eq ==> equiv ==> equiv ==> equiv ==> equiv) update }.

Class inactive_function  `{inactive_choice} := {
  inactive :> configuration -> ident -> Tinactive -> info;
  inactive_compat :> Proper (equiv ==> Logic.eq ==> equiv ==> equiv) inactive }.

Context `{robot_choice}.
Context `{frame_choice}.
Context `{update_choice}.
Context `{inactive_choice}.
Context `{@update_function _ _ _}.
Context `{@inactive_function _}.


(* NB: The byzantine robots are not always activated
       because fairness depends on all robots, not only good ones. *)
(* RMK: /!\ activate does not take the configuration as argument because we cannot define fairness
            in that case: fairness properties are about a single execution, not a tree of them. *)
Record demonic_action := {
  (** Select which robots are activated *)
  activate : ident -> bool;
  (** Update the state of (activated) byzantine robots *)
  relocate_byz : configuration -> B -> info;
  (** Local referential for (activated) good robots in the compute phase *)
  change_frame : configuration -> G -> Tframe;
  (** Update the state of (activated) good robots in the move phase  *)
  choose_update : configuration -> G -> Trobot -> Tactive;
  (** Update the state of inactive robots *)
  choose_inactive : configuration -> ident -> Tinactive;
  (** The change of frame and its inverse must satisfy the condition to be lifted to states *)
  precondition_satisfied : forall config g, precondition (frame_choice_bijection (change_frame config g));
  precondition_satisfied_inv : forall config g,
    precondition ((frame_choice_bijection (change_frame config g)) ⁻¹);
  (** Compatibility properties *)
  activate_compat : Proper (Logic.eq ==> equiv) activate;
  relocate_byz_compat : Proper (equiv ==> Logic.eq ==> equiv) relocate_byz;
  change_frame_compat : Proper (equiv ==> Logic.eq ==> equiv) change_frame;
  choose_update_compat : Proper (equiv ==> Logic.eq ==> equiv ==> equiv) choose_update;
  choose_inactive_compat : Proper (equiv ==> equiv ==> equiv) choose_inactive }.


(** Equivalence relation over [demonic_action]. *)
Global Instance da_Setoid : Setoid demonic_action := {|
  equiv := fun (da1 da2 : demonic_action) =>
           (forall id, da1.(activate) id == da2.(activate) id)
        /\ (forall config b, da1.(relocate_byz) config b == da2.(relocate_byz) config b)
        /\ (forall config g, da1.(change_frame) config g == da2.(change_frame) config g)
        /\ (forall config g pt, da1.(choose_update) config g pt == da2.(choose_update) config g pt)
        /\ (forall config id, da1.(choose_inactive) config id == da2.(choose_inactive) config id) |}.
Proof. split.
+ repeat split; intuition.
+ intros da1 da2 [? [? [? [? ?]]]]. repeat split; intros; symmetry; auto.
+ intros da1 da2 da3 [? [? [? [? ?]]]] [? [? [? [? ?]]]]. repeat split; intros; etransitivity; eauto.
Defined.

Global Instance activate_da_compat : Proper (equiv ==> Logic.eq ==> equiv) activate.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply activate_compat. Qed.

Global Instance relocate_byz_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) relocate_byz.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply relocate_byz_compat. Qed.

Global Instance change_frame_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) change_frame.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply change_frame_compat. Qed.

Global Instance choose_update_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv ==> equiv) choose_update.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply choose_update_compat. Qed.

Global Instance choose_inactive_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) choose_inactive.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply choose_inactive_compat. Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition active da := List.filter (activate da) names.

(* TODO: rename into inactive? *)
Definition idle da := List.filter (fun id => negb (activate da id)) names.

Global Instance active_compat : Proper (equiv ==> Logic.eq) active.
Proof.
intros da1 da2 Hda.
unfold active. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 id) eqn:Hactivate1, (activate da2 id) eqn:Hactivate2.
  - f_equal. apply IHl.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - apply IHl.
Qed.

Global Instance idle_compat : Proper (equiv ==> Logic.eq) idle.
Proof.
intros da1 da2 Hda.
unfold idle. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 id) eqn:Hactivate1, (activate da2 id) eqn:Hactivate2.
  - apply IHl.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - simpl. f_equal. apply IHl.
Qed.

Lemma idle_spec : forall da id, List.In id (idle da) <-> activate da id = false.
Proof.
intros da id. unfold idle. rewrite List.filter_In.
destruct (activate da id); intuition; try discriminate; [].
apply In_names.
Qed.

Lemma active_spec : forall da id, List.In id (active da) <-> activate da id = true.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (activate da id); intuition; try discriminate; [].
apply In_names.
Qed.

(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

(** **  One step executions  **)

(** [round r da config] returns the new configuration of robots (that is, a function
    giving the position of each robot) from the previous one [config] by applying
    the robogram [r] on each observation seen by each robot. [da.(relocate_byz)]
    is used for byzantine robots.
    
    This setting is general enough to accomodate all models we have considered so far. *)
Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (* for a given robot, we compute the new configuration *)
  fun id =>
    let state := config id in
    if da.(activate) id                       (* first see whether the robot is activated *)
    then
      match id with
        | Byz b => da.(relocate_byz) config b (* byzantine robots are relocated by the demon *)
        | Good g =>
          (* change the frame of reference *)
          let frame_choice := da.(change_frame) config g in
          let new_frame := frame_choice_bijection frame_choice in
          let local_config := map_config (lift (existT precondition new_frame
                                                       (precondition_satisfied da config g)))
                                         config in
          let local_state := local_config (Good g) in
          (* compute the observation *)
          let obs := obs_from_config local_config local_state in
          (* apply r on the observation *)
          let local_robot_decision := r obs in
          (* the demon chooses how to perform the state update *)
          let choice := da.(choose_update) local_config g local_robot_decision in
          (* the actual update of the robot state is performed by the update function *)
          let new_local_state := update local_config g frame_choice local_robot_decision choice in
          (* return to the global frame of reference *)
          lift (existT precondition (new_frame ⁻¹) (precondition_satisfied_inv da config g)) new_local_state
        end
    else inactive config id (da.(choose_inactive) config id).

Global Instance round_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda config1 config2 Hconfig id.
unfold round. rewrite Hda. destruct_match.
* (* active robot *)
  destruct id as [g | b].
  + (* good robot *)
    assert (Heq : map_config (lift (existT precondition (frame_choice_bijection (change_frame da1 config1 g))
                                      (precondition_satisfied da1 config1 g))) config1
               == map_config (lift (existT precondition (frame_choice_bijection (change_frame da2 config2 g))
                                      (precondition_satisfied da2 config2 g))) config2).
    { f_equiv; trivial; []. apply lift_compat. intros x y Hxy. simpl. f_equiv; trivial; [].
      apply frame_choice_bijection_compat. now f_equiv. }
    apply lift_compat, update_compat.
    - intros x y Hxy. simpl. f_equiv; trivial; []. apply frame_choice_bijection_compat. now f_equiv.
    - apply Heq.
    - reflexivity.
    - now f_equiv.
    - repeat (f_equiv; trivial).
    - repeat (f_equiv; trivial).
  + (* byzantine robot *)
    now f_equiv.
* (* inactive robot *)
  now apply inactive_compat, choose_inactive_da_compat.
Qed.


(** A third subset of robots: moving ones. *)
Definition moving r da config :=
  List.filter
    (fun id => if round r da config id =?= config id then false else true)
    names.

Global Instance moving_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) moving.
Proof.
intros r1 r2 Hr da1 da2 Hda c1 c2 Hc. unfold moving.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (round r1 da1 c1 id =?= c1 id) as [Heq1 | Heq1],
           (round r2 da2 c2 id =?= c2 id) as [Heq2 | Heq2].
  + apply IHl.
  + elim Heq2. transitivity (round r1 da1 c1 id).
    - symmetry. now apply round_compat.
    - rewrite Heq1. apply Hc.
  + elim Heq1. transitivity (round r2 da2 c2 id).
    - now apply round_compat.
    - rewrite Heq2. symmetry. apply Hc.
  + f_equal. apply IHl.
Qed.

Lemma moving_spec : forall r da config id,
  List.In id (moving r da config) <-> round r da config id =/= config id.
Proof.
intros r da config id. unfold moving. rewrite List.filter_In.
split; intro Hin.
+ destruct Hin as [_ Hin].
  destruct (round r da config id =?= config id) as [_ | Hneq]; intuition.
+ split.
  - apply In_names.
  - destruct (round r da config id =?= config id) as [Heq | _]; intuition.
Qed.

Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof.
intros r da config Hmove id.
destruct (round r da config id =?= config id) as [Heq | Heq]; trivial; [].
apply <- moving_spec in Heq. rewrite Hmove in Heq. inversion Heq.
Qed.

(** [execute r d config] returns an (infinite) execution from an initial global
    configuration [config], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram) : demon -> configuration -> execution :=
  cofix execute d config :=
  Stream.cons config (execute (Stream.tl d) (round r (Stream.hd d) config)).

(** Decomposition lemmas for [execute]. *)
Lemma execute_hd : forall (r : robogram) (d : demon) (config : configuration),
  Stream.hd (execute r d config) = config.
Proof. reflexivity. Qed.

Lemma execute_tail : forall (r : robogram) (d : demon) (config : configuration),
  Stream.tl (execute r d config) = execute r (Stream.tl d) (round r (Stream.hd d) config).
Proof. reflexivity. Qed.

Global Instance execute_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) execute.
Proof.
intros r1 r2 Hr. coinduction proof.
- simpl. assumption.
- now f_equiv.
- apply round_compat; trivial. now f_equiv.
Qed.

(** **  Execution models  **)

(** ***  Semi-synchronous (SSYNC) model  **)

(* FIXME?: this must hold for all configurations whereas only the current one may be useful *)
(* NB: The precondition is necessary to have the implication FSYNC -> SSYNC.
       We could impose that [Tinactive = unit] but this might create problems when comparing settings. *)
Definition SSYNC_da da := forall id, da.(activate) id = false ->
  forall config, inactive config id (da.(choose_inactive) config id) == config id.

Definition SSYNC d := Stream.forever (Stream.instant SSYNC_da) d.

Global Instance SSYNC_da_compat : Proper (equiv ==> iff) SSYNC_da.
Proof. intros da1 da2 Hda. unfold SSYNC_da. now setoid_rewrite Hda. Qed.

Global Instance SSYNC_compat : Proper (equiv ==> iff) SSYNC.
Proof. apply Stream.forever_compat, Stream.instant_compat, SSYNC_da_compat. Qed.

(** All moving robots are active.
    This is only true for the SSYNC (and FSYNC) model: in the ASYNC one,
    robots can keep moving while others are activated. *)
Lemma moving_active : forall da, SSYNC_da da ->
  forall r config, List.incl (moving r da config) (active da).
Proof.
intros da HSSYNC r config id. rewrite moving_spec, active_spec.
unfold round. destruct_match_eq Hcase; intuition.
Qed.

(** If no robot is active, then the configuration does not change. *)
Lemma no_active_same_config : forall da, SSYNC_da da ->
  forall r config, active da = List.nil -> round r da config == config.
Proof.
intros da HSSYNC r config Hactive.
assert (Hfalse : forall id, activate da id = false).
{ intro id. destruct (activate da id) eqn:Heq; trivial; []. exfalso.
  rewrite <- active_spec, Hactive in Heq. intuition. }
intro id. unfold round. rewrite (Hfalse id). intuition.
Qed.

Lemma SSYNC_round_simplify : forall r da config, SSYNC_da da ->
  round r da config 
  == fun id =>
    let state := config id in
    if da.(activate) id
    then
      match id with
        | Byz b => da.(relocate_byz) config b
        | Good g =>
          let frame_choice := da.(change_frame) config g in
          let new_frame := frame_choice_bijection frame_choice in
          let local_config := map_config (lift (existT precondition new_frame
                                                       (precondition_satisfied da config g)))
                                         config in
          let local_state := local_config (Good g) in
          let obs := obs_from_config local_config local_state in
          let local_robot_decision := r obs in
          let choice := da.(choose_update) local_config g local_robot_decision in
          let new_local_state := update local_config g frame_choice local_robot_decision choice in
          lift (existT precondition (new_frame ⁻¹) (precondition_satisfied_inv da config g)) new_local_state
        end
    else state.
Proof. unfold round. repeat intro. destruct_match_eq Hcase; auto. Qed.

(** ***  Fully-synchronous (FSYNC) model  **)

(** A fully synchronous demon is a particular case of fair demon: all good robots are activated
    at each round. In our setting this means that the [activate] function is always true. *)

Definition FSYNC_da da := forall id, da.(activate) id = true.

Definition FSYNC d := Stream.forever (Stream.instant FSYNC_da) d.

Global Instance FSYNC_da_compat : Proper (equiv ==> iff) FSYNC_da.
Proof. intros da1 da2 Hda. unfold FSYNC_da. now setoid_rewrite Hda. Qed.

Global Instance FSYNC_compat : Proper (equiv ==> iff) FSYNC.
Proof. apply Stream.forever_compat, Stream.instant_compat, FSYNC_da_compat. Qed.

Lemma FSYNC_SSYNC_da : forall da, FSYNC_da da -> SSYNC_da da.
Proof. unfold FSYNC_da, SSYNC_da. intuition. congruence. Qed.

Theorem FSYNC_SSYNC : forall d, FSYNC d -> SSYNC d.
Proof. apply Stream.forever_impl_compat, Stream.instant_impl_compat, FSYNC_SSYNC_da. Qed.

Lemma FSYNC_round_simplify : forall r da config, FSYNC_da da ->
  round r da config 
  == fun id =>
    let state := config id in
    match id with
      | Byz b => da.(relocate_byz) config b
      | Good g =>
        let frame_choice := da.(change_frame) config g in
        let new_frame := frame_choice_bijection frame_choice in
        let local_config := map_config (lift (existT precondition new_frame
                                                     (precondition_satisfied da config g)))
                                       config in
        let local_state := local_config (Good g) in
        let obs := obs_from_config local_config local_state in
        let local_robot_decision := r obs in
        let choice := da.(choose_update) local_config g local_robot_decision in
        let new_local_state := update local_config g frame_choice local_robot_decision choice in
        lift (existT precondition (new_frame ⁻¹) (precondition_satisfied_inv da config g)) new_local_state
      end.
Proof.
intros * HFSYNC. rewrite SSYNC_round_simplify; auto using FSYNC_SSYNC_da; [].
repeat intro. now rewrite HFSYNC.
Qed.

(** **  Fairness  **)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne id (d : demon) : Prop :=
  | NowFair : activate (Stream.hd d) id == true -> LocallyFairForOne id d
  | LaterFair : activate (Stream.hd d) id = false ->
                LocallyFairForOne id (Stream.tl d) -> LocallyFairForOne id d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ id, LocallyFairForOne id d).

(** [Between id id' d] means that [id] will be activated before at most [k]
    steps of [id'] in demon [d]. *)
Inductive Between id id' (d : demon) : nat -> Prop :=
| kReset : forall k, activate (Stream.hd d) id = true -> Between id id' d k
| kReduce : forall k, activate (Stream.hd d) id = false ->
                      activate (Stream.hd d) id' = true ->
                      Between id id' (Stream.tl d) k -> Between id id' d (S k)
| kStall : forall k, activate (Stream.hd d) id = false ->
                     activate (Stream.hd d) id' = false ->
                     Between id id' (Stream.tl d) k -> Between id id' d k.

(** k-fairnes: Every robot is activated within at most k activation of any other robot. *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall id id', Between id id' d k).

(** Compatibility properties *)
Local Lemma LocallyFairForOne_compat_aux : forall id d1 d2,
  d1 == d2 -> LocallyFairForOne id d1 -> LocallyFairForOne id d2.
Proof.
intros id da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda;
constructor; solve [now rewrite <- Hda | apply IHHfair; now f_equiv].
Qed.

Global Instance LocallyFairForOne_compat : Proper (Logic.eq ==> equiv ==> iff) LocallyFairForOne.
Proof.
intros ? ? ? ? ? Heq. subst. split; intro.
- eapply LocallyFairForOne_compat_aux; eauto.
- symmetry in Heq. eapply LocallyFairForOne_compat_aux; eauto.
Qed.

Global Instance Fair_compat : Proper (equiv ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Local Lemma Between_compat_aux : forall id id' k d1 d2, d1 == d2 -> Between id id' d1 k -> Between id id' d2 k.
Proof.
intros id id' k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq;
constructor; solve [now rewrite <- Heq | apply IHbet; now f_equiv].
Qed.

Global Instance Between_compat : Proper (Logic.eq ==> Logic.eq ==> equiv ==> Logic.eq ==> iff) Between.
Proof.
intros ? ? ? ? ? ? ? ? Heq ? ? ?. subst. split; intro.
- now eapply Between_compat_aux; eauto.
- symmetry in Heq. now eapply Between_compat_aux; eauto.
Qed.

Global Instance kFair_compat : Proper (Logic.eq ==> equiv ==> iff) kFair.
Proof. intros k ? ?. subst. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

(** A robot is never activated before itself with a fair demon!
    The fairness hypothesis is necessary, otherwise the robot may never be activated. *)
Lemma Between_same :
  forall id (d : demon) k, LocallyFairForOne id d -> Between id id d k.
Proof. intros id d k Hd. induction Hd; now econstructor; eauto. Qed.

(** A k-fair demon is fair. *)
Lemma Between_LocallyFair : forall id (d : demon) id' k,
  Between id id' d k -> LocallyFairForOne id d.
Proof. intros * Hg. induction Hg; now constructor; trivial; firstorder. Qed.

Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros ? ? id. eauto using (@Between_LocallyFair id _ id). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mono : forall id id' (d : demon) k,
  Between id id' d k -> forall k', (k <= k')%nat -> Between id id' d k'.
Proof.
intros id id' d k Hd. induction Hd; intros k' Hk; auto using Between; [].
destruct k'.
- now inversion Hk.
- constructor; assumption || now (apply IHHd; auto with arith).
Qed.

(** [kFair k d] is monotonic on [k]. *)
Theorem kFair_mono : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; match goal with H : kFair _ _ |- _ => destruct H end.
- intros. now apply Between_mono with k.
- now apply (fair k).
Qed.

(** A synchronous demon is fair *)
Lemma FSYNC_implies_0Fair: ∀ d, FSYNC d → kFair 0 d.
Proof. apply Stream.forever_impl_compat. intros s Hs id id'. constructor. apply Hs. Qed.

Corollary FSYNC_implies_fair: ∀ d, FSYNC d → Fair d.
Proof. intros. now eapply kFair_Fair, FSYNC_implies_0Fair. Qed.

(** If a demon is 0-fair, then the activation states of all robots are the same:
    either all are activated, or none is. *)
Theorem Fair0 : forall d, kFair 0 d ->
  forall id id', (Stream.hd d).(activate) id = (Stream.hd d).(activate) id'.
Proof.
intros d Hd id id'. destruct Hd as [Hd _].
assert (Hg := Hd id id'). assert (Hh := Hd id' id).
inv Hg; inv Hh;
repeat match goal with
  | H : forall c : configuration, _ |- _ => specialize (H config)
  | H : _ /\ _ |- _ => destruct H
  | |- _ => congruence
end.
Qed.

(** [FirstMove r d config] gives the number of rounds before one robot moves. *)
Inductive FirstMove r (d : demon) (config : configuration) : Prop :=
  | MoveNow : moving r (Stream.hd d) config <> nil -> FirstMove r d config
  | MoveLater : moving r (Stream.hd d) config = nil ->
                FirstMove r (Stream.tl d) (round r (Stream.hd d) config) -> FirstMove r d config.

Global Instance FirstMove_compat : Proper (equiv ==> equiv ==> equiv ==> iff) FirstMove.
Proof.
intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst.
* revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc.
  + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc.
  + apply MoveLater.
    - now rewrite <- Hr, <- Hd, <- Hc.
    - destruct Hd. now apply IHHfirst, round_compat.
* revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc.
  + apply MoveNow. now rewrite Hr, Hd, Hc.
  + apply MoveLater.
    - now rewrite Hr, Hd, Hc.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat; f_equiv.
Qed.

End Formalism.

Arguments robogram {info} {_} {_} {_} {_} {Trobot} {_}.
Arguments Build_robogram {info} {_} {_} {_} {_} {Trobot} {_} pgm {_}.
Arguments update_choice_Setoid {_} {_}.
Arguments update_choice_EqDec {_} {_}.
Arguments update_function {info} {_} {_} {_} Trobot Tframe Tactive {_} {_} {_}.
Arguments inactive_function {info} {_} {_} {_} Tinactive {_}.
Arguments update {info} {_} {_} {_} {Trobot} {Tframe} {Tactive} {_} {_} {_} {_}.
Arguments update_compat {info} {_} {_} {_} {Trobot} {Tframe} {Tactive} {_} {_} {_} {_}.
Arguments inactive {info} {_} {_} {_} {Tinactive} {_} {_}.
Arguments inactive_compat {info} {_} {_} {_} {Tinactive} {_} {_}.
Arguments demonic_action {info} {_} {_} {_} {Trobot} {Tframe} {Tactive} {Tinactive} {_} {_} {_} {_}.
Arguments demon {info} {_} {_} {_} {Trobot} {Tframe} {Tactive} {Tinactive} {_} {_} {_} {_}.


Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.

Section ChoiceExample.
(** **  Most Common Examples of Demon Choices  **)

Context `{State}.
Context {VS : RealVectorSpace location}.

(** An exemple of frame choice: just a bijection. *)
Definition FrameChoiceBijection : frame_choice (bijection location) := {|
  frame_choice_bijection := Datatypes.id;
  frame_choice_Setoid := @bij_Setoid location _;
  frame_choice_bijection_compat := fun _ _ Heq => Heq |}.

(** Similarities as a frame choice, only make sense inside real metric spaces. *)
Definition FirstChoiceSimilarity {RMS : RealMetricSpace location}
  : frame_choice (similarity location) := {|
  frame_choice_bijection := @sim_f location _ _ _ _;
  frame_choice_Setoid := similarity_Setoid;
  frame_choice_bijection_compat := f_compat |}.


(** An exemple of update choice: no choice at all. *)
Definition NoChoice : update_choice unit := {|
  update_choice_Setoid := _;
  update_choice_EqDec := _ |}.

(** Combining two update choices into a choice over a pair. *)
Definition MergeUpdateChoices A B `{update_choice A} `{update_choice B} : update_choice (A * B) := {|
  update_choice_Setoid := _;
  update_choice_EqDec := _ |}.

(** Idem for inactive choice. *)
Instance NoChoiceIna : inactive_choice unit := {|
  inactive_choice_Setoid := _;
  inactive_choice_EqDec := _ |}.

Definition MergeInactiveChoices A B `{inactive_choice A} `{inactive_choice B} : inactive_choice (A * B) := {|
  inactive_choice_Setoid := _;
  inactive_choice_EqDec := _ |}.

Instance NoChoiceInaFun `{Names} : inactive_function unit := {|
  inactive := fun config g _ => config g;
  inactive_compat := ltac:(intros ? ? Heq ? ? ? ? ? ?; subst; apply Heq) |}.

End ChoiceExample.
