(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals Lia Arith.Div2 Psatz SetoidDec.
Require Export Pactole.Setting.
Require Export Pactole.Spaces.Ring.
Require Export Pactole.Spaces.Isomorphism.
Require Export Pactole.Observations.MultisetObservation.


Close Scope Z_scope.
Set Implicit Arguments.
Typeclasses eauto := (bfs).


Section ExplorationDefs.

(** Setting definitions *)


(** Definition of the ring. *)
Context {RR : RingSpec}.
(* We do not care about threshold values, so we just take 1/2 everywhere. *)
Existing Instance localRing.
Notation ring_node := (finite_node ring_size).
(* NB: These instances will be replaced by the glob_* ones so they are local. *)

(* begin show *)
(** Number of good and Byzantine robots *)
Context {Robots : Names}.

(** Robots are on nodes *)
Global Instance Loc : Location := make_Location ring_node.

(** States of robots only contains their location. *)
Global Instance St : State location := OnlyLocation (fun _ => True).
Global Existing Instance proj_graph.

(** Robots observe the location of others robots with strong multiplicity. *)
Global Existing Instance multiset_observation.

(** Robots only decide in which direction they want to move. *)
Global Instance RC : robot_choice direction := { robot_choice_Setoid := direction_Setoid }.

(** Demon's frame choice: we move back the robot to the origin with a translation
                          and we can choose the orientation of the ring. *)
Global Instance FC : frame_choice (Z * bool) := {
  frame_choice_bijection :=
    fun nb => if snd nb then Ring.sym (fst nb) else Ring.trans (fst nb);
  frame_choice_Setoid := eq_setoid _ }.

Global Existing Instance NoChoice.
Global Existing Instance NoChoiceIna.
Global Existing Instance NoChoiceInaFun.


Global Instance UpdFun : update_function direction (Z * bool) unit := {
  update := fun config g _ dir _ => move_along (config (Good g)) dir;
  update_compat := ltac:(repeat intro; subst; now apply move_along_compat) }.
(* end show *)

(* Global Instance setting : GlobalDefinitions := {
  (* Number of good and Byzantine robots *)
  glob_Names := Robots;
  (* The space in which robots evolve *)
  glob_Loc := Loc;
  (* The state of robots (must contain at least the current location) *)
  glob_info := location;
  glob_State := OnlyLocation (fun _ => True);
  (* The observation: what robots can see from their surroundings *)
  glob_obs := multiset_observation;
  (* The output type of robograms: some information that we can use to get a target location *)
  glob_Trobot := direction;
  glob_robot_choice := RC;
  (* The frame decision made by the demon, used to build the frame change *)
  glob_Tframe := Z * bool;
  glob_frame_choice := FC;
  (* The influence of the demon on the state update of robots, when active *)
  glob_Tactive := unit;
  glob_update_choice := NoChoice;
  (* The influence of the demon on the state update of robots, when inactive *)
  glob_Tinactive := unit;
  glob_inactive_choice := NoChoiceIna;
  (* How a robots state is updated:
     - if active, using the result of the robogram and the decision from the demon
     - if inactive, using only the decision from the demon *)
  glob_update_function := UpdFun;
  glob_inactive_function := NoChoiceInaFun }. *)

(** ** Specification of exploration with stop *)

(** Any node will eventually be visited. *)
Definition is_visited (pt : location) (config : configuration) :=
  exists g, config (Good g) == pt.

Definition Will_be_visited (pt : location) (e : execution) : Prop :=
  Stream.eventually (Stream.instant (is_visited pt)) e.

(** Eventually, all robots stop moving. *)
Definition Stall (e : execution) := Stream.hd e == (Stream.hd (Stream.tl e)).

Definition Stopped (e : execution) : Prop :=
  Stream.forever Stall e.

Definition Will_stop (e : execution) : Prop :=
  Stream.eventually Stopped e.

(** [Exploration_with_stop r d config] means that executing [r] against demon [d] from
    configuration [config] indeed solves exploration with stop: after a finite time, every
    node of the space has been visited and all robots will stay at the same place forever. *)
Definition ExplorationWithStop (r : robogram) (d : demon) (config : configuration) :=
  (forall l, Will_be_visited l (execute r d config))
  /\ Will_stop (execute r d config).

(** [FullSolExplorationWithStop r d] means that the robogram [r] solves exploration with stop
    agains demon [d] regardless of the starting configuration.

    This is actually impossible when the number of robots is less than the size of the ring. *)
Definition FullSolExplorationWithStop (r : robogram) (d : demon) :=
  forall config, ExplorationWithStop r d config.

(** Acceptable starting configurations contain no tower,
    that is, all robots are at different locations. *)
Definition Valid_starting_config config : Prop :=
  Util.Preliminary.injective (@Logic.eq ident) (@equiv _ state_Setoid) config.
(*   forall pt : location, ((obs_from_config config (of_Z 0))[pt] <= 1)%nat. *)

Definition Explore_and_Stop (r : robogram) :=
  forall d config, Fair d -> Valid_starting_config config ->
  ExplorationWithStop r d config.

(** Compatibility properties *)
Global Instance is_visited_compat : Proper (equiv ==> equiv ==> iff) is_visited.
Proof using .
intros pt1 pt2 Hpt config1 config2 Hconfig.
split; intros [g Hv]; exists g.
- now rewrite <- Hconfig, Hv, Hpt.
- now rewrite Hconfig, Hv, Hpt.
Qed.

Global Instance Will_be_visited_compat : Proper (equiv ==> equiv ==> iff) Will_be_visited.
Proof using .
intros ? ? ?. now apply Stream.eventually_compat, Stream.instant_compat, is_visited_compat.
Qed.

Global Instance Stall_compat : Proper (equiv ==> iff) Stall.
Proof using .
intros e1 e2 He. split; intros Hs; unfold Stall in *;
(now rewrite <- He) || now rewrite He.
Qed.

Global Instance Stopped_compat : Proper (equiv ==> iff) Stopped.
Proof using .
intros e1 e2 He. split; revert e1 e2 He; coinduction rec.
- destruct H. now rewrite <- He.
- destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
- destruct H. now rewrite He.
- destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.

Global Instance Will_stop_compat : Proper (equiv ==> iff) Will_stop.
Proof using . apply Stream.eventually_compat, Stopped_compat. Qed.

Global Instance Valid_starting_config_compat : Proper (equiv ==> iff) Valid_starting_config.
Proof using .
intros ? ? Hconfig.
unfold Valid_starting_config, Util.Preliminary.injective.
now setoid_rewrite Hconfig.
Qed.

(** We can decide if a given configuration is a valid starting one. *)
Lemma Valid_starting_config_dec : forall config,
  {Valid_starting_config config} + {~ Valid_starting_config config}.
Proof using . intro config. unfold Valid_starting_config. apply config_injective_dec. Qed.

End ExplorationDefs.
