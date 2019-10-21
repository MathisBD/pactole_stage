(**************************************************************************)
(*  Mechanised Framework for Local Interactions & Distributed Algorithms  *)
(*  T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        *)
(*  PACTOLE project                                                       *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence.     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(** Mechanised Framework for Local Interactions & Distributed Algorithms    
                                                                            
    T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                          
                                                                            
    PACTOLE project                                                         
                                                                            
    This file is distributed under the terms of the CeCILL-C licence.       
                                                                          *)
(**************************************************************************)

Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.
Require Import Pactole.Models.Similarity.

Typeclasses eauto := (bfs).


(** Flexible demons are a special case of demons with the additional property that
    the updated location of the robot is not necessarily the one chosen by the robogram,
    but lies on the segment delimited by the current and target locations.
    To avoid Zenon-based paradoxes, we require the robot to move at least a given distance δ. *)
Section FlexibleFormalism.

Context `{Observation}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Variable Tactive : Type.
Context {Robot : robot_choice (path location)}.
(* Context {Frame : frame_choice Tframe}. *)
(* we lose the generality because the <= test must have a zoom *)
Instance Frame : frame_choice (similarity location) := FrameChoiceSimilarity.

Class FlexibleChoice `{update_choice Tactive} := {
  move_ratio : Tactive -> ratio;
  move_ratio_compat :> Proper (@equiv Tactive update_choice_Setoid ==> @equiv _ (sig_Setoid _)) move_ratio }.

(** Flexible moves are parametrized by a minimum distance [delta] that robots must move when they are activated. *)
Class FlexibleSetting `{FlexibleChoice}
                       {Update : update_function (path location) (similarity location) Tactive}
                       (delta : R) := {
  (** [move_ratio] is the ratio between the achieved and the planned move distances. *)
  ratio_spec : forall (config : configuration) g sim (trajectory : path location) choice,
    let pt := get_location (config (Good g)) in
    let pt' := get_location (update config g sim trajectory choice) in
    (* either we reach the target *)
    pt' == trajectory ratio_1
    (* or we only move part of the way but the robot has moved a distance at least [delta]. *)
    \/ pt' == trajectory (move_ratio choice)
       /\ (zoom sim) * delta <= dist pt pt' }.

(** If the robot is not trying to move, then it does not, no matter what the demon chooses. *)
Lemma update_no_move `{FlexibleSetting} : forall config g sim pt choice,
  get_location (update config g sim (straight_path pt pt) choice) == pt.
Proof.
intros config g sim pt choice.
destruct (ratio_spec config g sim (straight_path pt pt) choice) as [Heq | [Heq Hle]];
rewrite Heq; simpl; now rewrite add_opp, mul_origin, add_origin.
Qed.

End FlexibleFormalism.

Section OnlyFlexibleSetting.

Context `{Location}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Context `{Names}.
Instance Robot : robot_choice (path location) := { robot_choice_Setoid := path_Setoid location }.

Instance St : State location := OnlyLocation (fun _ => True).

(** Specialized definition where the only choice made by the demon is the movement ratio. *)
Instance OnlyFlexible : update_choice ratio := {|
  update_choice_Setoid := ratio_Setoid;
  update_choice_EqDec := _ |}.

Global Instance OnlyFlexibleChoice : @FlexibleChoice _ OnlyFlexible := {| move_ratio := Datatypes.id |}.

Instance FlexibleUpdate (delta : R) : update_function (path location) (similarity location) ratio := {|
  update := fun config g sim (traj : path location) ρ =>
              if Rle_bool ((zoom sim) * delta) (dist (get_location (config (Good g))) (get_location (traj ρ)))
              then traj ρ else traj ratio_1 |}.
Proof.
intros config1 config2 Hconfig gg g ? sim1 sim2 Hsim traj1 traj2 Htraj ρ1 ρ2 Hρ. subst gg.
assert (Heq : get_location (traj1 ρ1) == get_location (traj2 ρ2)).
{ apply get_location_compat. now f_equiv. }
destruct_match_eq Hle; destruct_match_eq Hle'; rewrite Heq, ?Hsim in *;
solve [ reflexivity
      | now f_equiv
      | rewrite Hconfig, Htraj, Hρ in *; now rewrite Hle in Hle' ].
Unshelve. all:autoclass.
Defined.

Global Instance FlexibleChoiceFlexibleUpdate delta : FlexibleSetting (Update := FlexibleUpdate delta) delta.
Proof. split.
intros config g traj choice pt pt'.
simpl update in *. unfold pt'. destruct_match_eq Hle.
- rewrite Rle_bool_true_iff in Hle. now right.
- now left.
Qed.

End OnlyFlexibleSetting.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
