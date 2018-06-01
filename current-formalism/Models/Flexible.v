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


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.


(** Flexible demons are a special case of demons with the additional property that
    the updated location of the robot is not necessarily the one chosen by the robogram,
    but lies on the segment delimited by the current and target locations.
    To avoid Zenon-based paradoxes, we require the robot to move at least a given distance δ. *)
Section FlexibleFormalism.

Context `{Spectrum}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Variable T1 T2 : Type.
Context {Frame : frame_choice T1}.

Class FlexibleChoice `{update_choice T2} := {
  move_ratio : T2 -> ratio;
  move_ratio_compat :> Proper (@equiv T2 update_choice_Setoid ==> @equiv _ sig_Setoid) move_ratio }.

(** Flexible moves are parametrized by the minimum distance [delta] that robots must move when they are activated. *)
Class FlexibleUpdate `{FlexibleChoice} {Update : update_function T2} (delta : R) := {
  (** [move_ratio] is the ratio between the achieved and the planned move distances. *)
  ratio_spec : forall config g trajectory choice,
    let pt := get_location (config (Good g)) in
    let pt' := get_location (update config g trajectory choice) in
    (* either we reach the target *)
    pt' == trajectory ratio_1
    (* or we only move part of the way but the robot has moved a distance at least [delta]. *)
    \/ pt' == trajectory (move_ratio choice)
       /\ delta <= dist pt pt' }.

End FlexibleFormalism.

(** If the robot is not trying to move, then it does not, no metter what the demon chooses. *)
Lemma update_no_move `{FlexibleUpdate} : forall (config : configuration) (g : G) (pt : location) (choice : T2),
  get_location (update config g (straight_path pt pt) choice) == pt.
Proof.
intros config g pt choice.
destruct (ratio_spec config g (straight_path pt pt) choice) as [Heq | [Heq Hle]];
rewrite Heq; simpl; now rewrite add_opp, mul_origin, add_origin.
Qed.

(** Specialized definition where the only choice made by the demon is the movement ratio. *)
Definition OnlyFlexible : update_choice ratio := {|
  update_choice_Setoid := _;
  update_choice_EqDec := _ |}.

Instance OnlyFlexibleChoice : @FlexibleChoice _ OnlyFlexible := {| move_ratio := Datatypes.id |}.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
