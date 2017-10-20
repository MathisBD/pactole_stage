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
Require Import Reals.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.


Typeclasses eauto := (bfs) 5.


(** Flexible demons are a special case of demons with the additional property that
    the updated location of the robot is not necessarily the one chosen by the robogram,
    but lies on the segment delimited by the current and target locations.
    To avoid Zenon-based paradoxes, we require the robot to move at least a given distance δ. *)
Section FlexibleFormalism.

Context {loc info T1 T2 : Type}.
Context `{IsLocation loc info}.
Context {RMS : RealMetricSpace loc}. (* only used for the equality case of the triangle inequality *)
Context `{Names}.
Context {Spect : Spectrum loc info}.
Context `{@first_demonic_choice loc info T1 _ _ _ _ _}.


Class FlexibleChoice `{second_demonic_choice T2} := {
  move_ratio : T2 -> R;
  move_ratio_bound : forall choice, 0 < move_ratio choice <= 1;
  move_ratio_compat :> Proper (@equiv T2 second_choice_Setoid ==> equiv) move_ratio }.

(** Flexible moves are parametrized by the minimum distance [delta] that robots must move when they are activated. *)
Class FlexibleUpdate `{FlexibleChoice} {Update : update_function T2} := {
  (** The minimum distance that robots should be allowed to move *)
  delta : R;
  (** [move_ratio] is ratio between the achieved and the planned move distances. *)
  ratio_spec : forall da config g target,
    let pt := get_location (config (Good g)) in
    let pt' := get_location (update config target (da.(choose_update) config g target)) in
    dist pt pt' = move_ratio (da.(choose_update) config g target) * (dist pt target);
  (** Moves are flexible: they do not necessarily reach their target but stay on a line *)
  flexible_update : forall da config g target,
    let pt := get_location (config (Good g)) in
    let pt' := get_location (update config target (da.(choose_update) config g target)) in
    (* either we reach the target *)
    pt' == target
    (* or [pt'] is between [pt] and [tgt] (equality case of the triangle inequality) *)
    \/ dist pt pt' + dist pt' target = dist pt target
    (* and the robot has moved a distance at least delta. *)
    /\ delta <= dist pt pt' }.

End FlexibleFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
