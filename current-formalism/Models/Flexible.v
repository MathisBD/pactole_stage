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
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.


Typeclasses eauto := (bfs).


Section FlexibleFormalism.

Context {loc info : Type}.
Context `{IsLocation loc info}.
Context {RMS : RealMetricSpace loc}.
Context `{Names}.
Context {Spect : Spectrum loc info}.


(** Flexible demons are a special case of demons with the additional property that
    the updated location of the robot is not necessarily the one chosen by the robogram,
    but lies on the segment delimited by the current and target locations.
    To avoid Zenon-based paradoxes, we require the robot to move at least a given distance δ. *)

(** Flexible moves are parametrized by the minimum distance that robots must move when they are activated. *)
Class FlexibleMoves := delta : R.
Notation δ := delta.

Definition flexible_da `{FlexibleMoves} da :=
  forall config g tgt,
  let pt := get_location (config (Good g)) in
  let pt' := get_location (update_state da config g tgt) in
  (* either we reach the target *)
  pt' == tgt
  (* or [pt'] is between [pt] and [tgt] (equality case of the triangle inequality) *)
  \/ dist pt pt' + dist pt' tgt = dist pt tgt
  (* and the robot have moved a distance at least delta. *)
  /\ delta <= dist pt pt'.

Definition flexible_demon `{FlexibleMoves} := Stream.forever (Stream.instant flexible_da).

End FlexibleFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
