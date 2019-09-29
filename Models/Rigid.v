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

Typeclasses eauto := (bfs).
Section RigidFormalism.

Context {Tframe : Type}.
Context `{Spectrum}.
Context {Robot : robot_choice location}.
Context {Frame : frame_choice Tframe}.
Context `{update_choice}.
Context {Upd : update_function location _ _}.


(** Rigid moves are a special case of state updates where the updated location of the robot
    is the one chosen by the robogram. *)
Class RigidSetting := {
  rigid_update : forall config frame g target choice,
    get_location (update config g frame target choice) == target }.

End RigidFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
