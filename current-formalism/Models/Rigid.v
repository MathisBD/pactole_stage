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


Section RigidFormalism.

Context `{Spectrum}.
Context {T1 T2 : Type}.
Context `{@frame_choice _ T1}.
Context `{update_choice T2}.
Context {Update : update_function T2}.

(** Rigid moves are a special case of state updates where the updated location of the robot
    is the one chosen by the robogram. *)
Class RigidUpdate := {
  rigid_update : forall da config g trajectory,
    get_location (update config g trajectory (da.(choose_update) config g trajectory)) == trajectory ratio_1 }.

End RigidFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
