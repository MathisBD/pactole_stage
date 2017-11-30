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


Section RigidFormalism.

Context {loc info T1 T2 : Type}.
Context `{IsLocation loc info}.
Context {N : Names}.
Context {Spect : Spectrum loc info}.
Context `{@frame_choice loc info T1 _ _ _ _ _}.
Context `{update_choice T2}.
Context {Update : @update_function loc info T2 _ _ _ _ _ _ _}.

Local Notation update := (@update loc info T2 _ _ _ _ _ _ _ Update).

(** Rigid moves are a special case of state updates where the updated location of the robot
    is the one chosen by the robogram. *)
Class RigidUpdate := {
  rigid_update : forall da config g target,
    get_location (update config g target (da.(choose_update) config g target)) == target }.

End RigidFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
