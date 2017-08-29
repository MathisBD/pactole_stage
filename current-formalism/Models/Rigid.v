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

Context {loc info : Type}.
Context `{IsLocation loc info}.
Context `{Names}.
Context {Spect : Spectrum loc info}.

(** Rigid demons are a special case of demons with the additional property that
    the updated location of the robot is the one chosen by the robogram. *)
Definition rigid_da da :=
  forall g pt state, get_location (update_state da g pt state) == pt.

Definition rigid_demon := Stream.forever (Stream.instant rigid_da).

End RigidFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
