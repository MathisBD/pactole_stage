(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain               
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence       
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.Graph.
Require Import Pactole.Spaces.Isomorphism.


Section DGF.

Context `{State}.
Context `{Names}.
Instance Robot : robot_choice location := {robot_choice_Setoid := location_Setoid }.
Context `{update_choice}.
Context `{inactive_choice}.
Context (E : Type).
Context {G : Graph location E}.
Context `{@frame_choice _ (isomorphism G)}.
Context {Upd : update_function location (isomorphism G) _}.
Context `{@Spectrum _ _ _ _}.


(** The robogram should return only adjacent node values.
    We enforce this by making a check in the [update] function. *)
Class DiscreteGraphUpdate := {
  discrete_graph_update : forall (da : demonic_action) config g (target : location),
    find_edge (get_location (config (Good g))) target <> None ->
 (* if the robogram tries to move on an adjacent node *)
    get_location (update config g (da.(change_frame) config g)
                         target (da.(choose_update) config g target)) == target }.
 (* then the update let it go there *)

End DGF.
