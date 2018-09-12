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

Context `{update_functions}.
Context (E : Type).
Context {G : Graph location E}.
Context `{@frame_choice _ (isomorphism G)}.
Context `{@Spectrum _ _ _ _}.


Notation "s ⁻¹" := (Isomorphism.inverse s) (at level 99).

(** The robogram should return only adjacent node values.
    We enforce this by making a check in the [update] function. *)
Class DiscreteGraphUpdate := {
  discrete_graph_update : forall da config g (target : path location),
    find_edge (get_location (config (Good g))) (target ratio_1) <> None ->
 (* if the robogram tries to move on an adjacent node *)
    get_location (update config g target (da.(choose_update) config g target)) == target ratio_1 }.
 (* then the update let it go there *)

End DGF.
