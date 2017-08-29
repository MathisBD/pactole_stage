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


Section Formalism.
Context (V E info  : Type).
Context {G : Graph V E}.
Context `{Names}.
Context `{EqDec info}.
Context {Loc : IsLocation V info}.
Context {Tar : IsTarget V info}.


(* Never used if we start from a good config. *)
Axiom e_default : E.

Context `{@Spectrum V info _ _ _ _ _ _}.

Notation "s ⁻¹" := (Isomorphism.inverse s) (at level 99).
Notation spectrum := (@spectrum V info _ _ _ _ _ _ _).
Notation configuration := (@configuration info _ _ _ _).

(** The robogram should return only adjacent node values.
    We enforce this by making a check in the [update_state] component of the demon. *)
Definition discrete_rigid_da da :=
  forall g state pt,
    find_edge (get_location state) pt <> None -> (* if the robogramme tries to move on an adjacent node *)
    get_location (update_state da g pt state) == pt. (* then the robogram let it go there *)

Definition discrete_rigid_demon := Stream.forever (Stream.instant discrete_rigid_da).


(** ** Full synchronicity

A fully synchronous demon is a particular case of fair demon: all good robots
are activated at each round. In our setting this means that the demon never
return a null reference. *)

(** A demonic action is synchronous if all robots are in the same state: either all [Active], or all [Moving]. *)
Definition da_Synchronous da : Prop := forall id id', activate da id = activate da id'.

Instance da_Synchronous_compat : Proper (equiv ==> iff) da_Synchronous.
Proof. unfold da_Synchronous. intros d1 d2 Hd. now setoid_rewrite Hd. Qed.

Definition StepSynchronous := Stream.forever (Stream.instant da_Synchronous).

Instance StepSynchronous_compat : Proper (equiv ==> iff) StepSynchronous.
Proof. unfold StepSynchronous. autoclass. Qed.

End Formalism.
