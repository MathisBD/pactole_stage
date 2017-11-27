(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)


Require Import Rbase.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Decidable.
Require Import Pactole.Util.Preliminary.
Require Pactole.Util.Bijection.
Require Import Pactole.Core.Robots.
Import Pactole.Util.Bijection.Notations.
Set Implicit Arguments.


(** *  Robot Information  **)

(** The states of robots is left as an abstract parameter.
    To be able to use it effectively, we need projections mapping this abstract type
    to parts of it that enjoy additional properties.
    For instance, the space in which robots evolve may be a real metric space, a graph, ...  *)

(** The minimum we ask for is the current location of the robot. *)
Class IsLocation loc info `{EqDec info} `{EqDec loc} := {
  get_location : info -> loc;
(*   update_location : loc -> info -> info; (* The [loc] argument is relative to the current location *) *)
  (** Lifting a change of frame to the location field *)
  app : (loc -> loc) -> info -> info;
  app_id : @equiv _ (fun_equiv _ _) (app id) id;
  app_compose : forall f g state, app f (app g state) == app (fun x => f (g x)) state;
  get_location_app : forall f state, get_location (app f state) == f (get_location state);
  (** Compatibility properties *)
  get_location_compat :> Proper (equiv ==> equiv) get_location;
(*   update_location_compat :> Proper (equiv ==> equiv ==> equiv) update_location; *)
  app_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) app }.

Arguments IsLocation loc info {_} {_} {_} {_}.


(** Same class but different name. *)
Class IsTarget loc info `{IsLocation loc info} := {
  get_target : info -> loc;
(*   update_target : loc -> info -> info; *)
  get_target_app : forall f state, get_target (app f state) == f (get_target state);
  (** Compatibility properties *)
  get_target_compat :> Proper (equiv ==> equiv) get_target }.
(*   update_target_compat :> Proper (equiv ==> equiv ==> equiv) update_target }. *)

Arguments IsTarget loc info {_} {_} {_} {_} {_}.

(* TODO: Define the disjoint union of such projections to ensure their independence. *)

Definition OnlyLocation loc `{EqDec loc} : IsLocation loc loc := {|
  get_location := id;
  app := id;
  app_id := reflexivity _;
  app_compose := ltac:(reflexivity);
  get_location_app := ltac:(reflexivity) |}.
