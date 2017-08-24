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
Require Import Pactole.Robots.
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
  update_location : loc -> info -> info;
  (** Performing a change of frame on the whole state *)
  app : (loc -> loc) -> info -> info;
  app_id : app id == id;
  app_compose : forall f g state, app f (app g state) == app (fun x => f (g x)) state;
  (** Compatibility properties *)
  get_location_compat :> Proper (equiv ==> equiv) get_location;
  update_location_compat :> Proper (equiv ==> equiv ==> equiv) update_location;
  app_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) app }.
(* The [loc] argument is relative to the current location *)

(* TODO: Define the disjoint union of such projections to ensure their independence. *)