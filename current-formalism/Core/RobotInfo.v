(**************************************************************************)
(*  Mechanised Framework for Local Interactions & Distributed Algorithms  *)
(*  T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        *)
(*  PACTOLE project                                                       *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(**************************************************************************)

(** Mechanised Framework for Local Interactions & Distributed Algorithms    
                                                                            
    T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                          
                                                                            
    PACTOLE project                                                         
                                                                            
    This file is distributed under the terms of the CeCILL-C licence      *)


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
  (** Lifting a change of frame to the location field *)
  app : (loc -> loc) -> info -> info;
  app_id : @equiv _ (fun_equiv _ _) (app id) id;
  app_compose : forall f g state, app f (app g state) == app (fun x => f (g x)) state;
  get_location_app : forall f state, get_location (app f state) == f (get_location state);
  (** Compatibility properties *)
  get_location_compat :> Proper (equiv ==> equiv) get_location;
  app_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) app }.

Arguments IsLocation loc info {_} {_} {_} {_}.

(* TODO: Define the disjoint union of such projections to ensure their independence. *)

(** A basic state containing only the current location. *)
Definition OnlyLocation loc `{EqDec loc} : IsLocation loc loc := {|
  get_location := id;
  app := id;
  app_id := reflexivity _;
  app_compose := ltac:(reflexivity);
  get_location_app := ltac:(reflexivity) |}.

(** Adding information that is not affected by frame change. *)
Instance AddInfo T loc info `{EqDec T} `(IsLocation loc info) : IsLocation loc (info * T) := {|
  get_location := fun x => get_location (fst x);
  app := fun f x => (app f (fst x), snd x) |}.
Proof.
+ intros []. simpl. split; try reflexivity; []. apply app_id.
+ intros f g []. simpl. split; try reflexivity; []. apply app_compose.
+ intros f []. simpl. apply get_location_app.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg [] [] []. simpl. repeat split; trivial; []. now apply app_compat.
Defined.

(** Adding a location-typed field that is affected by frame change. *)
Instance AddLocation loc info `(IsLocation loc info) : IsLocation loc (info * loc) := {|
  get_location := fun x => get_location (fst x);
  app := fun f x => (app f (fst x), f (snd x)) |}.
Proof.
+ intros []. simpl. split; try reflexivity; []. apply app_id.
+ intros f g []. simpl. split; try reflexivity; []. apply app_compose.
+ intros f []. simpl. apply get_location_app.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg [] [] []. simpl. split.
  - now apply app_compat.
  - now apply Hfg.
Defined.
