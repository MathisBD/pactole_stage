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


(** *  Space  **)

(** The space in which robots evolve, which must have a decidable equality.

    There is no direct instantiation, making sure that no spurious instance can be created.
    Instead, the user must provide the instance using [make_Space]. *)
Class Location := {
  location : Type;
  location_Setoid :> Setoid location;
  location_EqDec :> EqDec location_Setoid }.

Definition make_Location (T : Type) `{EqDec T} := {| location := T |}.
Arguments make_Location T {_} {_}.

(** *  Robot State  **)

(** The states of robots is left as an abstract parameter.
    To be able to use it effectively, we need projections mlifting this abstract type
    to parts of it that enjoy additional properties.
    For instance, the space in which robots evolve may be a real metric space, a graph, ...  *)

(** The minimum we ask for is the current location of the robot. *)
Class State info `{Location} := {
  get_location : info -> location;
  (** States are equipped with a decidable equality *)
  state_Setoid :> Setoid info;
  state_EqDec :> EqDec state_Setoid;
  (** Lifting a change of frame to the location field *)
  lift : (location -> location) -> info -> info;
  lift_id : @equiv _ (fun_equiv _ _) (lift id) id;
(*  lift_compose : forall f g state, Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
    lift f (lift g state) == lift (fun x => f (g x)) state;*)
  get_location_lift : forall f state, get_location (lift f state) == f (get_location state);
  (** Compatibility properties *)
  get_location_compat :> Proper (equiv ==> equiv) get_location;
  lift_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) lift }.

Arguments State info {_}.

(** A basic state containing only the current location. *)
Definition OnlyLocation `{Location} : State location := {|
  get_location := id;
  lift := id;
  lift_id := reflexivity _;
(*   lift_compose := ltac:(reflexivity); *)
  get_location_lift := ltac:(reflexivity) |}.

(** Adding a location-typed field that is affected by frame change. *)
Instance AddLocation info `(State info) : State (info * location) := {|
  get_location := fun x => get_location (fst x);
  lift := fun f x => (lift f (fst x), f (snd x)) |}.
Proof.
+ apply prod_Setoid; apply state_Setoid || apply location_Setoid.
+ apply prod_EqDec; apply state_EqDec || apply location_EqDec.
+ intros []. simpl. split; try reflexivity; []. apply lift_id.
(* + intros f g [] **. simpl. split; try reflexivity; []. now apply lift_compose. *)
+ intros f []. simpl. apply get_location_lift.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg [] [] []. simpl. split.
  - now apply lift_compat.
  - now apply Hfg.
Defined.

(** Adding information that is not affected by frame change. *)
Instance AddInfo info T `{EqDec T} `(State info) : State (info * T) := {|
  get_location := fun x => get_location (fst x);
  lift := fun f x => (lift f (fst x), snd x) |}.
Proof.
+ apply prod_Setoid; apply state_Setoid || auto.
+ apply prod_EqDec; apply state_EqDec || auto.
+ intros []. simpl. split; try reflexivity; []. apply lift_id.
(* + intros f g [] **. simpl. split; try reflexivity; []. now apply lift_compose. *)
+ intros f []. simpl. apply get_location_lift.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg [] [] []. simpl. repeat split; trivial; []. now apply lift_compat.
Defined.

(* RMK: As [AddLocation] has less parameters than [AddInfo], its priority is higher,
        ensuring that we cannot use the wrong one. *)