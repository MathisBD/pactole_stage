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
Require Import Classes.RelationPairs.
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
    To be able to use it effectively, we need projections lifting this abstract type
    to parts of it that enjoy additional properties.
    For instance, the space in which robots evolve may be a real metric space, a graph, ...  *)

(** The minimum we ask for is the current location of the robot,
    together with a way to lift functions on locations to functions on state,
    possibly under some precondition. *)
(* RMK: the precondition is required for the lifting to [sig]. *)
Class State `{Location} info := {
  get_location : info -> location;
  (** States are equipped with a decidable equality *)
  state_Setoid :> Setoid info;
  state_EqDec :> EqDec state_Setoid;
  (** Lifting a change of frame from a location to a full state, under some precondition *)
  precondition : (location -> location) -> Type;
  lift : sigT precondition -> info -> info;
  lift_id : forall Pid, lift (existT precondition id Pid) == id;
(*  lift_compose : forall f g state, Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
    lift f (lift g state) == lift (fun x => f (g x)) state;*)
  get_location_lift : forall f state, get_location (lift f state) == projT1 f (get_location state);
  (** Compatibility properties *)
  get_location_compat :> Proper (equiv ==> equiv) get_location;
  lift_compat :> Proper ((equiv ==> equiv)%signature @@ (@projT1 _ precondition) ==> equiv ==> equiv) lift }.
(*   lift_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) lift }. *)

Arguments State {_} info.

(** **  Some operators to build states  **)

(** A basic state containing only the current location. *)
Instance OnlyLocation `{Location} : State location := {|
  get_location := id;
  lift := fun f => projT1 f;
  precondition := fun _ => True |}.
Proof. all:autoclass. abstract (intros ? ? Heq x; apply Heq; reflexivity). Defined.

(** Adding a location-typed field that is affected by frame change. *)
Instance AddLocation `{Location} info (St : State info) : State (info * location) := {|
  get_location := fun x => get_location (fst x);
  lift := fun f x => (lift f (fst x), projT1 f (snd x));
  precondition := precondition |}.
Proof.
+ apply prod_Setoid; apply state_Setoid || apply location_Setoid.
+ apply prod_EqDec; apply state_EqDec || apply location_EqDec.
+ intros Pid []. simpl. split; try reflexivity; []. apply lift_id.
(* + intros f g [] **. simpl. split; try reflexivity; []. now apply lift_compose. *)
+ intros f []. simpl. apply get_location_lift.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg []. simpl. split.
  - now apply lift_compat.
  - now apply Hfg.
Defined.

(** Adding information that is not affected by frame change. *)
Instance AddInfo `{Location} info T `{EqDec T} (St : State info) : State (info * T) := {|
  get_location := fun x => get_location (fst x);
  lift := fun f x => (lift f (fst x), snd x);
  precondition := precondition |}.
Proof.
+ apply prod_Setoid; apply state_Setoid || auto.
+ apply prod_EqDec; apply state_EqDec || auto.
+ intros Pid []. simpl. split; try reflexivity; []. apply lift_id.
(* + intros f g [] **. simpl. split; try reflexivity; []. now apply lift_compose. *)
+ intros f []. simpl. apply get_location_lift.
+ intros [] [] []. simpl. now apply get_location_compat.
+ intros f g Hfg [] [] []. simpl in *. split; trivial; []. now apply lift_compat.
Defined.

(* RMK: As [AddLocation] has less parameters than [AddInfo], its priority is higher,
        ensuring that we cannot use the wrong one. *)

(** Restricting a state to satisfy some property. *)
Instance AddProp `{Location} info (P : info -> Prop) (St : State info) : State (sig P) := {|
  get_location := fun x => get_location (proj1_sig x);
  precondition := fun f => prod (@precondition _ _ St f) (forall x Pf, P x -> P (lift (existT precondition f Pf) x));
  lift := fun f x => exist P (lift (existT precondition (projT1 f) (fst (projT2 f))) (proj1_sig x)) _ |}.
Proof.
+ apply sig_Setoid, state_Setoid.
+ autoclass.
+ apply (snd (projT2 f)), proj2_sig.
+ intros ? ?. simpl. apply lift_id.
+ intros f x. simpl. apply get_location_lift.
+ repeat intro. now apply get_location_compat.
+ intros f g Hfg x y Hxy. simpl. now apply lift_compat.
Defined.

(** A more general version restricting a state to have a dependent witness of some type. *)
Instance AddType `{Location} info (P : info -> Type) (St : State info) : State (sigT P) := {|
  get_location := fun x => get_location (projT1 x);
  precondition := fun f => prod (@precondition _ _ St f) (forall x Pf, P x -> P (lift (existT precondition f Pf) x));
  lift := fun f x => existT P (lift (existT precondition (projT1 f) (fst (projT2 f))) (projT1 x)) _ |}.
Proof.
+ apply sigT_Setoid, state_Setoid.
+ autoclass.
+ apply (snd (projT2 f)), projT2.
+ intros ? ?. simpl. apply lift_id.
+ intros f x. simpl. apply get_location_lift.
+ repeat intro. now apply get_location_compat.
+ intros f g Hfg x y Hxy. simpl. now apply lift_compat.
Defined.
