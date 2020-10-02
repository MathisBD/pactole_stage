(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8_core.
Require Import Arith_base.
Require Import Lia.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Core.State.
Require Import Pactole.Core.Configuration.
Require Import Pactole.Observations.Definition.
Close Scope R_scope.
Set Implicit Arguments.


Section CompositionObservation.

(** **  Loosing information inside the state before building the observation  **)
Context {Loc : Location}.
Context {info1 info2 : Type}.
Context {St1 : @State _ info1}.
Context {St2 : @State _ info2}.
Context {N : Names}.
Context (Obs : @Observation _ _ St2 _).

Variable f : info1 -> info2.
Hypothesis f_compat : Proper (equiv ==> equiv) f.

(* TODO: find a better name *)
Instance FObservation : @Observation _ _ St1 _.
refine {|
  obs_from_config := fun config st => obs_from_config (map_config f config) (f st);
  obs_is_ok := fun sp config st => obs_is_ok sp (map_config f config) (f st) |}.
Proof.
(* BUG?: + forbidden here? *)
+ autoclass.
+ repeat intro. do 2 (f_equiv; trivial).
+ intros. apply obs_from_config_spec.
Defined.

End CompositionObservation.

Arguments FObservation {_} {info1} {info2} {_} {_} {_} _ f {_}.
