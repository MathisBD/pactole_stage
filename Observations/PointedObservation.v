(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

Require Import SetoidDec.
Require Import Pactole.Util.SetoidDefs.
Require Import Pactole.Core.State.
Require Import Pactole.Observations.Definition.
Set Implicit Arguments.


Section PointedObservation.

Context {Loc : Location}.
Context {info : Type}.
Context {St : State info}.
Context {N : Identifiers.Names}.
Context {Obs : Observation}.

Instance PointedObservation : Observation := {|
  observation := observation * info;
  observation_Setoid := prod_Setoid observation_Setoid state_Setoid;
  observation_EqDec := prod_EqDec observation_EqDec state_EqDec;
  obs_from_config := fun config st => (obs_from_config config st, st);
  obs_from_config_compat := ltac:(repeat intro; now split; trivial; apply obs_from_config_compat);
  obs_is_ok := fun obs config st => obs_is_ok (fst obs) config st /\ st == snd obs;
  obs_from_config_spec := fun config st => conj (obs_from_config_spec config st) (reflexivity st) |}.

End PointedObservation.
