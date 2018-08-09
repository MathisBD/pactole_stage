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
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.Configurations.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Spectra.Definition.
Close Scope R_scope.
Set Implicit Arguments.
Set Default Proof Using "All".


Section CompositionSpectrum.

(** **  Loosing information inside the state before building the spectrum  **)
Context `{Location}.
Context {info1 info2 : Type}.
Context `{St1 : @State info1 _}.
Context `{St2 : @State info2 _}.
Context `{Names}.
Context `(@Spectrum _ _ St2 _).

Variable f : info1 -> info2.
Hypothesis f_compat : Proper (equiv ==> equiv) f.

(* TODO: find a better name *)
Instance FSpectrum : @Spectrum _ _ St1 _ := {|
  spect_from_config := fun config pt => spect_from_config (map_config f config) pt;
  spect_is_ok := fun sp config pt => spect_is_ok sp (map_config f config) pt |}.
Proof.
(* BUG?: + forbidden here? *)
{ autoclass. }
+ autoclass.
+ repeat intro. do 2 (f_equiv; trivial).
+ intros. apply spect_from_config_spec.
Defined.

End CompositionSpectrum.

Arguments FSpectrum {_} {info1} {info2} {_} {_} {_} _ f {_}.
