(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Spectra.Definition.
Set Implicit Arguments.


Instance PointedSpectrum `{Spectrum} : Spectrum := {|
  spectrum := spectrum * location;
  spectrum_Setoid := prod_Setoid _ _;
  spectrum_EqDec := prod_EqDec spectrum_EqDec location_EqDec;
  spect_from_config := fun config pt => (spect_from_config config pt, pt);
  spect_is_ok := fun spect config pt => spect_is_ok (fst spect) config pt /\ pt == snd spect;
  spect_from_config_spec := fun config pt => conj (spect_from_config_spec config pt) (reflexivity pt) |}.
Proof.
abstract (repeat intro; now split; trivial; apply spect_from_config_compat).
Defined.
