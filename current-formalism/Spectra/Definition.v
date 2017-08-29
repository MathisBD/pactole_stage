Require Import SetoidDec.
Require Import Pactole.Robots.
Require Import Pactole.RobotInfo.
Require Import Pactole.Configurations.


(** **  Spectra  **)
(*
Class Spectrum loc info `{IsLocation loc info} `{Names} := {
  (** Spectrum is a decidable type *)
  spectrum : Type;
  spectrum_Setoid : Setoid spectrum;
  spectrum_EqDec : EqDec spectrum_Setoid;

  (** A predicate characterizing correct spectra for a given local configuration *)
  spect_from_config : configuration -> spectrum;
  spect_from_config_compat : Proper (equiv ==> equiv) spect_from_config;
  spect_is_ok : spectrum -> configuration -> Prop;
  spect_from_config_spec : forall config, spect_is_ok (spect_from_config config) config}.

Existing Instance spectrum_Setoid.
Existing Instance spectrum_EqDec.
Existing Instance spect_from_config_compat.
*)

Class Spectrum loc info `{IsLocation loc info} `{Names} := {
  (** Spectrum is a decidable type *)
  spectrum : Type;
  spectrum_Setoid : Setoid spectrum;
  spectrum_EqDec : EqDec spectrum_Setoid;
  
  (** A predicate characterizing correct spectra for a given local configuration *)
  spect_from_config : @configuration info _ _ _ _ -> loc -> spectrum;
  spect_from_config_compat : Proper (equiv ==> equiv ==> equiv) spect_from_config;
  spect_is_ok : spectrum ->  @configuration info _ _ _ _ -> Prop;
  spect_from_config_spec : forall config pt, spect_is_ok (spect_from_config config pt) config;
  
  (** The location from which the observation is made *)
  get_current : spectrum -> loc;
  get_current_ok : forall config pt, get_current (spect_from_config config pt) == pt }.

Existing Instance spectrum_Setoid.
Existing Instance spectrum_EqDec.
Existing Instance spect_from_config_compat.
