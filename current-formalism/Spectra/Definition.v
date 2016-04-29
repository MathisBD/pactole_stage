Require Import SetoidDec.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


(** **  Spectra  **)

Class Spectrum loc {S : Setoid loc} `{@EqDec loc S} `{Names} := {
  (** Spectrum is a decidable type *)
  spectrum : Type;
  spectrum_Setoid : Setoid spectrum;
  spectrum_EqDec : EqDec spectrum_Setoid;

  (** A predicate characterizing correct spectra for a given local configuration *)
  spect_from_config : @configuration loc _ _ _ _ _ -> spectrum;
  spect_from_config_compat : Proper (equiv ==> equiv) spect_from_config;
  spect_is_ok : spectrum -> @configuration loc _ _ _ _ _ -> Prop;
  spect_from_config_spec : forall config, spect_is_ok (spect_from_config config) config}.

Global Existing Instance spectrum_Setoid.
Global Existing Instance spectrum_EqDec.
Global Existing Instance spect_from_config_compat.
