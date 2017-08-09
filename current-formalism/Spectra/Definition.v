Require Import SetoidDec.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


(** **  Spectra  **)

Class Spectrum loc info `{Info : Information loc info} `{Names} := {
  (** Spectrum is a decidable type *)
  spectrum : Type;
  spectrum_Setoid : Setoid spectrum;
  spectrum_EqDec : EqDec spectrum_Setoid;

  (** A predicate characterizing correct spectra for a given local configuration *)
  spect_from_config : @configuration loc _ _ _ _ _ _ _ _ _ -> spectrum;
  spect_from_config_compat : Proper (equiv ==> equiv) spect_from_config;
  spect_is_ok : spectrum -> @configuration loc _ _ _ _ _ _ _ _ _ -> Prop;
  spect_from_config_spec : forall config, spect_is_ok (spect_from_config config) config}.

Existing Instance spectrum_Setoid.
Existing Instance spectrum_EqDec.
Existing Instance spect_from_config_compat.


Class PointedSpectrum loc info `{Info : Information loc info} `{Names} := {
  (** Spectrum is a decidable type *)
  pspectrum : Type;
  pspectrum_Setoid : Setoid pspectrum;
  pspectrum_EqDec : EqDec pspectrum_Setoid;
  
  (** A predicate characterizing correct spectra for a given local configuration *)
  pspect_from_config : @configuration loc _ _ _ _ _ _ _ _ _ -> loc -> pspectrum;
  pspect_from_config_compat : Proper (equiv ==> equiv ==> equiv) pspect_from_config;
  pspect_is_ok : pspectrum -> @configuration loc _ _ _ _ _ _ _ _ _ -> Prop;
  pspect_from_config_spec : forall config pt, pspect_is_ok (pspect_from_config config pt) config;
  
  get_current : pspectrum -> loc;
  get_current_ok : forall config pt, get_current (pspect_from_config config pt) == pt}.

Existing Instance pspectrum_Setoid.
Existing Instance pspectrum_EqDec.
Existing Instance pspect_from_config_compat.
