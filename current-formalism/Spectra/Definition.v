Require Import SetoidDec.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


(** **  Spectra  **)

Class Spectrum loc  {Sloc : Setoid loc}   `{@EqDec loc Sloc}
               info {Sinfo : Setoid info} `{@EqDec info Sinfo}
               {Info : @Information loc Sloc _ info Sinfo _}
               `{Names} := {
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
