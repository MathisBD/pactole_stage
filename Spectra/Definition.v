(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)

Require Import SetoidDec.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Core.Configurations.


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

Class Spectrum {info} `{State info} `{Names} := {
  (** Spectrum is a decidable type *)
  spectrum : Type;
  spectrum_Setoid : Setoid spectrum;
  spectrum_EqDec : EqDec spectrum_Setoid;
  
  (** Converting a (local) configuration into a spectrum, given the state of the observer *)
  spect_from_config : configuration -> info -> spectrum;
  spect_from_config_compat : Proper (equiv ==> equiv ==> equiv) spect_from_config;
  
  (** A predicate characterizing correct spectra for a given (local) configuration *)
  spect_is_ok : spectrum ->  configuration -> info -> Prop;
  spect_from_config_spec : forall config st, spect_is_ok (spect_from_config config st) config st }.

Existing Instance spectrum_Setoid.
Existing Instance spectrum_EqDec.
Existing Instance spect_from_config_compat.
Arguments spect_from_config : simpl never.
