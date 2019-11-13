(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)

Require Import SetoidDec.
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Core.State.
Require Import Pactole.Core.Configuration.


(** **  Observations  **)

Class Observation {info} `{State info} `{Names} := {
  (** observation is a decidable type *)
  observation : Type;
  observation_Setoid : Setoid observation;
  observation_EqDec : EqDec observation_Setoid;
  
  (** Converting a (local) configuration into an observation, given the state of the observer *)
  obs_from_config : configuration -> info -> observation;
  obs_from_config_compat : Proper (equiv ==> equiv ==> equiv) obs_from_config;
  
  (** A predicate characterizing correct observations for a given (local) configuration *)
  obs_is_ok : observation ->  configuration -> info -> Prop;
  obs_from_config_spec : forall config st, obs_is_ok (obs_from_config config st) config st }.

Existing Instance observation_Setoid.
Existing Instance observation_EqDec.
Existing Instance obs_from_config_compat.
Arguments obs_from_config : simpl never.
