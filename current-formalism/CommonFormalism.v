(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
                                                                            
   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                           
                                                                            
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

Set Implicit Arguments.
Require Import SetoidDec.
Require Pactole.Util.Stream.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Spectra.Definition.


Section Robogram.
Context {loc info : Type}.
Context `{Information loc info}.
Context `{Names}.
Context {Spect : Spectrum loc info}.

Local Notation configuration := (@configuration loc info _ _ _ _ _ _ _ _).
Local Notation spectrum := (@spectrum loc info _ _ _ _ _ _ _ Spect).


(** Good robots have a common program, which we call a [robogram]. *)
Record robogram := {
  pgm :> spectrum -> loc;
  pgm_compat : Proper (@equiv _ spectrum_Setoid ==> equiv) pgm}.
Global Existing Instance pgm_compat.

Global Instance robogram_Setoid : Setoid robogram := {|
  equiv := fun r1 r2 => forall s, equiv (pgm r1 s) (pgm r2 s) |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

(** Executions are simply streams of configurations. *)
Definition execution := Stream.t configuration.
End Robogram.
