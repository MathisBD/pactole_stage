(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
                                                                            
   C. Auger, P. Courtieu, L. Rieg, X. Urbain                                
                                                                            
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence       *)


Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import Setoid.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.Stream.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Spectra.Definition.

(* 
<<<<<<< HEAD
=======

Module Type Sig (Location : DecidableType)
                (N : Size)
                (Names : Robots(N))
                (Info : Information DecidableTypeWithApplication(Location))
                (Config : Configuration(Location)(N)(Names)(Info))
                (Spect : Spectrum(Location)(N)(Names)(Info)(Config)).
  
  (** ** Good robots have a common program, which we call a robogram *)
  
  Record robogram := {
    pgm :> Spect.t → Location.t;
    pgm_compat : Proper (Spect.eq ==> Location.eq) pgm}.
  Existing Instance pgm_compat.
  
  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  Declare Instance req_equiv : Equivalence req.

  (** Lifting an equivalence relation to an option type. *)
  Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
    match xo, yo with
      | None, None => True
      | None, Some _ | Some _, None => False
      | Some x, Some y => eqT x y
    end.
  Declare Instance opt_eq_refl : forall T (R : relation T), Reflexive R -> Reflexive (opt_eq R).
  Declare Instance opt_eq_sym : forall T (R : relation T), Symmetric R -> Symmetric (opt_eq R).
  Declare Instance opt_eq_trans : forall T (R : relation T), Transitive R -> Transitive (opt_eq R).
  Declare Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).

  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  Definition execution := Stream.t Config.t.
  
  (** *** Destructors for executions *)
  
  Definition eeq : execution -> execution -> Prop := Stream.eq Config.eq.
  
  Declare Instance eeq_equiv : Equivalence eeq.
  Declare Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@hd _).
  Declare Instance eeq_tl_compat : Proper (eeq ==> eeq) (@tl _).
End Sig.


Module Make (Location : DecidableType)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableTypeWithApplication(Location))
            (Config : Configuration(Location)(N)(Names)(Info))
            (Spect : Spectrum(Location)(N)(Names)(Info)(Config))
            : Sig (Location)(N)(Names)(Info)(Config)(Spect).

(** ** Programs for good robots *)

Unset Implicit Arguments.

>>>>>>> new-names
 *)
(** ** Good robots have a common program, which we call a robogram *)

Section Robogram.
Context {loc info : Type}.
Context {Sloc : Setoid loc}   {Eloc : EqDec Sloc}.
Context {Sinfo : Setoid info} {Einfo : EqDec Sinfo}.
Context {pN : NamesDef} {N : Names}.
Context {Info : Information loc Sloc Eloc info Sinfo Einfo}.
Context {Spect : Spectrum loc info}.

Local Notation configuration := (@configuration loc info _ _ _ _ _ _ _ _).
Local Notation spectrum := (@spectrum loc _ _ info _ _ _ _ _ Spect).


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


(** ** Executions *)

(** Now we can [execute] some robogram from a given configuration with a [demon] *)
Definition execution := Stream.t configuration.
End Robogram.
