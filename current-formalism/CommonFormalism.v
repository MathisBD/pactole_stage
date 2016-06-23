(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


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
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.




Module Type Sig (Location : DecidableType)(N : Size)(Names : Robots(N))
                (Config : Configuration(Location)(N)(Names))
                (Spect : Spectrum(Location)(N)(Names)(Config)).
  
  (** ** Good robots have a common program, which we call a robogram *)
  
  Record robogram := {
    pgm :> Spect.t → Location.t;
    pgm_compat : Proper (Spect.eq ==> Location.eq) pgm}.
  Existing Instance pgm_compat.
  
  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  Declare Instance req_equiv : Equivalence req.
  
  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  CoInductive execution :=
    NextExecution : Config.t → execution → execution.
  
  (** *** Destructors for demons *)
  
  Definition execution_head (e : execution) : Config.t :=
    match e with NextExecution conf _ => conf end.
  
  Definition execution_tail (e : execution) : execution :=
    match e with NextExecution _ e => e end.
  
  CoInductive eeq (e1 e2 : execution) : Prop :=
    | Ceeq : Config.eq (execution_head e1) (execution_head e2) ->
             eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.
  
  Declare Instance eeq_equiv : Equivalence eeq.
  Declare Instance eeq_bisim : Bisimulation execution.
  Declare Instance execution_head_compat : Proper (eeq ==> Config.eq) execution_head.
  Declare Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
End Sig.


Module Make (Location : DecidableType)(N : Size)(Names : Robots(N))
            (Config : Configuration(Location)(N)(Names))
            (Spect : Spectrum(Location)(N)(Names)(Config))
            : Sig (Location)(N)(Names)(Config)(Spect).

(** ** Programs for good robots *)

Unset Implicit Arguments.

(** ** Good robots have a common program, which we call a robogram *)

Record robogram := {
  pgm :> Spect.t → Location.t;
  pgm_compat : Proper (Spect.eq ==> Location.eq) pgm}.

Global Existing Instance pgm_compat.

Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
+ intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
+ intros r1 r2 r3 H1 H2 x y Heq.
  rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
Qed.

(** ** Executions *)

(** Now we can [execute] some robogram from a given configuration with a [demon] *)
CoInductive execution :=
  NextExecution : Config.t → execution → execution.


(** *** Destructors for demons *)

Definition execution_head (e : execution) : Config.t :=
  match e with NextExecution conf _ => conf end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

CoInductive eeq (e1 e2 : execution) : Prop :=
  | Ceeq : Config.eq (execution_head e1) (execution_head e2) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. split.
+ coinduction eeq_refl. reflexivity.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. 
  - inversion H. inversion H0. now transitivity (execution_head y).
  - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
    now inversion H. now inversion H0.
Qed.

Instance eeq_bisim : Bisimulation execution.
Proof. exists eeq. apply eeq_equiv. Qed.

Instance execution_head_compat : Proper (eeq ==> Config.eq) execution_head.
Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.

Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
Proof. intros e1 e2 He. now inversion He. Qed.

End Make.
