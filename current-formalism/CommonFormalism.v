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
Require Import Pactole.Streams.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.



Module Type Sig (Location : DecidableType)(N : Size)(Names : Robots(N))(Info : DecidableType)
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
  Definition execution := Streams.t Config.t.
  
  (** *** Destructors for executions *)
  
  Definition eeq : execution -> execution -> Prop := Streams.eq Config.eq.
  
  Declare Instance eeq_equiv : Equivalence eeq.
  Declare Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@hd _).
  Declare Instance eeq_tl_compat : Proper (eeq ==> eeq) (@tl _).
End Sig.


Module Make (Location : DecidableType)(N : Size)(Names : Robots(N))(Info : DecidableType)
            (Config : Configuration(Location)(N)(Names)(Info))
            (Spect : Spectrum(Location)(N)(Names)(Info)(Config))
            : Sig (Location)(N)(Names)(Info)(Config)(Spect).

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

  Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
    match xo, yo with
      | None, None => True
      | None, Some _ | Some _, None => False
      | Some x, Some y => eqT x y
    end.
  Lemma opt_eq_refl : forall T (R : relation T), Reflexive R -> Reflexive (opt_eq R).
  Proof.
    intros.
    unfold opt_eq.
    intros x.
    destruct x.
    apply H.
    trivial.
  Qed.
  
  Lemma opt_eq_sym : forall T (R : relation T), Symmetric R -> Symmetric (opt_eq R).
  Proof.
    intros T R HR x y Hxy; unfold opt_eq in *.
    destruct x, y; trivial.
    now apply HR.
  Qed.

  Lemma opt_eq_trans : forall T (R : relation T), Transitive R -> Transitive (opt_eq R).
  Proof.
    intros T R HR x y z Hxy Hyz; unfold opt_eq in *; destruct x, y, z; trivial. 
    now transitivity t0.
    easy.
  Qed.
  
  Lemma opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
  Proof.
    repeat split;
      destruct HeqT as [Hr Hs Ht];
      (try (now apply opt_eq_refl));
      try (now apply opt_eq_sym);
      try now apply (opt_eq_trans).
  Qed.
    (** ** Executions *)

(** Now we can [execute] some robogram from a given position with a [demon] *)
Definition execution := Streams.t Config.t.

Definition eeq (e1 e2 : execution) : Prop := Streams.eq Config.eq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. apply Streams.eq_equiv. apply Config.eq_equiv. Qed.

Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@hd _) := Streams.hd_compat _.
Instance eeq_tl_compat : Proper (eeq ==> eeq) (@tl _) := Streams.tl_compat _.
End Make.
