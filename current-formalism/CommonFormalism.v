(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.Streams.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


(** ** Good robots have a common program, which we call a robogram *)

Section Robogram.
Hypothesis (loc : Type).
Context {S : Setoid loc}.
Context {ES : EqDec S}.
Context {pN : NamesDef}.
Context {N : Names}.
Context {Spect : @Spectrum loc S ES pN N}.

Record robogram := {
  pgm :> spectrum → loc;
  pgm_compat : Proper (equiv ==> equiv) pgm}.
Existing Instance pgm_compat.

Instance reqSetoid : Setoid robogram := {| equiv := fun r1 r2 => forall s, equiv (pgm r1 s) (pgm r2 s) |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Qed.


(** Lifting an equivalence relation to an option type. *)
Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
  match xo, yo with
    | None, None => True
    | None, Some _ | Some _, None => False
    | Some x, Some y => eqT x y
  end.

Instance opt_eq_refl : forall T (R : T -> T -> Prop), Reflexive R -> Reflexive (opt_eq R).
Proof. intros T R HR [x |]; simpl; auto. Qed.

Instance opt_eq_sym : forall T (R : T -> T -> Prop), Symmetric R -> Symmetric (opt_eq R).
Proof. intros T R HR [x |] [y |]; simpl; auto. Qed.

Instance opt_eq_trans : forall T (R : T -> T -> Prop), Transitive R -> Transitive (opt_eq R).
Proof. intros T R HR [x |] [y |] [z |]; simpl; intros; eauto; contradiction. Qed.

Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
Proof. split; auto with typeclass_instances. Qed.

Instance opt_setoid T (S : Setoid T) : Setoid (option T) := {| equiv := opt_eq equiv |}.


(** ** Executions *)

(** Now we can [execute] some robogram from a given configuration with a [demon] *)
Definition execution := Streams.t config.

(** *** Destructors for executions *)

Definition eeq : execution -> execution -> Prop := Streams.eq equiv.

(** ** Prelude for Demonic schedulers *)

Instance eeq_equiv : Equivalence eeq.
Proof. apply Streams.eq_equiv. autoclass. Qed.

Instance eeq_hd_compat : Proper (eeq ==> equiv) (@hd _) := Streams.hd_compat _.
Instance eeq_tl_compat : Proper (eeq ==> eeq) (@tl _) := Streams.tl_compat _.
End Robogram.
