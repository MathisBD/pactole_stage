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
Require Import Pactole.Spectra.Definition.


(** ** Good robots have a common program, which we call a robogram *)

Section Robogram.
Context {loc : Type}.
Context {S : Setoid loc}.
Context {ES : EqDec S}.
Context {pN : NamesDef}.
Context {N : Names}.
Context {Spect : @Spectrum loc S ES pN N}.

Record robogram := {
  pgm :> spectrum → loc;
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
Definition execution := Streams.t configuration.

Global Instance execution_Setoid : Setoid execution := {| equiv := Streams.eq equiv |}.

Global Instance eeq_hd_compat : Proper (equiv ==> equiv) (@hd _) := Streams.hd_compat _.
Global Instance eeq_tl_compat : Proper (equiv ==> equiv) (@tl _) := Streams.tl_compat _.
End Robogram.
