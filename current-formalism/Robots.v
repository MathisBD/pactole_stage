(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.FinComplements.


Set Implicit Arguments.


(** ** Byzantine Robots *)

(** We have finetely many robots. Some are good, other are byzantine.
    Both are represented by an abtract type that can be enumerated. *)

Class NamesDef := {
  nG : nat;
  nB : nat;
  G : Type;
  B : Type;
  Gnames : list G;
  Bnames : list B}.

Inductive identifier {G} {B} : Type :=
  | Good (g : G)
  | Byz (b : B).

Definition ident `{H : NamesDef} := @identifier (@G H) (@B H).

Definition names `{H : NamesDef} : list ident := List.map Good Gnames ++ List.map Byz Bnames.


Class Names `{NamesDef} := {
  In_Gnames : forall g : G, In g Gnames;
  In_Bnames : forall b : B, In b Bnames;
  Gnames_NoDup : NoDup Gnames;
  Bnames_NoDup : NoDup Bnames;
  Gnames_length : length Gnames = nG;
  Bnames_length : length Bnames = nB}.

Lemma In_names `{Names} : forall r : ident, In r names.
Proof.
intro r. cbn. unfold names. rewrite in_app_iff. destruct r as [g | b].
- left. apply in_map, In_Gnames.
- right. apply in_map, In_Bnames.
Qed.

Lemma names_NoDup `{Names} : NoDup names.
Proof.
unfold names. rewrite <- NoDupA_Leibniz. apply (NoDupA_app _).
+ apply (map_injective_NoDupA _ _).
  - now repeat intro; subst.
  - intros ? ? Heq. now inversion Heq.
  - rewrite NoDupA_Leibniz. apply Gnames_NoDup.
+ apply (map_injective_NoDupA _ _).
  - now repeat intro; subst.
  - intros ? ? Heq. now inversion Heq.
  - rewrite NoDupA_Leibniz. apply Bnames_NoDup.
+ intros id HinA HinB. rewrite (InA_map_iff _ _) in HinA. rewrite (InA_map_iff _ _) in HinB.
  - destruct HinA as [? [? ?]], HinB as [? [? ?]]. subst. discriminate.
  - now repeat intro; subst.
  - now repeat intro; subst.
Qed.

Lemma names_length `{Names} : length names = nG + nB.
Proof. unfold names. now rewrite app_length, map_length, map_length, Gnames_length, Bnames_length. Qed.

Local Instance RobotsDef (n m : nat) : NamesDef := {|
  nG := n;
  nB := m;
  G := Fin.t n;
  B := Fin.t m |}.
Proof.
+ unfold G. cbn. apply (fin_map id).
+ unfold B. cbn. apply (fin_map id).
Defined.

Local Instance Robots (n m : nat) : @Names (RobotsDef n m).
Proof. split.
+ intro g. unfold Gnames. change g with (Datatypes.id g). apply In_fin_map.
+ intro b. unfold Bnames. change b with (Datatypes.id b). apply In_fin_map.
+ unfold Gnames. apply fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
+ unfold Bnames. apply fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
+ cbn. apply fin_map_length.
+ cbn. apply fin_map_length.
Qed.
