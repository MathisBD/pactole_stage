(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import FinComplements.


Set Implicit Arguments.


(** ** Byzantine Robots *)

(** We have finetely many robots. Some are good, other are evil. *)

Class Names1 := {
  nG : nat;
  nB : nat;
  G : Type;
  B : Type}.

Class Names2 `{Names1} := { ident : Type }.

Class Names3 `{Names2} := {
  Gnames : list G;
  Bnames : list B}.

Class Names `{Names3} := { names : list ident }.


Class NamesGProperties `{Names} := {
  In_Gnames : forall g : G, In g Gnames;
  Gnames_NoDup : NoDup Gnames;
  Gnames_length : length Gnames = nG}.

Class NamesBProperties `{Names} := {
  In_Bnames : forall b : B, In b Bnames;
  Bnames_NoDup : NoDup Bnames;
  Bnames_length : length Bnames = nB}.

Class NamesProperties `{Names} := {
  In_names : forall r : ident, In r names;
  names_NoDup : NoDup names;
  names_length : length names = nG + nB}.


Instance Robots1 (n m : nat) : Names1 := {|
  nG := n;
  nB := m;
  G := Fin.t n;
  B := Fin.t m |}.


Inductive identifier {G} {B} : Type :=
  | Good (g : G)
  | Byz (b : B).

Instance Robots2 (n m : nat) : @Names2 (Robots1 n m) := {| ident := @identifier (@G (Robots1 n m)) (@B (Robots1 n m)) |}.

Instance Robots3 (n m : nat) : @Names3 _ (Robots2 n m).
Proof.
split.
+ unfold G. cbn. apply (fin_map id).
+ unfold B. cbn. apply (fin_map id).
Defined.

Instance Robots (n m : nat) : @Names _ _ (Robots3 n m).
Proof.
split. cbn. change (list (@identifier (@G (Robots1 n m)) (@B (Robots1 n m)))).
apply (List.map Good Gnames ++ List.map Byz Bnames).
Defined.

Instance RobotsGProperties (n m : nat) : @NamesGProperties _ _ _ (Robots n m).
Proof. split.
+ intro g. unfold Gnames. change g with (Datatypes.id g). apply In_fin_map.
+ unfold Gnames. apply fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
+ cbn. apply fin_map_length.
Qed.

Instance RobotsBProperties (n m : nat) : @NamesBProperties _ _ _ (Robots n m).
Proof. split.
+ intro b. unfold Bnames. change b with (Datatypes.id b). apply In_fin_map.
+ unfold Bnames. apply fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
+ cbn. apply fin_map_length.
Qed.

Instance RobotsProperties (n m : nat) : @NamesProperties _ _ _ (Robots n m).
Proof. split.
* intro r. cbn. rewrite in_app_iff. destruct r as [g | b].
  + left. apply in_map. change (In g (@Gnames _ _ (Robots3 n m))). apply In_Gnames.
  + right. apply in_map. change (In b (@Bnames _ _ (Robots3 n m))). apply In_Bnames.
* unfold names. rewrite <- NoDupA_Leibniz. apply (NoDupA_app _).
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Gnames_NoDup.
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Bnames_NoDup.
  + intros id HinA HinB. rewrite (InA_map_iff _ _) in HinA. rewrite (InA_map_iff _ _) in HinB.
    - destruct HinA as [? [? ?]], HinB as [? [? ?]]. subst. discriminate.
    - now repeat intro; subst.
    - now repeat intro; subst.
* cbn. rewrite app_length, map_length, map_length.
  change (length (@Gnames _ _ (Robots3 n m)) + length (@Bnames _ _ (Robots3 n m)) = n + m).
  now rewrite Gnames_length, Bnames_length.
Qed.
