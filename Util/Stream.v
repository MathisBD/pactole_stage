(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
                                                                            
   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                           
                                                                            
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence         
                                                                          *)
(**************************************************************************)


Require Import Relations.
Require Import Morphisms.
Require Import SetoidDec.
Require Import RelationClasses.
Require Import Pactole.Util.Coqlib.
Set Implicit Arguments.


(* Replacement to the standard library on streams. *)


Section Streams.

Context {A : Type}.
Context `{Setoid A}.

CoInductive t A : Type := cons : A -> t A -> t A.

Definition hd (s : t A) := match s with | cons e _ => e end.
Definition tl (s : t A) := match s with | cons _ s' => s' end.

Lemma stream_eq s : s = cons (hd s) (tl s).
Proof using . now destruct s. Qed.

CoFixpoint constant (c : A) := cons c (constant c).

CoFixpoint alternate (c1 c2 : A) := cons c1 (cons c2 (alternate c1 c2)).

(** **  Operators over streams  **)

(** Logical operators on properties over streams. *)

Definition instant (P : A -> Prop) := fun s => P (hd s).
Global Arguments instant P s /.

CoInductive forever (P : t A -> Prop) (s : t A) : Prop :=
  Always : P s -> forever P (tl s) -> forever P s.
Global Arguments Always [P] [s] _ _.

Inductive eventually (P : t A -> Prop) (s : t A) : Prop :=
  | Now : P s -> eventually P s
  | Later : eventually P (tl s) -> eventually P s.
Global Arguments Now [P] [s] _.
Global Arguments Later [P] [s] _.

(** Logical operators on relations over streams. *)

Definition instant2 (P : A -> A -> Prop) := fun s1 s2 => P (hd s1) (hd s2).
Global Arguments instant2 P s1 s2 /.

CoInductive forever2 (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
  Always2 : P s1 s2 -> forever2 P (tl s1) (tl s2) -> forever2 P s1 s2.
Global Arguments Always2 [P] [s1] [s2] _ _.

Inductive eventually2 (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
  | Now2 : P s1 s2 -> eventually2 P s1 s2
  | Later2 : eventually2 P (tl s1) (tl s2) -> eventually2 P s1 s2.
Global Arguments Now2 [P] [s1] [s2] _.
Global Arguments Later2 [P] [s1] [s2] _.


(** Extensional equality on streams, up to a setoid equality on the stream elements. *)
Global Instance stream_Setoid : Setoid (t A).
Proof.
exists (forever2 (instant2 equiv)). split.
+ coinduction Heq. simpl. reflexivity.
+ coinduction Heq; simpl.
  - symmetry. match goal with H : forever2 _ _ _ |- _ => now inv H end.
  - match goal with H : forever2 _ _ _ |- _ => now inv H end.
+ coinduction Heq; simpl.
  - transitivity (hd y); match goal with H : forever2 _ _ _ |- _ => now inv H end.
  - transitivity (tl y); match goal with H : forever2 _ _ _ |- _ => now inv H end.
Defined.

(** Some sanity check on [constant] and [alternate]. *)
Lemma constant_hd : forall c : A, hd (constant c) = c.
Proof using . reflexivity. Qed.

Lemma constant_tl : forall c : A, tl (constant c) = constant c.
Proof using . reflexivity. Qed.

Lemma alternate_tl_tl : forall c1 c2 : A, tl (tl (alternate c1 c2)) = alternate c1 c2.
Proof using . reflexivity. Qed.

Lemma alternate_hd : forall c1 c2 : A, hd (alternate c1 c2) = c1.
Proof using . reflexivity. Qed.

Lemma alternate_tl_hd : forall c1 c2 : A, hd (tl (alternate c1 c2)) = c2.
Proof using . reflexivity. Qed.

(** Alternative caracterisation of [alternate]. *)
Lemma alternate_tl : forall c1 c2 : A, tl (alternate c1 c2) == alternate c2 c1.
Proof using . cofix alt. constructor; [| constructor]; simpl; try reflexivity; []. apply alt. Qed.

(** Compatibility lemmas. *)

Global Instance hd_compat : Proper (equiv ==> equiv) hd.
Proof using . intros s s' Hs. now inv Hs. Qed.

Global Instance tl_compat : Proper (equiv ==> equiv) tl.
Proof using . intros s s' Hs. now inv Hs. Qed.

Global Instance constant_compat : Proper (equiv ==> equiv) constant.
Proof using . unfold constant. now coinduction Heq. Qed.

Global Instance aternate_compat : Proper (@equiv A _ ==> equiv ==> equiv) alternate.
Proof using . cofix Heq. do 2 (constructor; trivial). cbn. now apply Heq. Qed.

Global Instance instant_compat : Proper ((equiv ==> iff) ==> equiv ==> iff) instant.
Proof using . intros P Q HPQ s s' Hs. unfold instant. apply HPQ, Hs. Qed.

Global Instance forever_compat : Proper ((equiv ==> iff) ==> equiv ==> iff) forever.
Proof using .
intros P Q HPQ s s' Hs. split.
+ revert s s' Hs. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs). match goal with H : forever _ _ |- _ => now inv H end.
  - inv Hs. match goal with H : forever _ _ |- _ => inv H end. eapply Hrec; eassumption.
+ revert s s' Hs. coinduction Hrec.
  - rewrite (HPQ _ _ Hs). match goal with H : forever _ _ |- _ => now inv H end.
  - inv Hs. match goal with H : forever _ _ |- _ => inv H end. eapply Hrec; eassumption.
Qed.

Global Instance eventually_compat : Proper ((equiv ==> iff) ==> equiv ==> iff) eventually.
Proof using .
intros P Q HPQ s s' Hs. split; intro eventually.
+ revert s' Hs. induction eventually; intros s' Hs.
  - apply Now. now rewrite <- (HPQ _ _ Hs).
  - apply Later. apply IHeventually. now inv Hs.
+ revert s Hs. induction eventually; intros s' Hs.
  - apply Now. now rewrite (HPQ _ _ Hs).
  - apply Later. apply IHeventually. now inv Hs.
Qed.


Global Instance instant2_compat : Proper ((equiv ==> equiv ==> iff) ==> equiv ==> equiv ==> iff) instant2.
Proof using . intros P Q HPQ ? ? Hs1 ? ? Hs2. unfold instant2. apply HPQ; apply Hs1 || apply Hs2. Qed.

Global Instance forever2_compat : Proper ((equiv ==> equiv ==> iff) ==> equiv ==> equiv ==> iff) forever2.
Proof using .
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split.
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs1 _ _ Hs2). match goal with H : forever2 _ _ _ |- _ => now inv H end.
  - inv Hs1. inv Hs2. match goal with H : forever2 P _ _ |- _ => inv H end. eapply Hrec; eassumption.
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite (HPQ _ _ Hs1 _ _ Hs2). match goal with H : forever2 _ _ _ |- _ => now inv H end.
  - inv Hs1. inv Hs2. match goal with H : forever2 Q _ _ |- _ => inv H end. eapply Hrec; eassumption.
Qed.

Global Instance eventually2_compat : Proper ((equiv ==> equiv ==> iff) ==> equiv ==> equiv ==> iff) eventually2.
Proof using .
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split; intro eventually2.
+ revert s1' s2' Hs1 Hs2. induction eventually2; intros s1' s2' Hs1 Hs2.
  - apply Now2. now rewrite <- (HPQ _ _ Hs1 _ _ Hs2).
  - apply Later2. inv Hs1. inv Hs2. now apply IHeventually2.
+ revert s1 s2 Hs1 Hs2. induction eventually2; intros s1' s2' Hs1 Hs2.
  - apply Now2. now rewrite (HPQ _ _ Hs1 _ _ Hs2).
  - apply Later2. inv Hs1. inv Hs2. now apply IHeventually2.
Qed.


Lemma instant_impl_compat : forall P Q : A -> Prop,
  (forall s, P s -> Q s) -> forall s, instant P s -> instant Q s.
Proof using . unfold instant. auto. Qed.

Lemma forever_impl_compat : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, forever P s -> forever Q s.
Proof using .
cofix Hrec. intros P Q HPQ s HP. constructor.
- inv HP. auto.
- inv HP. eapply Hrec; eauto.
Qed.

Lemma eventually_impl_compat : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, eventually P s -> eventually Q s.
Proof using .
intros P Q HPQ s HP. induction HP as [e HP | HP].
- apply Now. auto.
- now apply Later.
Qed.

Lemma instant2_impl_compat : forall P Q : A -> A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, instant2 P s1 s2 -> instant2 Q s1 s2.
Proof using . unfold instant2. auto. Qed.

Lemma forever2_impl_compat : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, forever2 P s1 s2 -> forever2 Q s1 s2.
Proof using .
cofix Hrec. intros P Q HPQ s1 s2 HP. constructor.
- inv HP. auto.
- inv HP. eapply Hrec; eauto.
Qed.

Lemma eventually2_impl_compat : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, eventually2 P s1 s2 -> eventually2 Q s1 s2.
Proof using .
intros P Q HPQ s1 s2 HP. induction HP as [e1 e2 HP | HP].
- apply Now2. auto.
- now apply Later2.
Qed.

(** Relation properties lifted to steams. *)

Global Instance instant2_refl R `{Reflexive _ R} : Reflexive (instant2 R).
Proof using . intro. simpl. reflexivity. Qed.

Global Instance instant2_sym R `{Symmetric _ R} : Symmetric (instant2 R).
Proof using . intros x y HR. simpl in *. now symmetry. Qed.

Global Instance instant2_trans R `{Transitive _ R} : Transitive (instant2 R).
Proof using . intros x y z ? ?. simpl in *. now transitivity (hd y). Qed.


Global Instance forever2_refl R `{Reflexive _ R} : Reflexive (forever2 R).
Proof using . coinduction Hrec. reflexivity. Qed.

Global Instance forever2_sym R `{Symmetric _ R} : Symmetric (forever2 R).
Proof using .
coinduction Hrec; match goal with H : forever2 _ _ _ |- _ => inv H end.
- now symmetry.
- assumption.
Qed.

Global Instance forever2_trans R `{Transitive _ R} : Transitive (forever2 R).
Proof using .
coinduction Hrec; match goal with H : forever2 _ _ _, H' : forever2 _ _ _ |- _ => inv H; inv H' end.
- now transitivity y.
- now transitivity (tl y).
Qed.


Global Instance eventually2_refl R `{Reflexive _ R} : Reflexive (eventually2 R).
Proof using . intro x. apply Now2. reflexivity. Qed.

Global Instance eventually2_sym R `{Symmetric _ R} : Symmetric (eventually2 R).
Proof using .
intros x y HR. induction HR.
- apply Now2. now symmetry.
- now apply Later2.
Qed.

(* It does not apprear to be transitive for lack of synchronisation of the streams. *)
Instance eventually2_trans R `{Transitive _ R} : Transitive (eventually2 R).
Proof. Abort.


Inductive until (P Q : t A -> Prop) (s : t A) : Prop :=
  | NotYet : P s -> until P Q (tl s) -> until P Q s
  | YesNow : Q s -> until P Q s.

Definition weak_until P Q s := forever P s \/ until P Q s.
End Streams.

(** Map on streams *)
Section Map.
Context {A B : Type}.

CoFixpoint map (f : A -> B) (s : t A) := cons (f (hd s)) (map f (tl s)).

Global Instance map_compat `{Setoid A} `{Setoid B} : Proper ((equiv ==> equiv) ==> equiv ==> equiv) map.
Proof using .
intros f g Hfg. hnf. simpl. cofix Hcorec. intros s1 s2 Hs. constructor; simpl.
- apply Hfg, Hs.
- apply Hcorec, Hs.
Qed.

Lemma map_cons : forall f x s, map f (cons x s) = cons (f x) (map f s).
Proof using . intros. apply stream_eq. Qed.

Lemma map_hd : forall f s, hd (map f s) = f (hd s).
Proof using . intros. now rewrite (stream_eq s). Qed.

Lemma map_tl : forall f s, map f (tl s) = tl (map f s).
Proof using . intros. now rewrite (stream_eq s). Qed.
End Map.
