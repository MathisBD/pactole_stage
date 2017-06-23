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
Require Import RelationClasses.
Require Import Pactole.Preliminary.


(* Replacement to the standard library on streams. *)


Set Implicit Arguments.


CoInductive t A : Type := cons : A -> t A -> t A.

Definition hd {A} (s : t A) := match s with | cons e _ => e end.
Definition tl {A} (s : t A) := match s with | cons _ s' => s' end.

CoFixpoint constant {A} (c : A) := cons c (constant c).

CoFixpoint alternate {A} (c1 c2 : A) := cons c1 (cons c2 (alternate c1 c2)).


(** Extensional equality on streams, up to a given equality on the stream elements. *)
(* TODO: define it as [forever (instant eqA)] *)
CoInductive eq {A} (eqA : relation A) (s1 s2: t A) : Prop :=
    StreamEq : eqA (hd s1) (hd s2) -> eq eqA (tl s1) (tl s2) -> eq eqA s1 s2.

Instance eq_refl {A : Type} (eqA : relation A) `{Reflexive _ eqA} : Reflexive (eq eqA).
Proof. coinduction Heq. reflexivity. Qed.

Instance eq_trans {A : Type} (eqA : relation A) `{Transitive _ eqA} : Transitive (eq eqA).
Proof.
coinduction Heq.
- transitivity (hd y); match goal with H : eq eqA _ _ |- _ => now inv H end.
- transitivity (tl y); match goal with H : eq eqA _ _ |- _ => now inv H end.
Qed.

Instance eq_sym {A : Type} (eqA : relation A) `{Symmetric _ eqA} : Symmetric (eq eqA).
Proof.
coinduction Heq.
- symmetry. match goal with H : eq eqA _ _ |- _ => now inv H end.
- match goal with H : eq eqA _ _ |- _ => now inv H end.
Qed.

Instance eq_equiv {A : Type} (eqA : relation A) `{Equivalence _ eqA} : Equivalence (eq eqA).
Proof. split; autoclass. Qed.

Instance hd_compat {A} (eqA : relation A) : Proper (eq eqA ==> eqA) hd.
Proof. intros s s' Hs. now inv Hs. Qed.

Instance tl_compat {A} (eqA : relation A) : Proper (eq eqA ==> eq eqA) tl.
Proof. intros s s' Hs. now inv Hs. Qed.

Instance constant_compat {A} (eqA : relation A) : Proper (eqA ==> eq eqA) constant.
Proof. unfold constant. now coinduction Heq. Qed.

Instance aternate_compat {A} (eqA : relation A) : Proper (eqA ==> eqA ==> eq eqA) alternate.
Proof. cofix Heq. do 2 (constructor; trivial). cbn. now apply Heq. Qed.

(** Logical operators on properties over streams. *)

Definition instant {A} (P : A -> Prop) := fun s => P (hd s).
Arguments instant {A} P s /.

Instance instant_compat {A} (eqA : relation A) : Proper ((eqA ==> iff) ==> eq eqA ==> iff) instant.
Proof. intros P Q HPQ s s' Hs. unfold instant. apply HPQ, Hs. Qed.

Lemma instant_impl_compat {A} : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, instant P s -> instant Q s.
Proof. unfold instant. auto. Qed.


CoInductive forever {A} (P : t A -> Prop) (s : t A) : Prop :=
  Always : P s -> forever P (tl s) -> forever P s.
Arguments Always {A} [P] [s] _ _.

Instance forever_compat {A} (eqA : relation A) : Proper ((eq eqA ==> iff) ==> eq eqA ==> iff) forever.
Proof.
intros P Q HPQ s s' Hs. split.
+ revert s s' Hs. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H. eapply Hrec; eassumption.
+ revert s s' Hs. coinduction Hrec.
  - rewrite (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H. eapply Hrec; eassumption.
Qed.

Lemma forever_impl_compat {A} : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, forever P s -> forever Q s.
Proof.
cofix Hrec. intros P Q HPQ s HP. constructor.
- inv HP. auto.
- inv HP. revert H0. now apply Hrec.
Qed.


Inductive eventually {A : Type} (P : t A -> Prop) (s : t A) : Prop :=
  | Now : P s -> eventually P s
  | Later : eventually P (tl s) -> eventually P s.
Arguments Now {A} [P] [s] _.
Arguments Later {A} [P] [s] _.

Instance eventually_compat {A} (eqA : relation A) : Proper ((eq eqA ==> iff) ==> eq eqA ==> iff) eventually.
Proof.
intros P Q HPQ s s' Hs. split; intro H.
+ revert s' Hs. induction H; intros s' Hs.
  - apply Now. now rewrite <- (HPQ _ _ Hs).
  - apply Later. apply IHeventually. now inv Hs.
+ revert s Hs. induction H; intros s' Hs.
  - apply Now. now rewrite (HPQ _ _ Hs).
  - apply Later. apply IHeventually. now inv Hs.
Qed.

Lemma eventually_impl_compat {A} : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, eventually P s -> eventually Q s.
Proof.
intros P Q HPQ s HP. induction HP as [e HP | HP].
- apply Now. auto.
- now apply Later.
Qed.

(** Logical operators on relations over streams. *)

Definition instant2 {A} (P : A -> A -> Prop) := fun s1 s2 => P (hd s1) (hd s2).
Arguments instant2 {A} P s1 s2 /.

Instance instant2_compat {A} (eqA : relation A) :
  Proper ((eqA ==> eqA ==> iff) ==> eq eqA ==> eq eqA ==> iff) instant2.
Proof. intros P Q HPQ ? ? Hs1 ? ? Hs2. unfold instant2. apply HPQ; apply Hs1 || apply Hs2. Qed.

Lemma instant2_impl_compat {A} : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, instant2 P s1 s2 -> instant2 Q s1 s2.
Proof. unfold instant2. auto. Qed.


CoInductive forever2 {A} (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
  Always2 : P s1 s2 -> forever2 P (tl s1) (tl s2) -> forever2 P s1 s2.
Arguments Always2 {A} [P] [s1] [s2] _ _.

Instance forever2_compat {A} (eqA : relation A) :
  Proper ((eq eqA ==> eq eqA ==> iff) ==> eq eqA ==> eq eqA ==> iff) forever2.
Proof.
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split.
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv Hs2. inv H. eapply Hrec; eassumption.
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv Hs2. inv H. eapply Hrec; eassumption.
Qed.

Lemma forever2_impl_compat {A} : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, forever2 P s1 s2 -> forever2 Q s1 s2.
Proof.
cofix Hrec. intros P Q HPQ s1 s2 HP. constructor.
- inv HP. auto.
- inv HP. revert H0. now apply Hrec.
Qed.


Inductive eventually2 {A : Type} (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
  | Now2 : P s1 s2 -> eventually2 P s1 s2
  | Later2 : eventually2 P (tl s1) (tl s2) -> eventually2 P s1 s2.
Arguments Now2 {A} [P] [s1] [s2] _.
Arguments Later2 {A} [P] [s1] [s2] _.

Instance eventually2_compat {A} (eqA : relation A) :
  Proper ((eq eqA ==> eq eqA ==> iff) ==> eq eqA ==> eq eqA ==> iff) eventually2.
Proof.
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split; intro H.
+ revert s1' s2' Hs1 Hs2. induction H; intros s1' s2' Hs1 Hs2.
  - apply Now2. now rewrite <- (HPQ _ _ Hs1 _ _ Hs2).
  - apply Later2. inv Hs1. inv Hs2. now apply IHeventually2.
+ revert s1 s2 Hs1 Hs2. induction H; intros s1' s2' Hs1 Hs2.
  - apply Now2. now rewrite (HPQ _ _ Hs1 _ _ Hs2).
  - apply Later2. inv Hs1. inv Hs2. now apply IHeventually2.
Qed.

Lemma eventually2_impl_compat {A} : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, eventually2 P s1 s2 -> eventually2 Q s1 s2.
Proof.
intros P Q HPQ s1 s2 HP. induction HP as [e1 e2 HP | HP].
- apply Now2. auto.
- now apply Later2.
Qed.

(** **  Operators [forever] and [eventually] skipping half the streams   **)


CoInductive next_forever {A} (P : t A -> Prop) (s : t A) : Prop :=
  next_Always : P s -> next_forever P (tl (tl s)) -> next_forever P s.
Arguments next_Always {A} [P] [s] _ _.

Instance next_forever_compat {A} (eqA : relation A) : Proper ((eq eqA ==> iff) ==> eq eqA ==> iff) next_forever.
Proof.
intros P Q HPQ s s' Hs. split.
+ revert s s' Hs. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H.
    apply (Hrec (tl (tl s)) (tl (tl s'))).
    now apply tl_compat.
    assumption.
+ revert s s' Hs. coinduction Hrec.
  - rewrite (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H. apply (Hrec (tl (tl s)) (tl (tl s'))).
    now apply tl_compat.
    assumption.
Qed.

Lemma next_forever_impl_compat {A} : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, next_forever P s -> next_forever Q s.
Proof.
cofix Hrec. intros P Q HPQ s HP. constructor.
- inv HP. auto.
- inv HP. revert H0. now apply Hrec.
Qed.


Inductive next_eventually {A : Type} (P : t A -> Prop) (s : t A) : Prop :=
| n_Now : P s -> next_eventually P s
| n_Later : next_eventually P (tl (tl s)) -> next_eventually P s.
Arguments n_Now {A} [P] [s] _.
Arguments n_Later {A} [P] [s] _.

Instance next_eventually_compat {A} (eqA : relation A) : Proper ((eq eqA ==> iff) ==> eq eqA ==> iff) next_eventually.
Proof.
intros P Q HPQ s s' Hs. split; intro H.
+ revert s' Hs. induction H; intros s' Hs.
  - apply n_Now. now rewrite <- (HPQ _ _ Hs).
  - apply n_Later. apply IHnext_eventually. now inv Hs; inv H1.
+ revert s Hs. induction H; intros s' Hs.
  - apply n_Now. now rewrite (HPQ _ _ Hs).
  - apply n_Later. apply IHnext_eventually. now inv Hs; inv H1.
Qed.

Lemma next_eventually_impl_compat {A} : forall P Q : t A -> Prop,
  (forall s, P s -> Q s) -> forall s, next_eventually P s -> next_eventually Q s.
Proof.
intros P Q HPQ s HP. induction HP as [e HP | HP].
- apply n_Now. auto.
- now apply n_Later.
Qed.


CoInductive next_forever2 {A} (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
  next_Always2 : P s1 s2 -> next_forever2 P (tl (tl s1)) (tl (tl s2)) -> next_forever2 P s1 s2.
Arguments next_Always {A} [P] [s] _ _.

Instance next_forever2_compat {A} (eqA : relation A) :
  Proper ((eq eqA ==> eq eqA ==> iff) ==> eq eqA ==> eq eqA ==> iff) next_forever2.
Proof.
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split.
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv H1. inv Hs2. inv H4. inv H.
    now apply (Hrec (tl (tl s1)) (tl (tl s1')) ltac:(auto) (tl (tl s2)) (tl (tl s2')) ltac:(auto)).
+ revert s1 s1' Hs1 s2 s2' Hs2. coinduction Hrec.
  - rewrite (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv H1. inv Hs2. inv H4. inv H.
    now apply (Hrec (tl (tl s1)) (tl (tl s1')) ltac:(auto) (tl (tl s2)) (tl (tl s2')) ltac:(auto)).
Qed.

Lemma next_forever2_impl_compat {A} : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, next_forever2 P s1 s2 -> next_forever2 Q s1 s2.
Proof.
cofix Hrec. intros P Q HPQ s1 s2 HP. constructor.
- inv HP. auto.
- inv HP. revert H0. now apply Hrec.
Qed.


Inductive next_eventually2 {A : Type} (P : t A -> t A -> Prop) (s1 s2 : t A) : Prop :=
| n_Now2 : P s1 s2 -> next_eventually2 P s1 s2
| n_Later2 : next_eventually2 P (tl (tl s1)) (tl (tl s2)) -> next_eventually2 P s1 s2.
Arguments n_Now2 {A} [P] [s1] [s2] _.
Arguments n_Later2 {A} [P] [s1] [s2] _.

Instance next_eventually2_compat {A} (eqA : relation A) :
  Proper ((eq eqA ==> eq eqA ==> iff) ==> eq eqA ==> eq eqA ==> iff) next_eventually2.
Proof.
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split; intro H.
+ revert s1' s2' Hs1 Hs2. induction H; intros s1' s2' Hs1 Hs2.
  - apply n_Now2. now rewrite <- (HPQ _ _ Hs1 _ _ Hs2).
  - apply n_Later2. inv Hs1. inv H1. inv Hs2. inv H4. now apply IHnext_eventually2.
+ revert s1 s2 Hs1 Hs2. induction H; intros s1' s2' Hs1 Hs2.
  - apply n_Now2. now rewrite (HPQ _ _ Hs1 _ _ Hs2).
  - apply n_Later2. inv Hs1. inv H1. inv Hs2. inv H4. now apply IHnext_eventually2.
Qed.

Lemma next_eventually2_impl_compat {A} : forall P Q : t A -> t A -> Prop,
  (forall s1 s2, P s1 s2 -> Q s1 s2) -> forall s1 s2, next_eventually2 P s1 s2 -> next_eventually2 Q s1 s2.
Proof.
intros P Q HPQ s1 s2 HP. induction HP as [e1 e2 HP | HP].
- apply n_Now2. auto.
- now apply n_Later2.
Qed.


Definition next_eq {A} (eqA : relation A) := next_forever2 (instant2 eqA).

Instance eq_next_eq_subrelation {A} (eqA : relation A) : subrelation (eq eqA) (next_eq eqA).
Proof.
coinduction Hrec.
- now inv H.
- inv H. now inv H1.
Qed.

Instance next_eq_refl {A : Type} (eqA : relation A) `{Reflexive _ eqA} : Reflexive (next_eq eqA).
Proof. coinduction Heq. destruct x. now unfold instant2. Qed.

Instance next_eq_trans {A : Type} (eqA : relation A) `{Transitive _ eqA} : Transitive (next_eq eqA).
Proof.
coinduction Heq; unfold instant2 in *.
- transitivity (hd y); match goal with H : next_eq eqA _ _ |- _ => now inv H end.
- transitivity (tl (tl y)); match goal with H : next_eq eqA _ _ |- _ => now inv H end.
Qed.

Instance next_eq_sym {A : Type} (eqA : relation A) `{Symmetric _ eqA} : Symmetric (next_eq eqA).
Proof.
coinduction Heq; unfold instant2 in *.
- symmetry. match goal with H : next_eq eqA _ _ |- _ => now inv H end.
- match goal with H : next_eq eqA _ _ |- _ => now inv H end.
Qed.

Instance next_eq_equiv {A : Type} (eqA : relation A) `{Equivalence _ eqA} : Equivalence (next_eq eqA).
Proof. split; autoclass. Qed.

Instance tl_next_compat {A} (eqA : relation A) : Proper (next_eq eqA ==> next_eq eqA) (fun s => tl (tl s)).
Proof. intros s s' Hs. now inv Hs. Qed.

Instance next_forever_next_compat {A} (eqA : relation A) :
  Proper ((next_eq eqA ==> iff) ==> next_eq eqA ==> iff) next_forever.
Proof.
intros P Q HPQ s s' Hs. split.
+ revert s s' Hs. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H. now apply (Hrec (tl (tl s)) (tl (tl s'))).
+ revert s s' Hs. coinduction Hrec.
  - rewrite (HPQ _ _ Hs). now inv H.
  - inv Hs. inv H. now apply (Hrec (tl (tl s)) (tl (tl s'))).
Qed.

Instance next_forever2_next_compat {A} (eqA : relation A) :
  Proper ((next_eq eqA ==> next_eq eqA ==> iff) ==> next_eq eqA ==> next_eq eqA ==> iff) next_forever2.
Proof.
intros P Q HPQ s1 s1' Hs1 s2 s2' Hs2. split.
+ revert s1 s1' s2 s2' Hs1 Hs2. coinduction Hrec.
  - rewrite <- (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv Hs2. inv H. revert H5. now apply Hrec.
+ revert s1 s1' s2 s2' Hs1 Hs2. coinduction Hrec.
  - rewrite (HPQ _ _ Hs1 _ _ Hs2). now inv H.
  - inv Hs1. inv Hs2. inv H. revert H5. now apply Hrec.
Qed.

