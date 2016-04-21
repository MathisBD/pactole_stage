(* Complements to the standard library on streams. *)


Require Import Relations.
Require Import Morphisms.
Require Import RelationClasses.
Require Import Pactole.Preliminary.


Set Implicit Arguments.


CoInductive t A : Type := cons : A -> t A -> t A.

Definition hd {A} (s : t A) := match s with | cons e _ => e end.
Definition tl {A} (s : t A) := match s with | cons _ s' => s' end.

CoFixpoint constant {A} (c : A) := cons c (constant c).

CoFixpoint alternate {A} (c1 c2 : A) := cons c1 (cons c2 (alternate c1 c2)).


(** Extensional equality on streams, up to a given equality on the stream elements. *)
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

(** Logical operators on streams. *)

Definition instant {A} (P : A -> Prop) := fun s => P (hd s).

Instance instant_compat {A} (eqA : relation A) : Proper ((eqA ==> iff) ==> eq eqA ==> iff) instant.
Proof. intros P Q HPQ s s' Hs. unfold instant. apply HPQ, Hs. Qed.

Lemma instant_impl_compat {A} : forall P Q : t A -> Prop, (forall s, P s -> Q s) -> forall s, instant P s -> instant Q s.
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

Lemma forever_impl_compat {A} : forall P Q : t A -> Prop, (forall s, P s -> Q s) -> forall s, forever P s -> forever Q s.
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

Lemma eventually_impl_compat {A} : forall P Q : t A -> Prop, (forall s, P s -> Q s) -> forall s, eventually P s -> eventually Q s.
Proof.
intros P Q HPQ s HP. induction HP as [e HP | HP].
- apply Now. auto.
- now apply Later.
Qed.
