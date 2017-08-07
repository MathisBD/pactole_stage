(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Set Implicit Arguments.


(********************)
(** *  Bijections  **)
(********************)

(** Bijections on a type [T] with an equivalence relation [eqT] *)

Section Bijections.
Context (T : Type).
Context {HeqT : Setoid T}.

Record bijection := {
  section :> T → T;
  retraction : T → T;
  section_compat : Proper (equiv ==> equiv) section;
  Inversion : ∀ x y, section x == y ↔ retraction y == x}.
Global Existing Instance section_compat.

Global Instance bij_Setoid : Setoid bijection := {| equiv := fun f g => forall x, f.(section) x == g x |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Global Instance section_full_compat : Proper (equiv ==> (equiv ==> equiv)) section.
Proof. intros f g Hfg x y Hxy. rewrite Hxy. now apply Hfg. Qed.

(** The identity bijection *)
Definition bij_id := {|
  section := fun x => x;
  retraction := fun x => x;
  section_compat := fun x y Heq => Heq;
  Inversion := ltac:(easy) |}.

(** Composition of bijections *)
Definition bij_compose (f g : bijection) : bijection.
refine {| section := fun x => f (g x);
          retraction := fun x => g.(retraction) (f.(retraction) x) |}.
Proof.
+ abstract (intros x y Hxy; now apply f.(section_compat), g.(section_compat)).
+ abstract (intros x y; now rewrite f.(Inversion), <- g.(Inversion)).
Defined.
Infix "∘" := bij_compose (left associativity, at level 40).

Lemma bij_compose_assoc : forall f g h : bijection, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. repeat intro. reflexivity. Qed.

(** Properties about inverse functions *)
Global Instance retraction_compat : Proper (equiv ==> (equiv ==> equiv)) retraction.
Proof. intros f g Hfg x y Hxy. now rewrite <- f.(Inversion), Hxy, Hfg, g.(Inversion). Qed.

Definition bij_inverse (bij : bijection) : bijection.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Notation "bij ⁻¹" := (bij_inverse bij) (at level 99).

Lemma retraction_section : forall (bij : bijection) x, bij.(retraction) (bij.(section) x) == x.
Proof. intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary bij_inv_bij_id : forall (bij : bijection), bij ⁻¹ ∘ bij == bij_id.
Proof. repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : bijection) x, bij.(section) (bij.(retraction) x) == x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary inv_bij_bij_id : forall (bij : bijection),
  (equiv ==> equiv)%signature (fun x => bij (bij ⁻¹ x)) bij_id.
Proof. repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma injective_retraction : forall bij : bijection, injective equiv equiv bij -> injective equiv equiv (bij ⁻¹).
Proof.
intros bij Hinj x y Heq. rewrite <- (section_retraction bij x), Heq. simpl. now rewrite section_retraction.
Qed.

Lemma compose_inverse : forall f g : bijection, (f ∘ g)⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. repeat intro. reflexivity. Qed.

End Bijections.

Arguments bijection T {_}.
