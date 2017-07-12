Require Import Equalities.
Require Import Morphisms.
Require Import Pactole.Preliminary.


Set Implicit Arguments.


(********************)
(** *  Bijections  **)
(********************)

(** Bijections on a type [T] with an equivalence relation [eqT] *)

Section Bijections.
Context (T : Type).
Context (eqT : T -> T -> Prop).
Context (HeqT : Equivalence eqT).

Record bijection := {
  section :> T -> T;
  retraction : T -> T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : forall x y, eqT (section x) y <-> eqT (retraction y) x}.

Definition bij_eq (f g : bijection) := (eqT ==> eqT)%signature f.(section) g.

Global Instance bij_eq_equiv : Equivalence bij_eq.
Proof. split.
+ intros f x y Hxy. apply section_compat. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

Global Existing Instance section_compat.

Global Instance section_full_compat : Proper (bij_eq ==> (eqT ==> eqT)) section.
Proof. intros f g Hfg x y Hxy. now apply Hfg. Qed.

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
Infix "∘" := bij_compose (left associativity, at level 59).

Lemma bij_compose_assoc : forall f g h : bijection, bij_eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h x y Hxy. rewrite Hxy. reflexivity. Qed.

(** Properties about inverse functions *)
Global Instance retraction_compat : Proper (bij_eq ==> (eqT ==> eqT)) retraction.
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

Definition bij_inverse (bij : bijection) : bijection.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Notation "bij ⁻¹" := (bij_inverse bij) (at level 99).

Lemma retraction_section : forall (bij : bijection) x, eqT (bij.(retraction) (bij.(section) x)) x.
Proof. intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary bij_inv_bij_id : forall (bij : bijection), bij_eq (bij ⁻¹ ∘ bij) bij_id.
Proof. repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : bijection) x, eqT (bij.(section) (bij.(retraction) x)) x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary inv_bij_bij_id : forall (bij : bijection),
  (eqT ==> eqT)%signature (fun x => bij (bij ⁻¹ x)) bij_id.
Proof. repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma injective_retraction : forall bij : bijection, injective eqT eqT bij -> injective eqT eqT (bij ⁻¹).
Proof.
intros bij Hinj x y Heq. rewrite <- (section_retraction bij x), Heq. simpl. now rewrite section_retraction.
Qed.

Lemma compose_inverse : forall f g : bijection, bij_eq ((f ∘ g)⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g x y Hxy. rewrite Hxy. reflexivity. Qed.

End Bijections.