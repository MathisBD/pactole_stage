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

Record t := {
  section :> T -> T;
  retraction : T -> T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : forall x y, eqT (section x) y <-> eqT (retraction y) x}.

Definition eq (f g : t) := (eqT ==> eqT)%signature f.(section) g.

Global Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros f x y Hxy. apply section_compat. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

Global Existing Instance section_compat.

Global Instance section_full_compat : Proper (eq ==> (eqT ==> eqT)) section.
Proof. intros f g Hfg x y Hxy. now apply Hfg. Qed.

(** The identity bijection *)
Definition id := {|
  section := fun x => x;
  retraction := fun x => x;
  section_compat := fun x y Heq => Heq;
  Inversion := ltac:(easy) |}.

(** Composition of bijections *)
Definition compose (f g : t) : t.
refine {| section := fun x => f (g x);
          retraction := fun x => g.(retraction) (f.(retraction) x) |}.
Proof.
+ abstract (intros x y Hxy; now apply f.(section_compat), g.(section_compat)).
+ abstract (intros x y; now rewrite f.(Inversion), <- g.(Inversion)).
Defined.
Infix "∘" := compose (left associativity, at level 59).

Lemma compose_assoc : forall f g h : t, eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h x y Hxy. rewrite Hxy. reflexivity. Qed.

(** Properties about inverse functions *)
Global Instance retraction_compat : Proper (eq ==> (eqT ==> eqT)) retraction.
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

Definition inverse (bij : t) : t.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Notation "bij ⁻¹" := (inverse bij) (at level 99).

Lemma retraction_section : forall (bij : t) x, eqT (bij.(retraction) (bij.(section) x)) x.
Proof. intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary bij_inv_id : forall (bij : t), eq (bij ⁻¹ ∘ bij) id.
Proof. repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : t) x, eqT (bij.(section) (bij.(retraction) x)) x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary inv_bij_id : forall (bij : t),
  (eqT ==> eqT)%signature (fun x => bij (bij ⁻¹ x)) id.
Proof. repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma injective_retraction : forall bij : t, injective eqT eqT bij -> injective eqT eqT (bij ⁻¹).
Proof.
intros bij Hinj x y Heq. rewrite <- (section_retraction bij x), Heq. simpl. now rewrite section_retraction.
Qed.

Lemma compose_inverse : forall f g : t, eq ((f ∘ g)⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g x y Hxy. rewrite Hxy. reflexivity. Qed.

End Bijections.
