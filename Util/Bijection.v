(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain               
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Require Import Utf8.
Require Import SetoidDec.
Require Import Pactole.Util.Coqlib.
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
Definition id := {|
  section := fun x => x;
  retraction := fun x => x;
  section_compat := fun x y Heq => Heq;
  Inversion := ltac:(easy) |}.

(** Composition of bijections *)
Definition compose (f g : bijection) : bijection.
refine {| section := fun x => f (g x);
          retraction := fun x => g.(retraction) (f.(retraction) x) |}.
Proof.
+ abstract (intros x y Hxy; now apply f.(section_compat), g.(section_compat)).
+ abstract (intros x y; now rewrite f.(Inversion), <- g.(Inversion)).
Defined.
Infix "∘" := compose (left associativity, at level 40).

Lemma compose_assoc : forall f g h : bijection, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. repeat intro. reflexivity. Qed.

(** Properties about inverse functions *)
Global Instance retraction_compat : Proper (equiv ==> (equiv ==> equiv)) retraction.
Proof. intros f g Hfg x y Hxy. now rewrite <- f.(Inversion), Hxy, Hfg, g.(Inversion). Qed.

Definition inverse (bij : bijection) : bijection.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Notation "bij ⁻¹" := (inverse bij) (at level 39).

Global Instance inverse_compat : Proper (equiv ==> equiv) inverse.
Proof. repeat intro. simpl. now f_equiv. Qed.

Lemma retraction_section : forall (bij : bijection) x, bij.(retraction) (bij.(section) x) == x.
Proof. intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary compose_inverse_l : forall (bij : bijection), bij ⁻¹ ∘ bij == id.
Proof. repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : bijection) x, bij.(section) (bij.(retraction) x) == x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary compose_inverse_r : forall (bij : bijection), bij ∘ bij ⁻¹ == id.
Proof. repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma inverse_compose : forall f g : bijection, (f ∘ g)⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. repeat intro. reflexivity. Qed.

(** Bijections are in particular injective. *)
Lemma injective : forall bij : bijection, injective equiv equiv bij.
Proof. intros bij x y Heq. now rewrite <- (retraction_section bij x), Heq, retraction_section. Qed.

End Bijections.

Module Notations.
Global Arguments bijection T {_}.
Global Infix "∘" := compose (left associativity, at level 40).
Global Notation "bij ⁻¹" := (inverse bij) (at level 39).
End Notations.
