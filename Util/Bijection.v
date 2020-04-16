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

Global Instance bij_Setoid : Setoid bijection.
simple refine {| equiv := fun f g => forall x, f.(section) x == g x |}; auto; [].
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Global Instance section_full_compat : Proper (equiv ==> (equiv ==> equiv)) section.
Proof using . intros f g Hfg x y Hxy. rewrite Hxy. now apply Hfg. Qed.

Global Instance retraction_compat : Proper (equiv ==> (equiv ==> equiv)) retraction.
Proof using . intros f g Hfg x y Hxy. now rewrite <- f.(Inversion), Hxy, Hfg, g.(Inversion). Qed.

(** The identity bijection *)
Definition id := {|
  section := fun x => x;
  retraction := fun x => x;
  section_compat := fun x y Heq => Heq;
  Inversion := ltac:(easy) |}.

(** Composition of bijections *)
Definition comp (f g : bijection) : bijection.
refine {| section := fun x => f (g x);
          retraction := fun x => g.(retraction) (f.(retraction) x) |}.
Proof.
+ abstract (intros x y Hxy; now apply f.(section_compat), g.(section_compat)).
+ abstract (intros x y; now rewrite f.(Inversion), <- g.(Inversion)).
Defined.

Global Instance BijectionComposition : Composition bijection.
refine {| compose := comp |}.
Proof.
intros f1 f2 Hf g1 g2 Hg x. cbn -[equiv].
rewrite (Hf (g1 x)). f_equiv. apply Hg.
Defined.
(*
Global Instance compose_compat : Proper (equiv ==> equiv ==> equiv) compose.
Proof.
intros f1 f2 Hf g1 g2 Hg x. cbn -[equiv].
rewrite (Hf (g1 x)). f_equiv. apply Hg.
Qed.
*)
Lemma compose_assoc : forall f g h : bijection, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof using . repeat intro. reflexivity. Qed.

(** Properties about inverse functions *)
Definition inv (bij : bijection) : bijection.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Global Instance BijectionInverse : Inverse bijection.
refine {| inverse := inv |}.
Proof. repeat intro. simpl. now f_equiv. Defined.
(*
Global Instance inverse_compat : Proper (equiv ==> equiv) inverse.
Proof. repeat intro. simpl. now f_equiv. Qed.
*)
Lemma retraction_section : forall (bij : bijection) x, bij.(retraction) (bij.(section) x) == x.
Proof using . intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary compose_inverse_l : forall (bij : bijection), bij ⁻¹ ∘ bij == id.
Proof using . repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : bijection) x, bij.(section) (bij.(retraction) x) == x.
Proof using . intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary compose_inverse_r : forall (bij : bijection), bij ∘ bij ⁻¹ == id.
Proof using . repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma inverse_compose : forall f g : bijection, (f ∘ g)⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof using . repeat intro. reflexivity. Qed.

(** Bijections are in particular injective. *)
Lemma injective : forall bij : bijection, injective equiv equiv bij.
Proof using . intros bij x y Heq. now rewrite <- (retraction_section bij x), Heq, retraction_section. Qed.

End Bijections.

Arguments bijection T {_}.
Arguments section {_} {_} !_ x.
Arguments retraction {_} {_} !_ x.
