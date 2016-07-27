(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Utf8.
Require Import Setoid.
Require Import Equalities.
Require Import Morphisms.
Require Import Rbase Rbasic_fun.
Require Import Pactole.Preliminary.
Require Import Pactole.Configurations.


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
  section :> T → T;
  retraction : T → T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.

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


(**********************)
(** *  Similarities  **)
(**********************)

Open Scope Z_scope.

(** Similarities are functions that change the way we move.
    Unlike bijections that only need a setoid, we need here a space.
    For convenience, we also add their center, that is the location 
    from which robots locally observe. *)
Module Make (Loc : DiscreteSpace).

Record t := {
  sim_f :> bijection Loc.eq;
  center : Loc.t;
  center_prop : Loc.eq (sim_f center) Loc.origin;
  dist_prop : forall x y, Loc.dist (sim_f x) (sim_f y) = Loc.dist x y}.

Definition eq sim1 sim2 := bij_eq sim1.(sim_f) sim2.(sim_f).

Global Instance eq_equiv : Equivalence eq.
Proof.
unfold eq. split.
+ intros [f c Hc Hk]. simpl. reflexivity.
+ intros [f cf Hcf Hkf] [g cg Hcg Hkg] Hfg. simpl in *. now symmetry.
+ intros [f cf Hcf Hkf] [g cg Hcg Hkg] [h ch Hch Hkh] ? ?. simpl in *. etransitivity; eassumption.
Qed.

Instance f_compat : Proper (eq ==> @bij_eq _ Loc.eq) sim_f.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

(** The identity similarity *)
Definition id : t.
refine {| sim_f := bij_id Loc.eq_equiv;
          center := Loc.origin;
          center_prop := reflexivity _ |}.
Proof. abstract (intros; auto). Defined.

Section Normed_Results.
(** The existence of homothecy and translation similarities (implied by these two hypotheses)
    is actually equivalent to defining a normed vector space. *)
Hypothesis translation_hypothesis : forall v x y, Loc.dist (Loc.add x v) (Loc.add y v) = Loc.dist x y.
Hypothesis rotation_hypothesis : forall x y, Loc.dist (Loc.opp x) (Loc.opp y) = Loc.dist x y.

(** The translation similarity *)
Lemma bij_translation_Inversion : forall v x y : Loc.t, Loc.eq (Loc.add x v) y ↔ Loc.eq (Loc.add y (Loc.opp v)) x.
Proof.
intros. split; intro Heq; rewrite Heq || rewrite <- Heq; rewrite <- Loc.add_assoc.
- now rewrite Loc.add_opp, Loc.add_origin.
- setoid_rewrite Loc.add_comm at 2. now rewrite Loc.add_opp, Loc.add_origin.
Qed.

Definition bij_translation (v : Loc.t) : bijection Loc.eq.
refine {|
  section := fun x => Loc.add x v;
  retraction := fun x => Loc.add x (Loc.opp v) |}.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ apply bij_translation_Inversion.
Defined.


Definition translation (v : Loc.t) : t.
refine {| sim_f := bij_translation v;
          center := Loc.opp v |}.
Proof.
+ simpl. abstract (now rewrite Loc.add_comm, Loc.add_opp).
+ simpl. auto.
Defined.

Global Instance translation_compat : Proper (Loc.eq ==> eq) translation.
Proof. intros u v Huv x y Hxy. simpl. now rewrite Huv, Hxy. Qed.

Lemma translation_origin : eq (translation Loc.origin) id.
Proof. intros x y Hxy. simpl. now rewrite Loc.add_origin. Qed.

(** the rotation similarity **)

Lemma bij_rotation_Inversion : forall x y : Loc.t, Loc.eq (Loc.opp x) y ↔ Loc.eq (Loc.opp y) x.
Proof.
intros.
split;intros Heq; rewrite <- Heq, Loc.opp_opp; reflexivity.
Qed.

Definition bij_rotation : bijection Loc.eq.
refine {|
  section := fun x => Loc.opp x;
  retraction := fun x => Loc.opp x |}.
Proof. intros; split; intros Heq; rewrite <- Heq, Loc.opp_opp; reflexivity. Defined.


Definition rotation : t.
refine {| sim_f := bij_rotation|}.
Proof.
+ simpl. rewrite Loc.opp_origin. reflexivity.
+ simpl. auto.
Defined.

Global Instance rotation_compat : Proper (eq) rotation.
Proof. intros u v Huv. simpl. now rewrite Huv. Qed.


(* (** The homothetic similarity *)
Lemma homothecy_Inversion : forall c ρ x y, ρ ≠ 0 ->
  Loc.eq (Loc.mul ρ (Loc.add x (Loc.opp c))) y ↔ Loc.eq (Loc.add (Loc.mul (/ ρ) y) c) x.
Proof.
intros. split; intro Heq; rewrite <- Heq; clear Heq.
- rewrite Loc.mul_morph, Rinv_l, Loc.mul_1; trivial.
  rewrite <- Loc.add_assoc. setoid_rewrite Loc.add_comm at 2.
  now rewrite Loc.add_opp, Loc.add_origin.
- repeat rewrite Loc.mul_distr_add. rewrite Loc.mul_morph. rewrite Rinv_r; trivial.
  rewrite Loc.mul_1, <- Loc.add_assoc. now rewrite Loc.mul_opp, Loc.add_opp, Loc.add_origin.
Qed.

 
 Definition bij_homothecy (c : Loc.t) (ρ : Z) (Hρ : ρ <> 0) : bijection Loc.eq.
refine {|
  section := fun x => Loc.mul ρ (Loc.add x (Loc.opp c));
  retraction := fun x => Loc.add (Loc.mul (/ρ) x) c |}.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ intros. now apply homothecy_Inversion.
Defined. 

Lemma bij_homothecy_zoom : forall c ρ (Hρ : ρ <> 0%Z) (x y : Loc.t),
  Loc.dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Zabs ρ * Loc.dist x y.
Proof. intros. cbn. rewrite homothecy_hypothesis. f_equal. apply translation_hypothesis. Qed.

Definition homothecy (c : Loc.t) (ρ : R) (Hρ : ρ <> 0) : t.
refine {|
  sim_f := bij_homothecy c Hρ;
  zoom := Rabs ρ;
  center := c |}.
Proof.
- simpl. abstract (now rewrite Loc.add_opp, Loc.mul_origin).
- exact (bij_homothecy_zoom c Hρ).
Defined.

Global Instance homothecy_compat :
  Proper (Loc.eq ==> @forall_relation _ _ (fun _ => full_relation ==> eq)) homothecy.
Proof. intros c1 c2 Hc ρ ? ? ? x y Hxy. simpl. now rewrite Hxy, Hc. Qed.

Lemma homothecy_translation : forall c (H10 : 1 <> 0), eq (homothecy c H10) (translation (Loc.opp c)).
Proof. intros c H10 x y Hxy. rewrite Hxy. simpl. now rewrite Loc.mul_1. Qed.
*)
End Normed_Results.
 
(** Composition of similarity *)

Definition compose (f g : t) : t.
refine {|
  sim_f := bij_compose _ f g;
  center := retraction g (retraction f Loc.origin) |}.
Proof.
+ simpl. abstract (now repeat rewrite section_retraction; autoclass).
+ simpl. abstract (intros; rewrite f.(dist_prop), g.(dist_prop); ring).
Defined.
Global Infix "∘" := compose (left associativity, at level 59).

Global Instance compose_compat : Proper (eq ==> eq ==> eq) compose.
Proof. intros f1 f2 Hf g1 g2 Hg x y Hxy. cbn. now rewrite Hxy, Hf, Hg. Qed.

Lemma compose_assoc : forall f g h, eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h x y Hxy. simpl. now rewrite Hxy. Qed.

(** Inverse of a similarity *)
Definition inverse (sim : t) : t.
refine {| sim_f := bij_inverse _ sim.(sim_f);
          center := sim Loc.origin |}.
Proof.
+ abstract (apply (retraction_section _)).
+ intros x y.
  rewrite <- sim.(dist_prop). simpl. repeat rewrite section_retraction; autoclass.
Defined.
Global Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat : Proper (eq ==> eq) inverse.
Proof. intros f g Hfg x y Hxy. simpl. rewrite Hxy. f_equiv. apply Hfg. Qed.

Lemma compose_inverse_l : forall sim : t, eq (sim ⁻¹ ∘ sim) id.
Proof. intros sim x y Hxy. simpl. now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r : forall sim : t, eq (sim ∘ (sim ⁻¹)) id.
Proof. intros sim x y Hxy. simpl. now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose : forall f g : t, eq ((f ∘ g) ⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g x y Hxy. simpl. rewrite Hxy. reflexivity. Qed.

Corollary injective : forall sim : t, Preliminary.injective Loc.eq Loc.eq sim.
Proof.
intros sim z t Heqf.
rewrite <- Loc.dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
assumption.
Qed.

End Make.
