Require Import Utf8.
Require Import Setoid.
Require Import Equalities.
Require Import Morphisms.
Require Import Rbase Rbasic_fun.
Require Import Pactole.Preliminary.
Require Import Pactole.Positions.


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
  Inversion := $(easy)$ |}.

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

Open Scope R_scope.

(** Similarities are functions that multiply distances by a constant zoom.
    Unlike bijections that only need a setoid, we need here a metric space.
    For convenience, we also add their center, that is the location from which robots locally observe. *)
Module Make (Loc : RealMetricSpace).

Record t := {
  sim_f :> bijection Loc.eq;
  zoom : R;
  center : Loc.t;
  center_prop : Loc.eq (sim_f center) Loc.origin;
  dist_prop : forall x y, Loc.dist (sim_f x) (sim_f y) = zoom * Loc.dist x y}.

Definition eq sim1 sim2 := bij_eq sim1.(sim_f) sim2.(sim_f).

Global Instance eq_equiv : Equivalence eq.
Proof. unfold eq. split.
+ intros [f k c Hc Hk]. simpl. reflexivity.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] Hfg. simpl in *. now symmetry.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] [h kh ch Hch Hkh] ? ?. simpl in *. etransitivity; eassumption.
Qed.

Instance f_compat : Proper (eq ==> @bij_eq _ Loc.eq) sim_f.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

(** As similarities are defined as bijections, we can prove that k <> 0
    (this requires that the metric space is not trivial (i.e. has dimension > 0). *)
Lemma zoom_non_null : forall sim, sim.(zoom) <> 0.
Proof.
intros sim Heq. destruct Loc.non_trivial as [x [y Htriv]]. apply Htriv.
assert (Heqsim : Loc.eq (sim x) (sim y)).
{ now rewrite <- Loc.dist_defined, sim.(dist_prop), Heq, Rmult_0_l. }
rewrite sim.(Inversion) in Heqsim. rewrite <- Heqsim, <- sim.(Inversion). reflexivity.
Qed.

Lemma zoom_pos : forall sim, 0 < sim.(zoom).
Proof.
intros sim. apply Preliminary.Rle_neq_lt.
- destruct sim as [f k c Hc Hk]. simpl. clear c Hc.
  destruct Loc.non_trivial as [x [y Hxy]]. specialize (Hk x y).
  rewrite <- Loc.dist_defined in Hxy.
  assert (Hdist := Loc.dist_pos x y).
  generalize (Loc.dist_pos (f x) (f y)).
  rewrite <- (Rmult_0_l (Loc.dist x y)) at 1. rewrite Hk. apply Rmult_le_reg_r. apply Rle_neq_lt; auto.
- intro. now apply (zoom_non_null sim).
Qed.

(** The identity bijection *)
Definition id : t.
refine {| sim_f := bij_id Loc.eq_equiv;
          zoom := 1;
          center := Loc.origin;
          center_prop := reflexivity _ |}.
Proof. abstract (intros; simpl; now rewrite Rmult_1_l). Defined.

(** The homothetic similarity *)
Lemma homothecy_Inversion : forall c ρ x y, ρ ≠ 0 ->
  Loc.eq (Loc.mul ρ (Loc.add x (Loc.opp c))) y ↔ Loc.eq (Loc.add (Loc.mul (/ ρ) y) c) x.
Proof.
intros. split; intro Heq; rewrite <- Heq; clear Heq.
- rewrite Loc.mul_morph, Rinv_l, Loc.mul_1; trivial.
  rewrite <- Loc.add_assoc. setoid_rewrite Loc.add_comm at 2.
  now rewrite Loc.add_opp, Loc.add_origin.
- repeat rewrite Loc.add_distr. rewrite Loc.mul_morph. rewrite Rinv_r; trivial.
  rewrite Loc.mul_1, <- Loc.add_assoc. now rewrite Loc.mul_opp, Loc.add_opp, Loc.add_origin.
Qed.

Definition bij_homothecy (c : Loc.t) (ρ : R) (Hρ : ρ <> 0) : bijection Loc.eq.
refine {|
  section := fun x => Loc.mul ρ (Loc.add x (Loc.opp c));
  retraction := fun x => Loc.add (Loc.mul (/ρ) x) c |}.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ intros. now apply homothecy_Inversion.
Defined.

Lemma bij_homothecy_zoom : forall c ρ (Hρ : ρ <> 0%R) (x y : Loc.t),
  Loc.dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Rabs ρ * Loc.dist x y.
Proof.
intros c ρ Hρ x y. cbn.
(*destruct (Rcase_abs (ρ * (x + - c) + - (ρ * (y + - c)))), (Rcase_abs (x + - y)), (Rcase_abs ρ); try field.
+ ring_simplify in r0. exfalso. revert r0. apply Rle_not_lt.
  replace (ρ * x - ρ * y) with (-ρ * - (x + -y)) by ring.
  rewrite <- Rmult_0_r with (-ρ). apply Rmult_le_compat_l; lra.
+ ring_simplify in r0. exfalso. revert r0. apply Rle_not_lt.
  replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring. rewrite <- Rmult_0_r with ρ. apply Rmult_le_compat_l; lra.
+ ring_simplify in r0. exfalso. revert r0. apply Rlt_not_ge.
  replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring. rewrite <- Rmult_0_r with ρ. apply Rmult_lt_compat_l; lra.
+ destruct (Rdec x y).
  - subst. ring.
  - ring_simplify in r0. exfalso. revert r0. apply Rlt_not_ge.
    replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring.
    rewrite <- Rmult_0_l with (x + - y). apply Rmult_lt_compat_r; lra.*)
Admitted.

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

Lemma translation_zoom : forall v x y : Loc.t, Loc.dist (Loc.add x v) (Loc.add y v) = 1 * Loc.dist x y.
Proof.
Admitted.

Definition translation (v : Loc.t) : t.
refine {| sim_f := bij_translation v;
          zoom := 1;
          center := Loc.opp v |}.
Proof.
+ simpl. abstract (now rewrite Loc.add_comm, Loc.add_opp).
+ simpl. apply translation_zoom.
Defined.

Global Instance translation_compat : Proper (Loc.eq ==> eq) translation.
Proof. intros u v Huv x y Hxy. simpl. now rewrite Huv, Hxy. Qed.

Lemma translation_origin : eq (translation Loc.origin) id.
Proof. intros x y Hxy. simpl. now rewrite Loc.add_origin. Qed.

Lemma homothecy_translation : forall c (H10 : 1 <> 0), eq (homothecy c H10) (translation (Loc.opp c)).
Proof. intros c H10 x y Hxy. rewrite Hxy. simpl. now rewrite Loc.mul_1. Qed.

(** Composition of similarity *)

Definition compose (f g : t) : t.
refine {|
  sim_f := bij_compose _ f g;
  zoom := f.(zoom) * g.(zoom);
  center := retraction g (retraction f Loc.origin) |}.
Proof.
+ simpl. abstract (now repeat rewrite section_retraction; refine _).
+ simpl. abstract (intros; rewrite f.(dist_prop), g.(dist_prop); ring).
Defined.
Global Infix "∘" := compose (left associativity, at level 59).

Lemma compose_assoc : forall f g h, eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h x y Hxy. simpl. now rewrite Hxy. Qed.

(** Inverse of a similarity *)
Definition inverse (sim : t) : t.
refine {| sim_f := bij_inverse _ sim.(sim_f);
          zoom := /sim.(zoom);
          center := sim Loc.origin |}.
Proof.
+ abstract (apply (retraction_section _)).
+ assert (sim.(zoom) <> 0) by apply zoom_non_null.
  intros x y. apply Rmult_eq_reg_l with sim.(zoom); trivial.
  rewrite <- sim.(dist_prop). simpl. repeat rewrite section_retraction; refine _. now field.
Defined.
Global Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat : Proper (eq ==> eq) inverse.
Proof. intros f g Hfg x y Hxy. simpl. rewrite Hxy. f_equiv. apply Hfg. Qed.

Lemma compose_inverse_l : forall sim : t, eq (sim ⁻¹ ∘ sim) id.
Proof. intros sim x y Hxy. simpl. now rewrite retraction_section; refine _. Qed.

Lemma compose_inverse_r : forall sim : t, eq (sim ∘ (sim ⁻¹)) id.
Proof. intros sim x y Hxy. simpl. now rewrite section_retraction; refine _. Qed.

Lemma inverse_compose : forall f g : t, eq ((f ∘ g) ⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g x y Hxy. simpl. rewrite Hxy. reflexivity. Qed.

Corollary injective : forall sim : t, Preliminary.injective Loc.eq Loc.eq sim.
Proof.
intros sim z t Heqf.
rewrite <- Loc.dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
apply Rmult_integral in Heqf. destruct Heqf; trivial.
assert (Hsim := zoom_non_null sim). contradiction.
Qed.

End Make.