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
Require Import Rbase Rbasic_fun.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Spaces.RealMetricSpaces.


Set Implicit Arguments.


(********************)
(** *  Bijections  **)
(********************)

(** Bijections on a type [T] with an equivalence relation [eqT] *)

Section Bijections.
Context (T : Type).
Context (HesT : Setoid T).

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


(**********************)
(** *  Similarities  **)
(**********************)

Open Scope R_scope.

(** Similarities are functions that multiply distances by a constant zoom.
    Unlike bijections that only need a setoid, we need here a metric space.
    For convenience, we also add their center, that is the location from which robots locally observe. *)

Record similarity T `{RealMetricSpace T} := {
  sim_f :> @bijection T _;
  zoom : R;
  center : T;
  center_prop : sim_f center == origin;
  dist_prop : forall x y, dist (sim_f x) (sim_f y) = zoom * dist x y}.
Arguments similarity T {_} {_} {_}.

Global Instance similarity_Setoid T `{RealMetricSpace T} : Setoid (similarity T) := {|
  equiv := fun sim1 sim2 => equiv (sim_f sim1) (sim_f sim2) |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Instance f_compat `{RealMetricSpace} : Proper (equiv ==> equiv) (@sim_f T _ _ _).
Proof. intros sim1 sim2 Hsim ?. now apply Hsim. Qed.

(** As similarities are defined as bijections, we can prove that k <> 0
    (this requires that the metric space is not trivial (i.e. has dimension > 0). *)
Lemma zoom_non_null `{RealMetricSpace} : forall sim, sim.(zoom) <> 0.
Proof.
intros sim Heq. apply non_trivial.
assert (Heqsim : equiv (sim unit) (sim origin)).
{ now rewrite <- dist_defined, sim.(dist_prop), Heq, Rmult_0_l. }
rewrite sim.(Inversion) in Heqsim. rewrite <- Heqsim, <- sim.(Inversion). reflexivity.
Qed.

Lemma zoom_pos `{RealMetricSpace} : forall sim, 0 < sim.(zoom).
Proof.
intros sim. apply Preliminary.Rle_neq_lt.
- destruct sim as [f k c Hc Hk]. simpl. clear c Hc.
  assert (Hnon_triv := non_trivial). specialize (Hk unit origin).
  rewrite <- dist_defined in Hnon_triv.
  assert (Hdist := dist_pos unit origin).
  generalize (dist_pos (f unit) (f origin)).
  rewrite <- (Rmult_0_l (dist unit origin)) at 1.
  rewrite Hk. apply Rmult_le_reg_r. apply Rle_neq_lt; auto.
- intro. now apply (zoom_non_null sim).
Qed.

(** The identity similarity *)
Definition id {T} `{RealMetricSpace T} : similarity T.
refine {| sim_f := bij_id _;
          zoom := 1;
          center := origin;
          center_prop := reflexivity _ |}.
Proof. abstract (intros; simpl; now rewrite Rmult_1_l). Defined.

Section Normed_Results.
(** The existence of homothecy and translation similarities (implied by these two hypotheses)
    is actually equivalent to defining a normed vector space. *)
Context (T : Type).
Context `(RealMetricSpace T).
Hypothesis translation_hypothesis : forall v x y : T, dist (add x v) (add y v) = dist x y.
Hypothesis homothecy_hypothesis : forall ρ x y, dist (mul ρ x) (mul ρ y) = Rabs ρ * dist x y.

(** The translation similarity *)
Lemma bij_translation_Inversion : forall v x y : T, add x v == y ↔ add y (opp v) == x.
Proof.
intros. split; intro Heq; rewrite Heq || rewrite <- Heq; rewrite <- add_assoc.
- now rewrite add_opp, add_origin.
- setoid_rewrite add_comm at 2. now rewrite add_opp, add_origin.
Qed.

Definition bij_translation (v : T) : @bijection T _.
refine {|
  section := fun x => add x v;
  retraction := fun x => add x (opp v) |}.
Proof.
+ now repeat intro; apply add_compat.
+ apply bij_translation_Inversion.
Defined.

Lemma translation_zoom : forall v x y : T, dist (add x v) (add y v) = 1 * dist x y.
Proof. intros. ring_simplify. apply translation_hypothesis. Qed.

Definition translation (v : T) : similarity T.
refine {| sim_f := bij_translation v;
          zoom := 1;
          center := opp v |}.
Proof.
+ simpl. abstract (now rewrite add_comm, add_opp).
+ simpl. apply translation_zoom.
Defined.

Global Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof. intros u v Huv x. simpl. now rewrite Huv. Qed.

Lemma translation_origin : translation origin == id.
Proof. intro. simpl. now rewrite add_origin. Qed.

(** The homothetic similarity *)
Lemma homothecy_Inversion : forall c ρ x y, ρ ≠ 0 -> mul ρ (add x (opp c)) == y ↔ add (mul (/ ρ) y) c == x.
Proof.
intros. split; intro Heq; rewrite <- Heq; clear Heq.
- rewrite mul_morph, Rinv_l, mul_1; trivial.
  rewrite <- add_assoc. setoid_rewrite add_comm at 2.
  now rewrite add_opp, add_origin.
- repeat rewrite mul_distr_add. rewrite mul_morph. rewrite Rinv_r; trivial.
  rewrite mul_1, <- add_assoc. now rewrite mul_opp, add_opp, add_origin.
Qed.

Definition bij_homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : @bijection T _.
refine {|
  section := fun x => mul ρ (add x (opp c));
  retraction := fun x => add (mul (/ρ) x) c |}.
Proof.
+ intros x y Hxy; now rewrite Hxy. (* TODO: make abstract work *)
+ intros. now apply homothecy_Inversion.
Defined.

Lemma bij_homothecy_zoom : forall c ρ (Hρ : ρ <> 0%R) (x y : T),
  dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Rabs ρ * dist x y.
Proof. intros. cbn. rewrite homothecy_hypothesis. f_equal. apply translation_hypothesis. Qed.

Definition homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : similarity T.
refine {|
  sim_f := bij_homothecy c Hρ;
  zoom := Rabs ρ;
  center := c |}.
Proof.
- simpl. abstract (now rewrite add_opp, mul_origin).
- exact (bij_homothecy_zoom c Hρ).
Defined.

Global Instance homothecy_compat :
  Proper (equiv ==> @forall_relation _ _ (fun _ => full_relation ==> equiv)) homothecy.
Proof. intros c1 c2 Hc ρ ? ? ? ?. simpl. now rewrite Hc. Qed.

Lemma homothecy_translation : forall c (H10 : 1 <> 0), homothecy c H10 == translation (opp c).
Proof. intros c H10 ?. simpl. now rewrite mul_1. Qed.

End Normed_Results.

(** Composition of similarity *)

Definition compose {T} `{RealMetricSpace T} (f g : similarity T) : similarity T.
refine {|
  sim_f := bij_compose f g;
  zoom := f.(zoom) * g.(zoom);
  center := retraction g (retraction f origin) |}.
Proof.
+ simpl. abstract (now repeat rewrite section_retraction; autoclass).
+ simpl. abstract (intros; rewrite f.(dist_prop), g.(dist_prop); ring).
Defined.
Global Infix "∘" := compose (left associativity, at level 40).

Global Instance compose_compat `{RealMetricSpace} : Proper (equiv ==> equiv ==> equiv) compose.
Proof. intros f1 f2 Hf g1 g2 Hg x. cbn. now rewrite Hf, Hg. Qed.

Lemma compose_assoc `{RealMetricSpace} : forall f g h, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. repeat intro. reflexivity. Qed.

(** Inverse of a similarity *)
Definition inverse {T} `{RealMetricSpace T} (sim : similarity T) : similarity T.
refine {| sim_f := bij_inverse sim.(sim_f);
          zoom := /sim.(zoom);
          center := sim origin |}.
Proof.
+ abstract (apply (retraction_section _)).
+ assert (sim.(zoom) <> 0) by apply zoom_non_null.
  intros x y. apply Rmult_eq_reg_l with sim.(zoom); trivial.
  rewrite <- sim.(dist_prop). simpl. repeat rewrite section_retraction; autoclass; []. now field.
Defined.
Global Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat `{RealMetricSpace} : Proper (equiv ==> equiv) inverse.
Proof. intros f g Hfg x. simpl. now f_equiv. Qed.

Lemma compose_inverse_l {T} `{RealMetricSpace T} : forall sim : similarity T, (sim ⁻¹ ∘ sim) == id.
Proof. intros sim x. simpl. now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r {T} `{RealMetricSpace T} : forall sim : similarity T, sim ∘ (sim ⁻¹) == id.
Proof. intros sim x. simpl. now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose {T} `{RealMetricSpace T} : forall f g : similarity T, (f ∘ g) ⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. intros f g x. simpl. reflexivity. Qed.

Corollary injective {T} `{RealMetricSpace T} : forall sim : similarity T, injective equiv equiv sim.
Proof.
intros sim z t Heqf.
rewrite <- dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
apply Rmult_integral in Heqf. destruct Heqf; trivial.
assert (Hsim := zoom_non_null sim). contradiction.
Qed.
