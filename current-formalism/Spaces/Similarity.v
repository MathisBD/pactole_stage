(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                           
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence         
                                                                          *)
(**************************************************************************)


Require Import Utf8.
Require Import SetoidDec.
Require Import Rbase Rbasic_fun.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Spaces.RealMetricSpace.
Set Implicit Arguments.


(**********************)
(** *  Similarities  **)
(**********************)

Open Scope R_scope.

(** Similarities are functions that multiply distances by a constant zoom.
    Unlike bijections that only need a setoid, we need here a metric space. *)
Record similarity T `{RealMetricSpace T} := {
  sim_f :> bijection T;
  zoom : R;
  dist_prop : forall x y, dist (sim_f x) (sim_f y) = zoom * dist x y}.
Arguments similarity T {_} {_} {_}.

Global Instance similarity_Setoid T `{RealMetricSpace T} : Setoid (similarity T) := {|
  equiv := fun sim1 sim2 => equiv (sim_f sim1) (sim_f sim2) |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Instance f_compat `{RealMetricSpace} : Proper (equiv ==> equiv) (@sim_f _ _ _ _).
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
- destruct sim as [f k Hk]. simpl.
  assert (Hnon_triv := non_trivial). specialize (Hk unit origin).
  unfold complement in Hnon_triv. rewrite <- dist_defined in Hnon_triv.
  assert (Hdist := dist_pos unit origin).
  generalize (dist_pos (f unit) (f origin)).
  rewrite <- (Rmult_0_l (dist unit origin)) at 1.
  rewrite Hk. apply Rmult_le_reg_r. apply Rle_neq_lt; auto.
- intro. now apply (zoom_non_null sim).
Qed.

Theorem injective {T} `{RealMetricSpace T} : forall sim : similarity T, Preliminary.injective equiv equiv sim.
Proof.
intros sim z t Heqf.
rewrite <- dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
apply Rmult_integral in Heqf. destruct Heqf; trivial.
assert (Hsim := zoom_non_null sim). contradiction.
Qed.

(** The identity similarity *)
Definition id {T} `{RealMetricSpace T} : similarity T := {|
  sim_f := @Bijection.id T _;
  zoom := 1;
  dist_prop := ltac:(intros; simpl; now rewrite Rmult_1_l) |}. (* TODO: make abstract work *)

Section Normed_Results.
(** The existence of homothecy and translation similarities (implied by these two hypotheses)
    is actually equivalent to defining a normed vector space. *)
Context (T : Type).
Context `{rmsT : RealMetricSpace T}.
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
          zoom := 1 |}.
Proof. simpl. abstract (intros; now rewrite translation_hypothesis, Rmult_1_l). Defined.

Global Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof. intros u v Huv x. simpl. now rewrite Huv. Qed.

Lemma translation_origin : translation origin == id.
Proof. intro. simpl. now rewrite add_origin. Qed.

Lemma translation_inverse : forall t, inverse (translation t) == translation (opp t).
Proof. intros t x. simpl. reflexivity. Qed.

(** The homothetic similarity *)
Lemma homothecy_Inversion : forall c ρ x y, ρ ≠ 0 -> add c (mul ρ (add x (opp c))) == y ↔ add (mul (/ ρ) (add y (opp c))) c == x.
Proof.
intros. split; intro Heq; rewrite <- Heq; clear Heq.
- now rewrite (add_comm c), <- add_assoc, add_opp, add_origin, mul_morph,
              Rinv_l, mul_1, <- add_assoc, (add_comm _ c), add_opp, add_origin.
- repeat rewrite mul_distr_add, ?mul_morph. rewrite Rinv_r; trivial.
  now rewrite 2 mul_1, <- add_assoc, <- mul_distr_add, add_opp, mul_origin, add_origin,
              add_assoc, (add_comm c), <- add_assoc, add_opp, add_origin.
Qed.

Definition bij_homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : @bijection T _.
refine {|
  section := fun x => @add _ _ _ rmsT c (@mul _ _ _ rmsT ρ (@add _ _ _ rmsT x (@opp _ _ _ rmsT c)));
  retraction := fun x => add (mul (/ρ) (add x (opp c))) c |}.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ intros. now apply homothecy_Inversion.
Defined.

Lemma bij_homothecy_zoom : forall c ρ (Hρ : ρ <> 0%R) (x y : T),
  dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Rabs ρ * dist x y.
Proof.
intros. cbn. setoid_rewrite (add_comm c). rewrite translation_hypothesis.
rewrite homothecy_hypothesis. f_equal. apply translation_hypothesis.
Qed.

Definition homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : similarity T.
refine {|
  sim_f := bij_homothecy c Hρ;
  zoom := Rabs ρ |}.
Proof.
abstract (simpl; intros; now rewrite 2 (add_comm c), translation_hypothesis,
                                     homothecy_hypothesis, translation_hypothesis).
Defined.

Global Instance homothecy_compat :
  Proper (equiv ==> @forall_relation _ _ (fun _ => full_relation ==> equiv)) homothecy.
Proof. intros c1 c2 Hc ρ ? ? ? ?. simpl. now rewrite Hc. Qed.

Lemma homothecy_inverse : forall c ρ (Hρ : ρ <> 0),
  inverse (homothecy c Hρ) == homothecy c (Rinv_neq_0_compat ρ Hρ).
Proof. simpl. intros. apply add_comm. Qed.

Lemma homothecy_ratio_1 : forall c (H10 : 1 <> 0), homothecy c H10 == id.
Proof. repeat intro. simpl. now rewrite mul_1, add_comm, <- add_assoc, (add_comm _ c), add_opp, add_origin. Qed.

End Normed_Results.

(** Composition of similarities *)

Definition compose {T} `{RealMetricSpace T} (f g : similarity T) : similarity T.
refine {|
  sim_f := compose f g;
  zoom := f.(zoom) * g.(zoom); |}.
Proof. simpl. abstract (intros; rewrite f.(dist_prop), g.(dist_prop); ring). Defined.
Global Infix "∘" := compose (left associativity, at level 40).

Global Instance compose_compat `{RealMetricSpace} : Proper (equiv ==> equiv ==> equiv) compose.
Proof. intros f1 f2 Hf g1 g2 Hg x. cbn. now rewrite Hf, Hg. Qed.

Lemma compose_assoc `{RealMetricSpace} : forall f g h, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. repeat intro. reflexivity. Qed.

Lemma compose_id_l `{RealMetricSpace} : forall sim, id ∘ sim == sim.
Proof. intros sim x. simpl. reflexivity. Qed.

Lemma compose_id_r `{RealMetricSpace} : forall sim, sim ∘ id == sim.
Proof. intros sim x. simpl. reflexivity. Qed.

(** Inverse of a similarity *)
Definition inverse {T} `{RealMetricSpace T} (sim : similarity T) : similarity T.
refine {| sim_f := inverse sim.(sim_f);
          zoom := /sim.(zoom) |}.
Proof.
assert (sim.(zoom) <> 0) by apply zoom_non_null.
intros x y. apply Rmult_eq_reg_l with sim.(zoom); trivial.
rewrite <- sim.(dist_prop). simpl. repeat rewrite section_retraction; autoclass; []. now field.
Defined.
Global Notation "s ⁻¹" := (inverse s) (at level 39).

Global Instance inverse_compat `{RealMetricSpace} : Proper (equiv ==> equiv) inverse.
Proof. intros f g Hfg x. simpl. now f_equiv. Qed.

Lemma compose_inverse_l {T} `{RealMetricSpace T} : forall sim : similarity T, (sim ⁻¹ ∘ sim) == id.
Proof. intros sim x. simpl. now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r {T} `{RealMetricSpace T} : forall sim : similarity T, sim ∘ (sim ⁻¹) == id.
Proof. intros sim x. simpl. now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose {T} `{RealMetricSpace T} : forall f g : similarity T, (f ∘ g) ⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. intros f g x. simpl. reflexivity. Qed.

(* Center of a similarity, that is, the point that gets mapped to the origin. *)
Definition center {T} `{RealMetricSpace T} (sim : similarity T) : T := sim⁻¹ origin.

Lemma center_prop {T} `{RealMetricSpace T} : forall sim : similarity T, sim (center sim) == origin.
Proof. intro. unfold center. apply compose_inverse_r. Qed.

Instance center_compat `{RealMetricSpace} : Proper (equiv ==> equiv) (@center _ _ _ _).
Proof. intros sim ? Hsim. apply (injective sim). now rewrite center_prop, Hsim, center_prop. Qed.


Module Notations.
Global Arguments similarity T {_} {_} {_}.
Notation similarity := similarity.
Global Infix "∘" := compose (left associativity, at level 40).
Global Notation "sim ⁻¹" := (inverse sim) (at level 39).
End Notations.
