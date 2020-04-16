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
Require Import Lra.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Spaces.EuclideanSpace.
Set Implicit Arguments.


(**********************)
(** *  Similarities  **)
(**********************)

Open Scope R_scope.

Section SimilarityDefinition.

Context {T : Type}.
Context `{RealMetricSpace T}.

(** Similarities are functions that multiply distances by a constant zoom.
    Unlike bijections that only need a setoid, we need here a metric space. *)
Record similarity := {
  sim_f :> bijection T;
  zoom : R;
  dist_prop : forall x y, dist (sim_f x) (sim_f y) = zoom * dist x y}.
(* Arguments similarity T {_} {_} {_} {_}. *)

Global Instance similarity_Setoid : Setoid similarity.
simple refine {| equiv := fun sim1 sim2 => equiv (sim_f sim1) (sim_f sim2) |}.
Proof.
* apply bij_Setoid.
* split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Global Instance f_compat : Proper (equiv ==> equiv) sim_f.
Proof using . intros sim1 sim2 Hsim ?. now apply Hsim. Qed.

Global Instance zoom_compat : Proper (equiv ==> equiv) zoom.
Proof using .
intros sim1 sim2 Hsim.
apply Rmult_eq_reg_r with (dist origin one).
+ now rewrite <- 2 dist_prop, Hsim.
+ rewrite dist_defined. intro. apply non_trivial. now symmetry.
Qed.

(** As similarities are defined as bijections, we can prove that k <> 0
    (this requires that the metric space is not trivial (i.e. has dimension > 0). *)
Lemma zoom_non_null : forall sim, sim.(zoom) <> 0.
Proof using .
intros sim Heq. apply non_trivial.
assert (Heqsim : equiv (sim one) (sim origin)).
{ now rewrite <- dist_defined, sim.(dist_prop), Heq, Rmult_0_l. }
rewrite sim.(Inversion) in Heqsim. rewrite <- Heqsim, <- sim.(Inversion). reflexivity.
Qed.

Lemma zoom_pos : forall sim, 0 < sim.(zoom).
Proof using .
intros sim. apply Rle_neq_lt.
- destruct sim as [f k Hk]. simpl.
  assert (Hnon_triv := non_trivial). specialize (Hk one origin).
  unfold complement in Hnon_triv. rewrite <- dist_defined in Hnon_triv.
  assert (Hdist := dist_nonneg one origin).
  generalize (dist_nonneg (f one) (f origin)).
  rewrite <- (Rmult_0_l (dist one origin)) at 1.
  rewrite Hk. apply Rmult_le_reg_r. apply Rle_neq_lt; auto.
- intro. now apply (zoom_non_null sim).
Qed.

Theorem injective : forall sim : similarity, Preliminary.injective equiv equiv sim.
Proof using .
intros sim z t Heqf.
rewrite <- dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
apply Rmult_integral in Heqf. destruct Heqf; trivial.
assert (Hsim := zoom_non_null sim). contradiction.
Qed.

(** The identity similarity *)
Definition id : similarity := {|
  sim_f := @Bijection.id T _;
  zoom := 1;
  dist_prop := ltac:(abstract (intros; simpl; now rewrite Rmult_1_l)) |}.

(** Composition of similarities *)
Definition comp (f g : similarity) : similarity.
refine {|
  sim_f := @compose (Bijection.bijection T) _ _ f g;
  zoom := f.(zoom) * g.(zoom); |}.
Proof. abstract (intros; simpl; rewrite f.(dist_prop), g.(dist_prop); ring). Defined.

Global Instance SimilarityComposition : Composition similarity.
refine {| compose := comp |}.
Proof. intros f1 f2 Hf g1 g2 Hg x. cbn. now rewrite Hf, Hg. Defined.

(* Global Instance compose_compat `{RealMetricSpace} : Proper (equiv ==> equiv ==> equiv) compose.
Proof. intros f1 f2 Hf g1 g2 Hg x. cbn. now rewrite Hf, Hg. Qed. *)

Lemma compose_assoc : forall f g h, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof using . repeat intro. reflexivity. Qed.

Lemma compose_id_l : forall sim, id ∘ sim == sim.
Proof using . intros sim x. simpl. reflexivity. Qed.

Lemma compose_id_r : forall sim, sim ∘ id == sim.
Proof using . intros sim x. simpl. reflexivity. Qed.

(** Inverse of a similarity *)
Definition inv (sim : similarity) : similarity.
refine {| sim_f := inverse sim.(sim_f);
          zoom := /sim.(zoom) |}.
Proof.
assert (sim.(zoom) <> 0) by apply zoom_non_null.
intros x y. apply Rmult_eq_reg_l with sim.(zoom); trivial.
rewrite <- sim.(dist_prop). simpl. repeat rewrite section_retraction; autoclass; []. now field.
Defined.

Global Instance SimilarityInverse : Inverse similarity.
refine {| inverse := inv |}.
Proof. intros f g Hfg x. simpl. now f_equiv. Defined.

(* Global Instance inverse_compat `{RealMetricSpace} : Proper (equiv ==> equiv) inv.
Proof. intros f g Hfg x. simpl. now f_equiv. Qed. *)

Lemma compose_inverse_l : forall sim : similarity, (sim ⁻¹ ∘ sim) == id.
Proof using . intros sim x. simpl. now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r : forall sim : similarity, sim ∘ (sim ⁻¹) == id.
Proof using . intros sim x. simpl. now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose : forall f g : similarity, (f ∘ g) ⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof using . intros f g x. simpl. reflexivity. Qed.

Lemma inverse_dist_prop : forall (sim : similarity) x y,
  dist ((sim ⁻¹) x) ((sim ⁻¹) y) = /(zoom sim) * dist x y.
Proof using . intros sim x y. rewrite dist_prop. now simpl. Qed.

(** Center of a similarity, that is, the point that gets mapped to the origin. *)
Definition center (sim : similarity) : T := sim⁻¹ origin.

Lemma center_prop : forall sim : similarity, sim (center sim) == origin.
Proof using . intro. unfold center. apply compose_inverse_r. Qed.

Global Instance center_compat : Proper (equiv ==> equiv) center.
Proof using . intros sim ? Hsim. apply (injective sim). now rewrite center_prop, Hsim, center_prop. Qed.

(* TODO: prove that similarities preserve barycenters *)
End SimilarityDefinition.
Arguments similarity T {_} {_} {_} {_}.


Section TranslationHomothecy.
Context {T : Type}.
Context `{rnsT : RealNormedSpace T}.

(** The translation similarity *)
Lemma bij_translation_Inversion : forall v x y : T, add x v == y ↔ add y (opp v) == x.
Proof using .
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
Proof using . intros. ring_simplify. apply dist_translation. Qed.

Definition translation (v : T) : similarity T.
refine {| sim_f := bij_translation v;
          zoom := 1 |}.
Proof. cbn -[dist]. abstract (intros; now rewrite dist_translation, Rmult_1_l). Defined.

Global Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof using . intros u v Huv x. simpl. now rewrite Huv. Qed.

Lemma translation_origin : translation origin == id.
Proof using . intro. simpl. now rewrite add_origin. Qed.

Lemma translation_inverse : forall t, inverse (translation t) == translation (opp t).
Proof using . intros t x. simpl. reflexivity. Qed.

(** The homothetic similarity *)
Lemma homothecy_Inversion : forall c ρ x y, ρ ≠ 0 ->
  add c (mul ρ (add x (opp c))) == y ↔ add (mul (/ ρ) (add y (opp c))) c == x.
Proof using .
intros. split; intro Heq; rewrite <- Heq; clear Heq.
- now rewrite (add_comm c), <- add_assoc, add_opp, add_origin, mul_morph,
              Rinv_l, mul_1, <- add_assoc, (add_comm _ c), add_opp, add_origin.
- repeat rewrite mul_distr_add, ?mul_morph. rewrite Rinv_r; trivial.
  now rewrite 2 mul_1, <- add_assoc, <- mul_distr_add, add_opp, mul_origin, add_origin,
              add_assoc, (add_comm c), <- add_assoc, add_opp, add_origin.
Qed.

Definition bij_homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : @bijection T _.
simple refine {|
  section := fun x => (c + ρ * (x - c))%VS;
  retraction := fun x => add (mul (/ρ) (add x (opp c))) c |}; autoclass.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ intros. now apply homothecy_Inversion.
Defined.

Lemma bij_homothecy_zoom : forall c ρ (Hρ : ρ <> 0%R) (x y : T),
  dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Rabs ρ * dist x y.
Proof using .
intros. cbn -[dist]. setoid_rewrite (add_comm c). rewrite dist_translation.
rewrite dist_homothecy. f_equal. apply dist_translation.
Qed.

Definition homothecy (c : T) (ρ : R) (Hρ : ρ <> 0) : similarity T.
refine {|
  sim_f := bij_homothecy c Hρ;
  zoom := Rabs ρ |}.
Proof.
abstract (cbn -[dist]; intros; now rewrite 2 (add_comm c), dist_translation,
                                           dist_homothecy, dist_translation).
Defined.

Global Instance homothecy_compat :
  Proper (equiv ==> @forall_relation _ _ (fun _ => full_relation ==> equiv)) homothecy.
Proof using . intros c1 c2 Hc ρ ? ? ? ?. simpl. now rewrite Hc. Qed.

Lemma homothecy_inverse : forall c ρ (Hρ : ρ <> 0),
  inverse (homothecy c Hρ) == homothecy c (Rinv_neq_0_compat ρ Hρ).
Proof using . simpl. intros. apply add_comm. Qed.

Lemma homothecy_ratio_1 : forall c (H10 : 1 <> 0), homothecy c H10 == id.
Proof using .
repeat intro. simpl.
now rewrite mul_1, add_comm, <- add_assoc, (add_comm _ c), add_opp, add_origin.
Qed.

Lemma homothecy_fixpoint : forall c ρ (Hρ : ρ <> 0), homothecy c Hρ c == c.
Proof using . intros. simpl. now rewrite add_opp, mul_origin, add_origin. Qed.

End TranslationHomothecy.
