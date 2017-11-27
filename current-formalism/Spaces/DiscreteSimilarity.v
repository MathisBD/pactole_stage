(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)

Require Import Utf8.
Require Import SetoidClass.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Core.Configurations.
Require Import Pactole.Spaces.DiscreteSpace.
Require Import Pactole.Util.Bijection.


Set Implicit Arguments.


(**********************)
(** *  Similarities  **)
(**********************)

Open Scope Z_scope.

(** Similarities are functions that change the way we move.
    Unlike bijections that only need a setoid, we need here a space.
    For convenience, we also add their center, that is the location 
    from which robots locally observe. *)
Section DiscreteSimilarity.
Variable loc : Type.
Context `{Space : DiscreteSpace loc}.

Record similarity := {
  sim_f :> bijection loc;
  center : loc;
  center_prop : sim_f center == origin;
  dist_prop : forall x y, dist (sim_f x) (sim_f y) = dist x y}.

Instance similarity_Setoid : Setoid similarity := {
  equiv := fun sim1 sim2 => sim1.(sim_f) == sim2.(sim_f) }.
Proof. split.
+ intros [f c Hc Hk]. simpl. reflexivity.
+ intros [f cf Hcf Hkf] [g cg Hcg Hkg] Hfg. simpl in *. now symmetry.
+ intros [f cf Hcf Hkf] [g cg Hcg Hkg] [h ch Hch Hkh] ? ?. cbn [sim_f] in *. etransitivity; eassumption.
Defined.

Instance sim_f_compat : Proper (equiv ==> equiv) sim_f.
Proof. intros ? ? Heq. now apply Heq. Qed.

(** The identity similarity *)
Definition id : similarity := {|
  sim_f := @Bijection.id loc _;
  center := origin;
  center_prop := reflexivity _;
  dist_prop := ltac:(abstract (intros; auto)) |}.


Section Normed_Results.
(** The existence of homothecy and translation similarities (implied by these two hypotheses)
    is actually equivalent to defining a normed vector space. *)
Hypothesis translation_hypothesis : forall v x y, dist (add x v) (add y v) = dist x y.
Hypothesis rotation_hypothesis : forall x y, dist (opp x) (opp y) = dist x y.

(** The translation similarity *)
Lemma bij_translation_Inversion : forall v x y, add x v == y ↔ add y (opp v) == x.
Proof.
intros. split; intro Heq; rewrite Heq || rewrite <- Heq; rewrite <- add_assoc.
- now rewrite add_opp, add_origin.
- setoid_rewrite add_comm at 2. now rewrite add_opp, add_origin.
Qed.

Definition bij_translation (v : loc) : bijection loc.
refine {| section := fun x => @add loc _ _ Space x v;
          retraction := fun x => add x (opp v) |}.
Proof.
+ abstract (intros x y Hxy; now rewrite Hxy).
+ apply bij_translation_Inversion.
Defined.


Definition translation (v : loc) : similarity.
refine {| sim_f := bij_translation v;
          center := opp v |}.
Proof.
+ simpl. abstract (now rewrite add_comm, add_opp).
+ simpl. auto.
Defined.

Global Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof. intros u v Huv x. simpl. now rewrite Huv. Qed.

Lemma translation_origin : translation origin == id.
Proof. intro. simpl. apply add_origin. Qed.

(** The rotation similarity *)
Lemma bij_rotation_Inversion : forall x y : loc, opp x == y ↔ opp y == x.
Proof. split; intro Heq; rewrite <- Heq, opp_opp; reflexivity. Qed.

Definition bij_rotation : bijection loc.
refine {| section := fun x => opp x;
          retraction := fun x => opp x |}.
Proof.
+ repeat intro. now apply opp_compat.
+ apply bij_rotation_Inversion.
Defined.


Definition rotation : similarity.
refine {| sim_f := bij_rotation;
          center := origin |}.
Proof.
+ apply opp_origin.
+ apply rotation_hypothesis.
Defined.


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

Definition compose (f g : similarity) : similarity.
refine {| sim_f := Bijection.compose f g;
          center := retraction g (retraction f origin) |}.
Proof.
+ simpl. abstract (now repeat rewrite section_retraction; autoclass).
+ simpl. abstract (now intros; rewrite f.(dist_prop), g.(dist_prop)).
Defined.
Infix "∘" := compose (left associativity, at level 59).

Global Instance compose_compat : Proper (equiv ==> equiv ==> equiv) compose.
Proof. intros f1 f2 Hf g1 g2 Hg x. cbn. now rewrite Hf, Hg. Qed.

Lemma compose_assoc : forall f g h, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. repeat intro. reflexivity. Qed.

(** Inverse of a similarity *)
Definition inverse (sim : similarity) : similarity.
refine {| sim_f := Bijection.inverse sim.(sim_f);
          center := sim origin |}.
Proof.
+ abstract (apply (retraction_section _)).
+ intros x y. rewrite <- sim.(dist_prop). apply dist_compat; apply section_retraction.
Defined.
Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat : Proper (equiv ==> equiv) inverse.
Proof. repeat intro. simpl. now f_equiv. Qed.

Lemma compose_inverse_l : forall sim : similarity, sim ⁻¹ ∘ sim == id.
Proof. intros sim x. simpl. now rewrite retraction_section. Qed.

Lemma compose_inverse_r : forall sim : similarity, sim ∘ (sim ⁻¹) == id.
Proof. intros sim x. simpl. now rewrite section_retraction. Qed.

Lemma inverse_compose : forall f g : similarity, (f ∘ g) ⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. repeat intro. reflexivity. Qed.

Corollary injective : forall sim : similarity, Preliminary.injective equiv equiv sim.
Proof.
intros sim z t Heqf.
rewrite <- dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
assumption.
Qed.

End DiscreteSimilarity.
