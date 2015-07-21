(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Robots.
Require Import Positions.


Module Type Sig (Location : MetricSpace)(N : Size)(Spect : Spectrum(Location)(N)).
  Module Names := Spect.Names.
  Module Pos := Spect.Pos.
  
  Record bijection {T : Type} {eqT} {Heq : @Equivalence T eqT} := {
    section :> T → T;
    retraction : T → T;
    section_compat : Proper (eqT ==> eqT) section;
    Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.
  Arguments bijection {T} {eqT} Heq.
  
  Notation "s ⁻¹" := (s.(retraction)) (at level 99).
  
  Definition bij_eq (bij1 bij2 : bijection Location.eq_equiv) :=
    (Location.eq ==> Location.eq)%signature bij1.(section) bij2.
  
  Parameter bij_eq_equiv : Equivalence bij_eq.
  
  (** Properties about inverse functions *)
  Parameter retraction_compat : Proper (bij_eq ==> (Location.eq ==> Location.eq)) retraction.
  Parameter bij_inv_bij : forall (bij : bijection Location.eq_equiv) x, Location.eq (bij ⁻¹ (bij x)) x.
  Parameter inv_bij_bij : forall (bij : bijection Location.eq_equiv) x, Location.eq (bij (bij ⁻¹ x)) x.
  Parameter bij_inv_bij_id : forall (bij : bijection Location.eq_equiv),
    (Location.eq ==> Location.eq)%signature (fun x => bij ⁻¹ (bij x)) Datatypes.id.
  Parameter inv_bij_bij_id : forall (bij : bijection Location.eq_equiv),
    (Location.eq ==> Location.eq)%signature (fun x => bij (bij ⁻¹ x)) Datatypes.id.
  Parameter injective_retraction : forall bij : bijection Location.eq_equiv,
    injective Location.eq Location.eq bij -> injective Location.eq Location.eq (bij ⁻¹).
  
  (** Similarities are functions that multiply distance by a constant ratio.
      For convenience, we also add their center, that is the location from which robots locally observe. *)
  Record similarity := {
    f :> @bijection Location.t _ _;
    ratio : R;
    center : Location.t;
    center_prop : f center = Location.origin;
    dist_prop : forall x y, Location.dist (f x) (f y) = (ratio * Location.dist x y)%R}.
  
  Definition sim_eq sim1 sim2 := bij_eq sim1.(f) sim2.(f).
  Declare Instance similarity_f_compat : forall sim, Proper bij_eq sim.(f).
  Declare Instance sim_eq_equiv : Equivalence sim_eq.
  
  (** As similarities are defined as bijections, we can prove that k <> 0
      as soon as we have 2 points, that is when the metric space has dimension > 0. *)
  Parameter sim_ratio_non_null : forall x y : Location.t, ~Location.eq x y -> forall sim, sim.(ratio) <> 0%R.
  Parameter sim_ratio_pos : forall x y : Location.t, ~Location.eq x y -> forall sim, (0 < sim.(ratio))%R.
  Parameter similarity_injective : forall x y : Location.t, ~Location.eq x y ->
    forall sim : similarity, Preliminary.injective Location.eq Location.eq sim.
  
  (** ** Good robots have a common program, which we call a robogram *)
  
  Record robogram := {
    pgm :> Spect.t → Location.t;
    pgm_compat : Proper (Spect.eq ==> Location.eq) pgm}.
  Existing Instance pgm_compat.
  
  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  Declare Instance req_equiv : Equivalence req.
  
  (** Lifting an equivalence relation to an option type. *)
  Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
    match xo, yo with
      | None, None => True
      | None, Some _ | Some _, None => False
      | Some x, Some y => eqT x y
    end.
  Declare Instance opt_eq_refl : forall T (R : relation T), Reflexive R -> Reflexive (opt_eq R).
  Declare Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
  
  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given position with a [demon] *)
  CoInductive execution :=
    NextExecution : Pos.t → execution → execution.
  
  (** *** Destructors for demons *)
  
  Definition execution_head (e : execution) : Pos.t :=
    match e with NextExecution pos _ => pos end.
  
  Definition execution_tail (e : execution) : execution :=
    match e with NextExecution _ e => e end.
  
  CoInductive eeq (e1 e2 : execution) : Prop :=
    | Ceeq : Pos.eq (execution_head e1) (execution_head e2) ->
             eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.
  
  Declare Instance eeq_equiv : Equivalence eeq.
  Declare Instance eeq_bisim : Bisimulation execution.
  Declare Instance execution_head_compat : Proper (eeq ==> Pos.eq) execution_head.
  Declare Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
End Sig.


Module Make (Location : MetricSpace)(N : Size)(Spect : Spectrum(Location)(N)) : Sig (Location)(N)(Spect).

Module Names := Spect.Names.
Module Pos := Spect.Pos.

(** ** Programs for good robots *)

(* TODO: put similarities into a separate file, with definition for the usual ones:
   translation, homothecy, rotation, symmetry, ... *)
Record bijection (T : Type) eqT (Heq : @Equivalence T eqT) := {
  section :> T → T;
  retraction : T → T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.

Notation "s ⁻¹" := (s.(retraction)) (at level 99).

Definition bij_eq (bij1 bij2 : bijection Location.eq_equiv) :=
  (Location.eq ==> Location.eq)%signature bij1.(section) bij2.

Instance bij_eq_equiv : Equivalence bij_eq.
Proof. split.
+ intros f x y Hxy. apply section_compat. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

(** Properties about inverse functions *)
Instance retraction_compat : Proper (bij_eq ==> (Location.eq ==> Location.eq)) (@retraction _ _ Location.eq_equiv).
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

Lemma bij_inv_bij : forall (bij : bijection Location.eq_equiv) x, Location.eq (bij ⁻¹ (bij x)) x.
Proof. intros bij x. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary inv_bij_bij : forall (bij : bijection Location.eq_equiv) x, Location.eq (bij (bij ⁻¹ x)) x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary bij_inv_bij_id : forall (bij : bijection Location.eq_equiv),
  (Location.eq ==> Location.eq)%signature (fun x => bij ⁻¹ (bij x)) Datatypes.id.
Proof. repeat intro. now rewrite bij_inv_bij. Qed.

Corollary inv_bij_bij_id : forall (bij : bijection Location.eq_equiv),
  (Location.eq ==> Location.eq)%signature (fun x => bij (bij ⁻¹ x)) Datatypes.id.
Proof. repeat intro. now rewrite inv_bij_bij. Qed.

Lemma injective_retraction : forall bij : bijection Location.eq_equiv,
  injective Location.eq Location.eq bij -> injective Location.eq Location.eq (bij ⁻¹).
Proof.
intros bij Hinj x y Heq. apply Hinj. rewrite bij.(Inversion), bij_inv_bij.
now rewrite <- bij.(Inversion), inv_bij_bij in Heq.
Qed.

(** Similarities are functions that multiply distance by a constant ratio.
    For convenience, we also add their center, that is the location from which robots locally observe. *)
Record similarity := {
  f :> @bijection Location.t _ _;
  ratio : R;
  center : Location.t;
  center_prop : f center = Location.origin;
  dist_prop : forall x y, Location.dist (f x) (f y) = (ratio * Location.dist x y)%R}.

Definition sim_eq sim1 sim2 := bij_eq sim1.(f) sim2.(f).

Instance similarity_f_compat : forall sim, Proper bij_eq sim.(f).
Proof.
intros sim ? ? Heq. rewrite <- Location.dist_defined in Heq |- *.
rewrite <- (Rmult_0_r sim.(ratio)), <- Heq. now apply dist_prop.
Qed.

Instance sim_eq_equiv : Equivalence sim_eq.
Proof. unfold sim_eq. split.
+ intros [f k c Hc Hk]. simpl. reflexivity.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] Hfg. simpl in *. now symmetry.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] [h kh ch Hch Hkh] ? ?. simpl in *. etransitivity; eassumption.
Qed.

(** As similarities are defined as bijections, we can prove that k <> 0
    as soon as we have 2 points, that is when the metric space has dimension > 0. *)
Lemma sim_ratio_non_null : forall x y : Location.t, ~Location.eq x y ->
  forall sim, sim.(ratio) <> 0%R.
Proof.
intros x y Hxy sim Heq. apply Hxy.
assert (Heqsim : Location.eq (sim x) (sim y)).
{ now rewrite <- Location.dist_defined, sim.(dist_prop), Heq, Rmult_0_l. }
rewrite sim.(Inversion) in Heqsim. rewrite <- Heqsim, <- sim.(Inversion). reflexivity.
Qed.

Lemma sim_ratio_pos : forall x y : Location.t, ~Location.eq x y ->
  forall sim, (0 < sim.(ratio))%R.
Proof.
intros x y Hxy sim. apply Preliminary.Rle_neq_lt.
- destruct sim as [f k c Hc Hk]. simpl. clear c Hc. specialize (Hk x y).
  rewrite <- Location.dist_defined in Hxy.
  assert (Hdist := Location.dist_pos x y).
  generalize (Location.dist_pos (f x) (f y)).
  rewrite <- (Rmult_0_l (Location.dist x y)) at 1. rewrite Hk. apply Rmult_le_reg_r. lra.
- intro. now apply (sim_ratio_non_null Hxy sim).
Qed.

Corollary similarity_injective : forall x y : Location.t, ~Location.eq x y ->
  forall sim : similarity, Preliminary.injective Location.eq Location.eq sim.
Proof.
intros x y Hxy sim z t Heqf.
rewrite <- Location.dist_defined in Heqf |- *. rewrite sim.(dist_prop) in Heqf.
apply Rmult_integral in Heqf. destruct Heqf; trivial.
assert (Hsim := sim_ratio_non_null Hxy sim). contradiction.
Qed.

Unset Implicit Arguments.

(** ** Good robots have a common program, which we call a robogram *)

Record robogram := {
  pgm :> Spect.t → Location.t;
  pgm_compat : Proper (Spect.eq ==> Location.eq) pgm}.

Global Existing Instance pgm_compat.

Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
+ intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
+ intros r1 r2 r3 H1 H2 x y Heq.
  rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
Qed.

(** ** Prelude for Demonic schedulers *)

(** Lifting an equivalence relation to an option type. *)
Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
  match xo, yo with
    | None, None => True
    | None, Some _ | Some _, None => False
    | Some x, Some y => eqT x y
  end.

Instance opt_eq_refl : forall T (R : relation T), Reflexive R -> Reflexive (opt_eq R).
Proof. intros T R HR [x |]; simpl; auto. Qed.

Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
Proof. split.
+ intros [x |]; simpl; reflexivity || auto.
+ intros [x |] [y |]; simpl; trivial; now symmetry.
+ intros [x |] [y |] [z |]; simpl; tauto || etransitivity; eassumption.
Qed.

(** ** Executions *)

(** Now we can [execute] some robogram from a given position with a [demon] *)
CoInductive execution :=
  NextExecution : Pos.t → execution → execution.


(** *** Destructors for demons *)

Definition execution_head (e : execution) : Pos.t :=
  match e with NextExecution pos _ => pos end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

CoInductive eeq (e1 e2 : execution) : Prop :=
  | Ceeq : Pos.eq (execution_head e1) (execution_head e2) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. split.
+ coinduction eeq_refl. reflexivity.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. intro.
  - inversion H. inversion H0. now transitivity (execution_head y id).
  - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
    now inversion H. now inversion H0.
Qed.

Instance eeq_bisim : Bisimulation execution.
Proof. exists eeq. apply eeq_equiv. Qed.

Instance execution_head_compat : Proper (eeq ==> Pos.eq) execution_head.
Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.

Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
Proof. intros e1 e2 He. now inversion He. Qed.

End Make.
