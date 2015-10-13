(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Pactole.CommonFormalism.
Require Pactole.RigidFormalism.
Require Import Pactole.Gathering.InR.SortingR.
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.Lexprod.
Require Import Pactole.Gathering.InR2.R2geometry.


Import Permutation.
Set Implicit Arguments.

Function target_triangle (pt1 pt2 pt3 : R2.t) : R2.t :=
  let typ := classify_triangle pt1 pt2 pt3 in
  match typ with
  | Equilateral => barycenter_3_pts pt1 pt2 pt3
  | Isosceles p => p
  | Scalene => opposite_of_max_side pt1 pt2 pt3
  end.

Lemma target_triangle_compat : forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    target_triangle pt1 pt2 pt3 = target_triangle pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' hpermut.
  generalize (classify_triangle_compat hpermut).
  intro h_classify.
  functional induction (target_triangle pt1 pt2 pt3)
  ;generalize h_classify; intro h_classify'
  ;symmetry in h_classify';rewrite e in h_classify';unfold target_triangle
  ;rewrite h_classify';auto.
  - apply barycenter_compat;auto.
  - apply opposite_of_max_side_compat;auto.
Qed.



(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR2.

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter nG: nat.
Hypothesis nG_conf : (3 <= nG)%nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.


(** The spectrum is a multiset of configurations *)
Module Spect := MultisetSpectrum.Make(R2)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 2, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Common := CommonRealFormalism.Make(R2)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(R2)(N)(Spect)(Common).
Close Scope R_scope.
Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

Lemma Config_list_alls : forall pt, Spect.Config.list (fun _ => pt) = alls pt N.nG.
Proof.
intro. rewrite Config.list_spec, map_cst.
setoid_rewrite Spect.Names.names_length. unfold N.nB. now rewrite plus_0_r.
Qed.

Lemma map_sim_support : forall (sim : Sim.t) s,
  Permutation (Spect.support (Spect.map sim s)) (map sim (Spect.support s)).
Proof.
intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_support.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.empty.
Proof.
intros conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.multiset_empty in Heq.
assert (Hlgth:= Spect.Config.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
unfold N.nB, N.nG in *.
cut (3 <= 0). omega.
rewrite Hlgth at 2. rewrite plus_0_r. apply nG_conf.
Qed.

(* FIXME: These three definitions: gathered_at, gather and WillGather
   should be shared by all our proofs about gathering (on Q, R, R2,
   for impossibility and possibility proofs). Shouldn't they be in a
   module? We could even add a generic notion of forbidden
   configurations. *)


(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (conf : Config.t) := forall g : Names.G, conf (Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive gather (pt: R2.t) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> gather pt (execution_tail e) -> gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive willGather (pt : R2.t) (e : execution) : Prop :=
  | Now : gather pt e -> willGather pt e
  | Later : willGather pt (execution_tail e) -> willGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these configurations as [forbidden]. *)
Definition forbidden (config : Config.t) :=
  Nat.Even N.nG /\ N.nG >=2 /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : R2.t, willGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R2.t, willGather pt (execute r d config).

(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(* A location is determined by distances to 3 points. *)
(*
Lemma dist_case : forall x y, R2.dist x y = x - y \/ R2.dist x y = y - x.
Proof.
unfold R.dist, Rdef.dist. intros x y. destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. lra.t
- apply Rabs_left in Hlt. lra.
Qed.

Lemma dist_locate : forall x y k, R.dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.
*)
Lemma GPS : forall x y z t1 t2, x <> y -> y <> z -> x <> z ->
  R2.dist t1 x = R2.dist t2 x -> R2.dist t1 y = R2.dist t2 y -> R2.dist t1 z = R2.dist t2 z -> t1 = t2.
Proof.
intros x y z t1 t2 Hxy Hyz Hxz Hx Hy Hz.
Admitted.
Arguments GPS x y z t1 t2 _ _ _ _ _ _ : clear implicits.

Lemma diff_0_1 : ~R2.eq (0, 0) (0, 1).
Proof. intro Heq. inversion Heq. now apply R1_neq_R0. Qed.

Lemma three_fixpoints_is_id : forall sim : Sim.t,
  (exists pt1 pt2 pt3 : R2.t, pt1 <> pt2 /\ pt1 <> pt3 /\ pt2 <> pt3
                           /\ sim pt1 = pt1 /\ sim pt2 = pt2 /\ sim pt3 = pt3) ->
  Sim.eq sim Sim.id.
Proof.
intros sim [pt1 [pt2 [pt3 [Hneq12 [Hneq23 [Hneq13 [Hpt1 [Hpt2 Hpt3]]]]]]]] x y Hxy.
assert (Hzoom : sim.(Sim.zoom) = 1).
{ apply (Rmult_eq_reg_r (R2.dist pt1 pt2)). rewrite <- sim.(Sim.dist_prop).
  - rewrite Hpt1, Hpt2. ring.
  - rewrite R2.dist_defined. assumption. }
rewrite Hxy. apply (GPS pt1 pt2 pt3); trivial.
- rewrite <- Hpt1 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
- rewrite <- Hpt2 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
- rewrite <- Hpt3 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
Qed.

(** Definition of rotations *)

Definition rotate_bij (θ : R) : Similarity.bijection R2.eq.
refine {|
  Similarity.section := fun r => (cos θ * fst r - sin θ * snd r, sin θ * fst r + cos θ * snd r);
  Similarity.retraction := fun r => (cos (-θ) * fst r - sin (-θ) * snd r, sin (-θ) * fst r + cos (-θ) * snd r) |}.
Proof.
unfold R2.eq, R2def.eq.
abstract (intros xy xy'; split; intro; subst; destruct xy as [x y] || destruct xy' as [x y]; simpl;
rewrite Rtrigo1.cos_neg, Rtrigo1.sin_neg; f_equal; ring_simplify ; do 2 rewrite <- Rfunctions.Rsqr_pow2;
rewrite <- (Rmult_1_l x) at 3 || rewrite <- (Rmult_1_l y) at 3; rewrite <- (Rtrigo1.sin2_cos2 θ); ring).
Defined.

Lemma arith : forall (θ : R) (x y : R2.t),
  (cos θ)² * (fst x)² - 2 * (cos θ)² * fst x * fst y + (cos θ)² * (snd x)² -
  2 * (cos θ)² * snd x * snd y + (cos θ)² * (fst y)² + (cos θ)² * (snd y)² +
  (fst x)² * (sin θ)² - 2 * fst x * (sin θ)² * fst y + (sin θ)² * (snd x)² -
  2 * (sin θ)² * snd x * snd y + (sin θ)² * (fst y)² + (sin θ)² * (snd y)² =
  (fst x)² - 2 * fst x * fst y + (snd x)² - 2 * snd x * snd y + (fst y)² + (snd y)².
Proof.
(* AACtactics should help with rewriting by sin2_cos2 here *)
Admitted.


Definition rotate (θ : R) : Sim.t.
refine {|
  Sim.sim_f := rotate_bij θ;
  Sim.zoom := 1;
  Sim.center := (0, 0) |}.
Proof.
+ simpl. unfoldR2. abstract(f_equal; field).
+ unfoldR2. intros. rewrite Rmult_1_l. f_equal. simpl.
repeat rewrite Rfunctions.Rsqr_pow2; ring_simplify; repeat rewrite <- Rfunctions.Rsqr_pow2.
apply arith.
Defined.

Lemma rotate_inverse : forall θ, Sim.eq ((rotate θ)⁻¹) (rotate (-θ)).
Proof. intros θ x y Hxy. now rewrite Hxy. Qed.

Lemma rotate_mul_comm : forall θ k u, R2.eq (rotate θ (R2.mul k u)) (R2.mul k (rotate θ u)).
Proof. intros θ k [x y]. unfoldR2. simpl. f_equal; field. Qed.

Lemma rotate_opp_comm : forall θ u, R2.eq (rotate θ (R2.opp u)) (R2.opp (rotate θ u)).
Proof. intros θ [? ?]. unfoldR2. simpl. f_equal; field. Qed.

Lemma rotate_add_distr : forall θ u v, R2.eq (rotate θ (R2.add u v)) (R2.add (rotate θ u) (rotate θ v)).
Proof. intros θ [? ?] [? ?]. unfoldR2. simpl. f_equal; field. Qed.

(** A similarity in R² is described by its ratio, center and rotation angle. *)
Theorem similarity_in_R2 : forall sim : Sim.t, exists θ,
  forall x, sim x = R2.mul sim.(Sim.zoom) (rotate θ (R2.add x (R2.opp sim.(Sim.center)))).
Proof.
intro sim. assert (Hkpos : 0 < sim.(Sim.zoom)) by apply Sim.zoom_pos.
destruct sim as [f k c Hc Hk]. simpl in *. unfoldR2 in Hc.

Admitted.

Corollary inverse_similarity_in_R2 : forall (sim : Sim.t) θ,
  (forall x, sim x = sim.(Sim.zoom) * (rotate θ (x + (- sim.(Sim.center)))))%R2 ->
  (forall x, R2.eq ((sim ⁻¹) x) ((/sim.(Sim.zoom)) *
                                  (rotate (-θ) (x + (sim.(Sim.zoom) * rotate θ sim.(Sim.center)))))%R2).
Proof.
intros sim θ Hdirect x. cbn -[rotate].
rewrite <- sim.(Similarity.Inversion). rewrite Hdirect. clear Hdirect.
assert (Sim.zoom sim <> 0) by apply Sim.zoom_non_null.
setoid_rewrite <- rotate_mul_comm. rewrite R2.add_distr. rewrite R2.mult_morph.
replace (Sim.zoom sim * / Sim.zoom sim) with 1 by (now field). rewrite R2.mul_1.
repeat rewrite rotate_add_distr. rewrite <- rotate_inverse.
(* Does not work! Sniff...
match goal with |- context[(rotate θ) ((rotate θ ⁻¹) ?x)] => idtac "found";
change ((rotate θ) ((rotate θ ⁻¹) x)) with (Sim.compose (rotate θ) (rotate θ ⁻¹) x) end *)
change ((rotate θ) ((rotate θ ⁻¹) x)) with (Sim.compose (rotate θ) (rotate θ ⁻¹) x).
change ((rotate θ) ((rotate θ ⁻¹) (Sim.zoom sim *  (rotate θ) (Sim.center sim))%R2))
  with (Sim.compose (rotate θ) (rotate θ ⁻¹) (Sim.zoom sim * (rotate θ) (Sim.center sim))%R2).
rewrite Sim.compose_inverse_r.
unfoldR2. destruct x as [x1 x2], sim as [f k [c1 c2] ? ?]; simpl in *. f_equal; field.
Qed.


Lemma sim_Minjective : forall (sim : Sim.t), MMultiset.Preliminary.injective R2.eq R2.eq sim.
Proof. apply Sim.injective. Qed.

Hint Immediate sim_Minjective.

Instance forbidden_compat : Proper (Config.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [? [pt1 [pt2 [Hneq Hpt]]]]];(split;[|split]); trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

(* cf algo in 1D, should be in the multiset library *)
Lemma max_mult_similarity_invariant : forall (sim : Sim.t) s, Spect.max_mult (Spect.map sim s) = Spect.max_mult s.
Proof.
intros. apply Spect.max_mult_map_injective_invariant.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

Corollary max_similarity : forall (sim : Sim.t),
  forall s, Spect.eq (Spect.max (Spect.map sim s)) (Spect.map sim (Spect.max s)).
Proof.
intros. apply Spect.max_map_injective.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

Lemma support_non_nil : forall config, Spect.support (!! config) <> nil.
Proof. intros config Habs. rewrite Spect.support_nil in Habs. apply (spect_non_nil _ Habs). Qed.

Lemma support_max_non_nil : forall config, Spect.support (Spect.max (!! config)) <> nil.
Proof. intros config Habs. rewrite Spect.support_nil, Spect.max_empty in Habs. apply (spect_non_nil _ Habs). Qed.

Lemma max_morph : forall (sim : Sim.t) s, Spect.eq (Spect.max (Spect.map sim s)) (Spect.map sim (Spect.max s)).
Proof.
intros f s. apply Spect.max_map_injective.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(* Safe to use only when SEC is well-defined, ie when robots are not gathered. *)
Function target (s : Spect.t) : R2.t :=
  let l := Spect.support s in
  let sec := List.filter (on_circle (SEC l)) l in
  match sec with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* gathered *)
    | pt1 :: pt2 :: nil => R2.middle pt1 pt2
    | pt1 :: pt2 :: pt3 :: nil => (* triangle cases *)
      target_triangle pt1 pt2 pt3
    | _ => (* general case *) center (SEC l)
  end.

Instance target_compat : Proper (Spect.eq ==> Logic.eq) target.
Proof.
intros s1 s2 Hs. unfold target.
assert (Hperm : Permutation (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1))
                            (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))).
{ rewrite <- PermutationA_Leibniz. etransitivity.
  - apply (filter_PermutationA_compat _); refine _. now rewrite Hs.
  - rewrite filter_extensionality_compat; try reflexivity.
    intros x y Hxy. subst. now rewrite Hs. }
destruct (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
+ apply Permutation_nil in Hperm. now rewrite Hperm.
+ apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
+ apply Permutation_length_2_inv in Hperm.
  destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial.
  unfold R2.middle. now rewrite R2.add_comm.
+ assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) =3%nat) by now rewrite <- Hperm.
  destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
    as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
  apply target_triangle_compat;assumption.
+ assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) = 4 + length l)%nat
    by now rewrite <- Hperm.
  destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
    as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
  now rewrite Hs.
Qed.

Definition SECT (s : Spect.t) : list R2.t :=
  let l := Spect.support s in
  target s :: List.filter (on_circle (SEC l)) l.

Instance SECT_compat : Proper (Spect.eq ==> @Permutation _) SECT.
Proof.
intros s1 s2 Hs. unfold SECT. rewrite Hs at 1. constructor.
etransitivity.
- rewrite <- PermutationA_Leibniz. apply (filter_PermutationA_compat _); refine _. rewrite Hs. reflexivity.
- rewrite filter_extensionality_compat; try reflexivity.
  intros ? ? ?. subst. now rewrite Hs.
Qed.

Definition SECT_cardinal s :=
  Spect.cardinal (Spect.filter (fun x => if List.in_dec R2.eq_dec x (SECT s) then true else false) s).

Instance SECT_cardinal_compat : Proper (Spect.eq ==> Logic.eq) SECT_cardinal.
Proof.
intros s1 s2 Hs. unfold SECT_cardinal. f_equiv. rewrite Hs.
apply Spect.filter_extensionality_compat.
- intros x y Hxy. now rewrite Hxy.
- intro x. destruct (in_dec R2.eq_dec x (SECT s1)), (in_dec R2.eq_dec x (SECT s2));
  trivial; rewrite Hs in *; contradiction.
Qed.

Definition is_clean (s : Spect.t) : bool :=
  if inclA_bool _ R2.eq_dec (Spect.support s) (SECT s) then true else false.

Instance is_clean_compat : Proper (Spect.eq ==> Logic.eq) is_clean.
Proof.
intros ? ? Heq. unfold is_clean.
destruct (inclA_bool _ R2.eq_dec (Spect.support x) (SECT x)) eqn:Hx,
         (inclA_bool _ R2.eq_dec (Spect.support y) (SECT y)) eqn:Hy;
  trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff in *.
+ elim Hy. intros e Hin. rewrite <- Heq in Hin.
  apply SECT_compat in Heq. rewrite <- PermutationA_Leibniz in Heq.
  rewrite <- Heq. now apply Hx.
+ elim Hx. intros e Hin. rewrite Heq in Hin.
  apply SECT_compat in Heq. rewrite <- PermutationA_Leibniz in Heq.
  rewrite Heq. now apply Hy.
Qed.

Definition gatherR2_pgm (s : Spect.t) : R2.t :=
  match Spect.support (Spect.max s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* majority *)
    | _ :: _ :: _ =>
      if is_clean s then target s (* reduce *)
      else if mem R2.eq_dec (0, 0) (SECT s) then (0, 0) else target s (* clean *)
  end.

Instance gatherR2_pgm_compat : Proper (Spect.eq ==> R2.eq) gatherR2_pgm.
Proof.
intros s1 s2 Hs. unfold gatherR2_pgm.
assert (Hsize : length (Spect.support (Spect.max s1)) = length (Spect.support (Spect.max s2))).
{ f_equiv. rewrite <- PermutationA_Leibniz. now do 2 f_equiv. }
destruct (Spect.support (Spect.max s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support (Spect.max s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ apply Spect.max_compat, Spect.support_compat in Hs. rewrite Hs1, Hs2 in Hs.
  rewrite PermutationA_Leibniz in Hs. apply Permutation_length_1_inv in Hs. now inversion Hs.
+ rewrite Hs. destruct (is_clean s2).
  - now f_equiv.
  - destruct (mem R2.eq_dec (0, 0) (SECT s1)) eqn:Hin,
             (mem R2.eq_dec (0, 0) (SECT s2)) eqn:Hin';
    rewrite ?mem_true_iff, ?mem_false_iff, ?InA_Leibniz in *;
    try (reflexivity || (rewrite Hs in Hin; contradiction)). now f_equiv.
Qed.

Definition gatherR2 : robogram := {| pgm := gatherR2_pgm |}.

(** **  Decreasing measure ensuring termination  **)

(** Global measure: lexicgraphic order on the index of the type of config + some specific measure:
    ]  Gathered: no need
   0]  Majority tower: # robots not on majority tower
   1]  Non-isosceles triangle and c = SEC ∪ DEST: # robots not on DEST
   2]  Non-isosceles triangle and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   1'] Isosceles triangle not equilateral and c = SEC ∪ DEST: # robots not on DEST
   2'] Isosceles triangle not equilateral and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   3]  Equilateral triangle and c = SEC ∪ DEST: # robots not on DEST
   4]  Equilateral triangle and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   5]  General case ($|\SEC| \geq 4$) and c = SEC ∪ DEST: # robots not on DEST
   6]  General case ($|\SEC| \geq 4$) and c <> SECT$: # robots not on SEC ∪ DEST
*)

Close Scope R_scope.

Definition measure_reduce (s : Spect.t) := N.nG - s[target s].
Definition measure_clean (s : Spect.t) := N.nG - SECT_cardinal s.

Function measure (s : Spect.t) : nat * nat :=
  match Spect.support (Spect.max s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => (0, N.nG -  s[pt]) (* majority *)
    | _ :: _ :: _ =>
      let l := Spect.support s in
      let sec := List.filter (on_circle (SEC l)) l in
      match sec with
        | nil | _ :: nil => (0, 0) (* impossible cases *)
        | pt1 :: pt2 :: pt3 :: nil =>
          match classify_triangle pt1 pt2 pt3 with (* triangle cases *)
            | Equilateral => if is_clean s then (3, measure_reduce s) else (4, measure_clean s)
            | Isosceles vertex => if is_clean s then (1, measure_reduce s) else (2, measure_clean s)
            | Scalene => if is_clean s then (1, measure_reduce s) else (2, measure_clean s)
          end
        | _ => (* general case *) if is_clean s then (5, measure_reduce s) else (6, measure_clean s)
      end
  end.

Instance measure_reduce_compat : Proper (Spect.eq ==> Logic.eq) measure_reduce.
Proof. intros ? ? Heq. unfold measure_reduce. now rewrite Heq. Qed.

Instance measure_clean_compat : Proper (Spect.eq ==> Logic.eq) measure_clean.
Proof. intros ? ? Heq. unfold measure_clean. now rewrite Heq. Qed.

Instance measure_compat : Proper (Spect.eq ==> Logic.eq) measure.
Proof.
intros s1 s2 Hs. unfold measure.
assert (Hsize : length (Spect.support (Spect.max s1)) = length (Spect.support (Spect.max s2))).
{ f_equiv. rewrite <- PermutationA_Leibniz. now do 2 f_equiv. }
destruct (Spect.support (Spect.max s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support (Spect.max s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ rewrite Hs. repeat f_equal.
  rewrite <- (PermutationA_1 _). rewrite <- Hs1, <- Hs2. rewrite Hs. reflexivity.
+ clear -Hs.
  assert (Hperm : Permutation (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1))
                              (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))).
  { rewrite <- PermutationA_Leibniz. etransitivity.
    - apply (filter_PermutationA_compat _); refine _. now rewrite Hs.
    - rewrite filter_extensionality_compat; try reflexivity.
      intros x y Hxy. subst. now rewrite Hs. }
  destruct (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
  - apply Permutation_nil in Hperm. now rewrite Hperm.
  - apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
  - apply Permutation_length_2_inv in Hperm.
    destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial;
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) =3%nat) by now rewrite <- Hperm.
    destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
      as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite (classify_triangle_compat Hperm).
    destruct (classify_triangle b1 b2 b3); rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) = 4 + length l)%nat
      by now rewrite <- Hperm.
    destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
      as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
Qed.


Definition lt_config x y := lexprod lt lt (measure (!! x)) (measure (!! y)).

Lemma wf_lt_conf: well_founded lt_config.
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply wf_lexprod;apply lt_wf.
Qed.

Instance lt_conf_compat: Proper (Config.eq ==> Config.eq ==> iff) lt_config.
Proof.
  intros conf1 conf1' heq1 conf2 conf2' heq2.
  unfold lt_config.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Definition map_triangle_type f t :=
  match t with
  | Isosceles p => Isosceles (f p)
  | _ => t
  end.

Definition sim_circle (sim:Sim.t) c :=
  {| center := sim c.(center) ; radius := sim.(Sim.zoom) * (c.(radius)) |}.

Lemma classify_triangle_morph :
  forall (sim : Sim.t) pt1 pt2 pt3, classify_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = map_triangle_type sim (classify_triangle pt1 pt2 pt3).
Proof.
  intros sim pt1 pt2 pt3.
  unfold classify_triangle at 1.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *; try apply Sim.zoom_non_null.
  functional induction (classify_triangle pt1 pt2 pt3);
  repeat rewrite ?e, ?e0, ?e1, ?(sim.(Sim.dist_prop)), ?Rdec_bool_mult_l; try reflexivity;
  try apply Sim.zoom_non_null.
Qed.

Lemma on_circle_morph :
  forall (sim : Sim.t) pt c, on_circle (sim_circle sim c) (sim pt) = on_circle c pt.
Proof.
  intros sim pt c.
  unfold on_circle at 1.
  unfold sim_circle.
  simpl.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *;try apply Sim.zoom_non_null.
  reflexivity.
Qed.

Lemma enclosing_circle_morph :
  forall (sim : Sim.t) c l, enclosing_circle (sim_circle sim c) (List.map sim l) <-> enclosing_circle c l.
Proof.
  intros sim c l.
  unfold enclosing_circle.
  unfold sim_circle.
  simpl.
  setoid_rewrite in_map_iff.
  split;intro h.
  - intros x h'.
    specialize (h (sim x)).
    setoid_rewrite (sim.(Sim.dist_prop)) in h.
    apply Rmult_le_reg_l in h;auto.
    + apply Sim.zoom_pos.
    + eauto.
  - intros x H.
    destruct H as [x' [hsim hIn]].
    subst.
    rewrite (sim.(Sim.dist_prop)).
    eapply Rmult_le_compat_l in h;eauto.
    apply Rlt_le, Sim.zoom_pos.
Qed.

(* TODO *)
Axiom SEC_morph : forall (sim:Sim.t) l, SEC (List.map sim l) = sim_circle sim (SEC l).

Lemma barycenter_3_morph: forall (sim : Sim.t) pt1 pt2 pt3,
  barycenter_3_pts (sim pt1) (sim pt2) (sim pt3) = sim (barycenter_3_pts pt1 pt2 pt3).
Proof.
  intros sim pt1 pt2 pt3.
  unfold barycenter_3_pts.
Admitted.

Lemma opposite_of_max_side_morph : forall (sim : Sim.t) pt1 pt2 pt3,
  opposite_of_max_side (sim pt1) (sim pt2) (sim pt3) = sim (opposite_of_max_side pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold opposite_of_max_side.
repeat rewrite (sim.(Sim.dist_prop)).
assert (Hconf : (0 < Sim.zoom sim)%R) by apply Sim.zoom_pos.
repeat rewrite Rle_bool_mult_l; trivial.
repeat match goal with
  | |- context[Rle_bool ?x ?y] => destruct (Rle_bool x y)
end; reflexivity.
Qed.

Lemma target_triangle_morph:
  forall (sim : Sim.t) pt1 pt2 pt3, target_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = sim (target_triangle pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold target_triangle.
rewrite classify_triangle_morph.
destruct (classify_triangle pt1 pt2 pt3);simpl;auto.
- apply barycenter_3_morph.
- apply opposite_of_max_side_morph.
Qed.

Ltac solve_ineq_0 :=
  repeat progress match goal with
                  | |- not(eq _ R0) => apply not_eq_sym ; apply Rlt_not_eq
                  | |- (0 < _)%R => apply Rlt_0_1
                  | |- (0 < _)%R => apply Rplus_lt_0_compat
                  end.


Lemma middle_is_barycenter_3:
  forall x y , (barycenter_3_pts x y (/ 2%R * (x+y)) = (/ 2)%R * (x + y))%R2.
Proof.
  intros x y.
  unfold barycenter_3_pts.
  repeat rewrite R2.add_distr.
  repeat rewrite R2.mult_morph.
  (*repeat rewrite R2.add_assoc.
   *)  rewrite <- (Rinv_r_simpl_r 2 (/ 3)) at 1;solve_ineq_0.
  rewrite <- (Rinv_r_simpl_r 2 (/ 3)) at 2;solve_ineq_0.
  rewrite <- Rinv_mult_distr;solve_ineq_0.
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr;solve_ineq_0.
  setoid_rewrite R2.add_comm at 2.
  repeat rewrite R2.add_assoc.
  repeat rewrite R2.plus_morph.
  rewrite <- R2.add_assoc.
  rewrite R2.plus_morph.
  setoid_rewrite Rmult_comm at 3.
  setoid_rewrite Rmult_comm at 4.
  setoid_rewrite <- (Rmult_1_r (/ 6)) at 2 3.
  rewrite (Rmult_comm (/ 6) 1).
  repeat rewrite <- Rmult_plus_distr_r.
  rewrite (Rplus_comm).
  repeat rewrite <- R2.add_distr.
  rewrite <- (Rinv_r_simpl_r 3 (/ 2));solve_ineq_0.
  repeat rewrite Rmult_assoc.
  rewrite <- Rinv_mult_distr;solve_ineq_0.
  setoid_rewrite Rmult_comm at 2.
  reflexivity.
Qed.


Lemma R2_is_middle_morph : forall x y C (sim:Sim.t), is_middle x y C -> (is_middle (sim x) (sim y) (sim C)).
Proof.
  intros x y C sim hmid.
  red.
  intros p.
  unfold is_middle in hmid.
  rewrite <- (@Similarity.section_retraction _ _ _ (sim.(Sim.sim_f)) p).
  setoid_rewrite sim.(Sim.dist_prop).
  setoid_rewrite R_sqr.Rsqr_mult.
  setoid_rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  - apply Rle_0_sqr.
  - apply hmid.
Qed.


Lemma R2_middle_morph : forall x y (sim:Sim.t), (R2.middle (sim x) (sim y))%R2 = sim ((R2.middle x y))%R2.
Proof.
  intros x y sim.
  generalize (@middle_spec x y).
  intro hmidlxy.
  generalize (@middle_spec (sim x) (sim y)).
  intro hmidsimxy.
  assert (is_middle (sim x) (sim y) (sim (R2.middle x y))).
  { apply R2_is_middle_morph.
    auto. }
  apply middle_unique with (sim x) (sim y);assumption.
Qed.

Lemma R2_is_bary3_morph : forall x y z C (sim : Sim.t),
  is_barycenter_3_pt x y z C -> (is_barycenter_3_pt (sim x) (sim y) (sim z) (sim C)).
Proof.
  intros x y z C sim hmid.
  red.
  intros p.
  unfold is_barycenter_3_pt in hmid.
  rewrite <- (@Similarity.section_retraction _ _ _ (sim.(Sim.sim_f)) p).
  setoid_rewrite sim.(Sim.dist_prop).
  setoid_rewrite R_sqr.Rsqr_mult.
  repeat setoid_rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  - apply Rle_0_sqr.
  - apply hmid.
Qed.


Lemma R2_bary3_morph : forall x y z (sim : Sim.t),
  (barycenter_3_pts (sim x) (sim y) (sim z))%R2 = sim ((barycenter_3_pts x y z))%R2.
Proof.
  intros x y z sim.
  generalize (@bary3_spec x y z).
  intro hmidlxy.
  generalize (@bary3_spec (sim x) (sim y) (sim z)).
  intro hmidsimxy.
  assert (is_barycenter_3_pt (sim x) (sim y) (sim z) (sim (barycenter_3_pts x y z))).
  { apply R2_is_bary3_morph.
    auto. }
  apply bary3_unique with (sim x) (sim y) (sim z);assumption.
Qed.


Lemma target_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> target (Spect.map sim s) = sim (target s).
Proof.
intros sim s hnonempty. unfold target.
assert (Hperm : Permutation (List.map sim (filter (on_circle (SEC (Spect.support s))) (Spect.support s)))
                  (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (Spect.support (Spect.map sim s)))).
{ assert (Heq : filter (on_circle (SEC (Spect.support s))) (Spect.support s)
              = filter (fun x => on_circle (sim_circle sim (SEC (Spect.support s))) (sim x)) (Spect.support s)).
  { apply filter_extensionality_compat; trivial. repeat intro. subst. now rewrite on_circle_morph. }
  rewrite Heq. rewrite <- filter_map.
  rewrite <- PermutationA_Leibniz. rewrite <- Spect.map_injective_support; trivial.
  - rewrite filter_extensionality_compat; try reflexivity.
    repeat intro. subst. f_equal. symmetry. rewrite <- SEC_morph.
    apply SEC_compat. apply map_sim_support.
  - intros ? ? H. now rewrite H.
  - apply Sim.injective. }
rewrite <- PermutationA_Leibniz in Hperm.
assert (Hlen := PermutationA_length _ Hperm).
destruct ((filter (on_circle (SEC (Spect.support s))) (Spect.support s))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hn,
         (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (Spect.support (Spect.map sim s)))
         as [| pt1' [| pt2' [| pt3' [| ? ?]]]]; simpl in *; try (omega || reflexivity); clear Hlen.
+ destruct (@SEC_reached (Spect.support s)) as [x hx].
  * generalize (@SEC_reached _ hnonempty).
    intros hin.
    destruct hin as [pt [hin honcirc]].
    intro abs.
    rewrite abs in hin.
    elim (in_nil hin).
  * admit.
+ now rewrite (PermutationA_1 _) in Hperm.
+ rewrite (PermutationA_2 _) in Hperm.
  destruct Hperm as [[H1 H2] | [H1 H2]]; subst.
  * rewrite R2_middle_morph.
    reflexivity.
  * rewrite R2_middle_morph.
    unfold R2.middle.
    rewrite R2.add_comm at 1.
    reflexivity.
+ rewrite PermutationA_Leibniz in Hperm. rewrite <- (target_triangle_compat Hperm). apply target_triangle_morph.
+ change (sim (center (SEC (Spect.support s)))) with (center (sim_circle sim (SEC (Spect.support s)))).
  f_equal. rewrite <- SEC_morph. apply SEC_compat, map_sim_support.
Admitted.

Corollary SECT_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> Permutation (SECT (Spect.map sim s)) (map sim (SECT s)).
Proof.
intros sim s s_nonempty. unfold SECT.
rewrite (target_morph _ s_nonempty). simpl. constructor.
transitivity (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (map sim (Spect.support s))).
+ rewrite <- PermutationA_Leibniz. apply (filter_PermutationA_compat _).
  - repeat intro. now subst.
  - rewrite PermutationA_Leibniz. apply map_sim_support.
+ rewrite filter_map.
  cut (map sim (filter (fun x => on_circle (SEC (Spect.support (Spect.map sim s))) (sim x)) (Spect.support s))
       = (map sim (filter (on_circle (SEC (Spect.support s))) (Spect.support s)))).
  - intro Heq. now rewrite Heq.
  - f_equal. apply filter_extensionality_compat; trivial.
    repeat intro. subst. now rewrite map_sim_support, SEC_morph, on_circle_morph.
Qed.


Instance inclA_bool_compat A eqA :
  Proper (eq ==> eq ==> @PermutationA A eqA ==> @PermutationA A eqA ==> eq) (@inclA_bool A eqA).
Proof.
Admitted.

Lemma is_clean_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> is_clean (Spect.map sim s) = is_clean s.
Proof.
intros sim s s_nonempty. unfold is_clean.
destruct (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support (Spect.map sim s)) (SECT (Spect.map sim s))) eqn:Hx,
         (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support s) (SECT s)) eqn:Hy;
trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff, ?inclA_Leibniz in *.
- elim Hy. intros x Hin. apply (in_map sim) in Hin. rewrite <- map_sim_support in Hin.
  apply Hx in Hin. rewrite SECT_morph, in_map_iff in Hin;auto.
  destruct Hin as [x' [Heq ?]]. apply Sim.injective in Heq. now rewrite <- Heq.
- elim Hx. intros x Hin. rewrite SECT_morph;auto. rewrite map_sim_support in Hin.
  rewrite in_map_iff in *. destruct Hin as [x' [? Hin]]. subst. exists x'. repeat split. now apply Hy.
Qed.


Theorem round_simplify : forall da conf,
    Config.eq (round gatherR2 da conf)
              (fun id => match da.(step) id with
                         | None => conf id
                         | Some f =>
                           let s := !! conf in
                           match Spect.support (Spect.max s) with
                           | nil => conf id (* only happen with no robots *)
                           | pt :: nil => pt (* majority stack *)
                           | _ => if is_clean s then target s else
                                    if mem R2.eq_dec (conf id) (SECT s) then conf id else target s
                           end
                         end).
Proof.
intros da conf id. hnf. unfold round.
assert (supp_nonempty:=support_non_nil conf).
destruct (step da id) as [f |] eqn:Hstep; trivial.
destruct id as [g | b]; try now eapply Fin.case0; exact b.
remember (conf (Good g)) as pt. remember (f pt) as sim.
assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. }
simpl pgm. unfold gatherR2_pgm.
assert (Hperm : Permutation (map sim (Spect.support (Spect.max (!! conf))))
                            (Spect.support (Spect.max (!! (Config.map sim conf)))))
  by (now rewrite <- map_sim_support, <- PermutationA_Leibniz, <- max_morph, Spect.from_config_map).
assert (Hlen := Permutation_length Hperm).
destruct (Spect.support (Spect.max (!! conf))) as [| pt1 [| pt2 l]] eqn:Hmax,
         (Spect.support (Spect.max (!! (Config.map sim conf)))) as [| pt1' [| pt2' l']];
simpl in Hlen; discriminate || clear Hlen.
- rewrite Spect.support_nil, Spect.max_empty in Hmax. elim (spect_non_nil _ Hmax).
- simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'. now apply Sim.compose_inverse_l.
- rewrite <- Spect.from_config_map, is_clean_morph; trivial.
  + destruct (is_clean (!! conf)).
    * rewrite <- Spect.from_config_map, target_morph; trivial;auto.
      now apply Sim.compose_inverse_l.
    * rewrite <- (Sim.center_prop sim). rewrite Heqsim at 3. rewrite (step_center da _ _ Hstep).
      assert (Hperm' : PermutationA eq (SECT (!! (Config.map sim conf))) (map sim (SECT (!! conf)))).
      { rewrite PermutationA_Leibniz, <- SECT_morph;auto.
        f_equiv. now rewrite Spect.from_config_map. }
    rewrite Hperm'. rewrite (mem_injective_map _); trivial; try (now apply Sim.injective); [].
    destruct (mem R2.eq_dec pt (SECT (!! conf))).
      -- rewrite <- (Sim.center_prop sim), Heqsim, (step_center _ _ _ Hstep). now apply Sim.compose_inverse_l.
      -- simpl. rewrite <- sim.(Similarity.Inversion), <- target_morph;auto.
         f_equiv. now apply Spect.from_config_map.
Qed.

(** ***  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, everyone goes there. **)
Lemma round_simplify_Majority : forall da conf pt,
    Spect.support (Spect.max (!! conf)) = pt :: nil ->
    Config.eq (round gatherR2 da conf)
              (fun id => match step da id with
                      | None => conf id
                      | Some _ => pt
                         end).
Proof.
  intros da conf pt Hmaj id. rewrite round_simplify;auto.
  destruct (step da id); try reflexivity. cbv zeta. now rewrite Hmaj.
Qed.



Lemma round_simplify_clean : forall da conf,
  2 <= length (Spect.support (Spect.max (!! conf))) ->
  is_clean (!! conf) = true ->
  Config.eq (round gatherR2 da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => target (!! conf)
                    end).
Proof.
intros da conf Hlen Hclean id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta. rewrite Hclean.
destruct (Spect.support (Spect.max (!! conf))) as [| ? [| ? ?]]; simpl in Hlen; try omega.
reflexivity.
Qed.

Lemma round_simplify_dirty : forall da conf,
  2 <= length (Spect.support (Spect.max (!! conf))) ->
  is_clean (!! conf) = false ->
  Config.eq (round gatherR2 da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => if mem R2.eq_dec (conf id) (SECT (!! conf)) then conf id else target (!! conf)
                    end).
Proof.
intros da conf Hlen Hclean id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta. rewrite Hclean.
destruct (Spect.support (Spect.max (!! conf))) as [| ? [| ? ?]]; simpl in Hlen; try omega.
reflexivity.
Qed.

Theorem destination_is_target : forall da config, 2 <= length (Spect.support (Spect.max (!! config))) ->
  forall id, In id (moving gatherR2 da config) -> round gatherR2 da config id = target (!! config).
Proof.
intros da config Hlen id Hmove. rewrite round_simplify.
destruct (step da id) as [f |] eqn:Hstep.
* rewrite moving_spec, round_simplify, Hstep in Hmove. cbn in *.
  destruct (Spect.support (Spect.max (!! config))) as [| ? [| ? ?]]; simpl in Hlen; try omega.
  destruct (is_clean (!! config)) eqn:Hclean.
  + reflexivity.
  + destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem.
    - now elim Hmove.
    - reflexivity.
* apply moving_active in Hmove. rewrite active_spec in Hmove. contradiction.
Qed.

Corollary same_destination : forall da config id1 id2,
  In id1 (moving gatherR2 da config) -> In id2 (moving gatherR2 da config) ->
  round gatherR2 da config id1 = round gatherR2 da config id2.
Proof.
intros da config id1 id2 Hmove1 Hmove2.
destruct (le_lt_dec 2 (length (Spect.support (Spect.max (!! config))))) as [Hle |Hlt].
+ now repeat rewrite destination_is_target.
+ rewrite moving_spec in *. do 2 rewrite round_simplify in *. cbn in *.
  destruct (step da id1), (step da id2); try (now elim Hmove1 + elim Hmove2); [].
  destruct (Spect.support (Spect.max (!! config))) as [| ? [| ? ?]] eqn:Hsupp.
  - now elim Hmove1.
  - reflexivity.
  - simpl in Hlt. omega.
Qed.

(* Next lemmas taken from the gathering algo in R. *)
(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Majority_grow :  forall pt config da, Spect.support (Spect.max (!! config)) = pt :: nil ->
  (!! config)[pt] <= (!! (round gatherR2 da config))[pt].
Proof.
intros pt conf da Hmaj.
rewrite (round_simplify_Majority _ _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - R2dec. R2dec_full; apply le_n_S + apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall pt pt' conf da, pt <> pt' ->
  Spect.support (Spect.max (!! conf)) = pt :: nil -> (!! (round gatherR2 da conf))[pt'] <= (!! conf)[pt'].
Proof.
intros pt pt' conf da Hdiff Hmaj.
rewrite (round_simplify_Majority _ _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - R2dec_full; try contradiction; []. R2dec_full; try apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.


Definition MajTower_at x conf := forall y, y <> x -> ((!! conf)[y] < (!! conf)[x]).

Instance MajTower_at_compat : Proper (Logic.eq ==> Config.eq ==> iff) MajTower_at.
Proof. intros ? ? ? ? ? Hconf. subst. unfold MajTower_at. now setoid_rewrite Hconf. Qed.

Lemma Majority_MajTower_at : forall config pt,
  Spect.support (Spect.max (!! config)) = pt :: nil -> MajTower_at pt config.
Proof.
intros config pt Hmaj x Hx. apply Spect.max_spec2.
- rewrite <- Spect.support_In, Hmaj. now left.
- rewrite <- Spect.support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

Theorem MajTower_at_equiv : forall config pt, MajTower_at pt config <->
  Spect.support (Spect.max (!! config)) = pt :: nil.
Proof.
intros config pt. split; intro Hmaj.
* apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz.
  apply (NoDupA_equivlistA_PermutationA _).
  + apply NoDupA_singleton.
  + apply Spect.support_NoDupA.
  + intro y. rewrite InA_singleton.
    rewrite Spect.support_In, Spect.max_spec1_iff; try apply spect_non_nil; [].
    split; intro Hpt.
    - subst y. intro x. destruct (R2.eq_dec x pt).
      -- rewrite e. reflexivity.
      -- apply lt_le_weak. now apply (Hmaj x).
    - destruct (R2.eq_dec y pt) as [? | Hy]; trivial.
      exfalso. apply (Hmaj y) in Hy. elim (lt_irrefl (!! config)[pt]).
      eapply le_lt_trans; try eassumption; [].
      apply Hpt.
* intros x Hx. apply Spect.max_spec2.
  - rewrite <- Spect.support_In, Hmaj. now left.
  - rewrite <- Spect.support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.


(** Whenever there is a majority stack, it remains forever so. *)
Theorem MajTower_at_forever : forall pt conf da, MajTower_at pt conf -> MajTower_at pt (round gatherR2 da conf).
Proof.
intros pt conf da Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! conf)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
  rewrite MajTower_at_equiv in Hmaj.
  assumption.
- eapply Majority_grow; eauto.
  rewrite MajTower_at_equiv in Hmaj.
  assumption.
Qed.

Lemma forbidden_support_length : forall config, forbidden config ->
  Spect.size (!! config) = 2.
Proof.
intros conf [Heven [HsizeG [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
rewrite <- (@Spect.cardinal_total_sub_eq (Spect.add pt2 (Nat.div2 N.nG) (Spect.singleton pt1 (Nat.div2 N.nG)))
                                        (!! conf)).
+ rewrite Spect.size_add.
  destruct (Spect.In_dec pt2 (Spect.singleton pt1 (Nat.div2 N.nG))) as [Hin | Hin].
  - exfalso. rewrite Spect.In_singleton in Hin.
    destruct Hin. now elim Hdiff.
  - rewrite Spect.size_singleton; trivial.
    apply Exp_prop.div2_not_R0. apply HsizeG.
  - apply Exp_prop.div2_not_R0. apply HsizeG.
+ intro pt. destruct (R2.eq_dec pt pt2), (R2.eq_dec pt pt1); subst.
  - elim Hdiff. transitivity pt;auto.
  - rewrite Spect.add_spec, Spect.singleton_spec.
    destruct (R2.eq_dec pt pt2); try contradiction.
    destruct (R2.eq_dec pt pt1); try contradiction.
    simpl.
    rewrite e0.
    now apply Nat.eq_le_incl.
  - rewrite Spect.add_other, Spect.singleton_spec;auto.
    destruct (R2.eq_dec pt pt1); try contradiction.
    rewrite e0.
    now apply Nat.eq_le_incl.
  - rewrite Spect.add_other, Spect.singleton_spec;auto.
    destruct (R2.eq_dec pt pt1); try contradiction.
    auto with arith.
+ rewrite Spect.cardinal_add, Spect.cardinal_singleton, Spect.cardinal_from_config.
  unfold N.nB. rewrite plus_0_r. now apply even_div2.
Qed.


(* TODO: delete and put the hypothesis exactly when it is needed (that is in forbidden, that is all). *)
Lemma nGge2: N.nG >= 2.
red.
transitivity 3;auto.
apply nG_conf.
Qed.

Lemma support_max_1_not_forbidden : forall config pt,
  MajTower_at pt config -> ~forbidden config.
Proof.
intros config pt Hmaj. rewrite MajTower_at_equiv in Hmaj.
assert (Hmax : forall x, Spect.In x (Spect.max (!! config)) <-> x = pt).
{ intro x. rewrite <- Spect.support_spec, Hmaj. split.
  - intro Hin. inversion_clear Hin. assumption. inversion H.
  - intro. subst x. now left. }
intro Hforbidden.
assert (Hsuplen := forbidden_support_length Hforbidden).
destruct Hforbidden as [Heven [? [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
assert (Hsup : Permutation (Spect.support (!! config)) (pt1 :: pt2 :: nil)).
{ assert (Hin1 : InA eq pt1 (Spect.support (!! config))).
  { rewrite Spect.support_spec. unfold Spect.In. rewrite Hpt1. apply Exp_prop.div2_not_R0. assumption. }
  assert (Hin2 : InA eq pt2 (Spect.support (!! config))).
  { rewrite Spect.support_spec. unfold Spect.In. rewrite Hpt2. now apply Exp_prop.div2_not_R0. }
  apply (PermutationA_split _) in Hin1. destruct Hin1 as [l Hl]. rewrite Hl in Hin2.
  inversion_clear Hin2; try now subst; elim Hdiff.
  rewrite Spect.size_spec, Hl in Hsuplen. destruct l as [| x [| ? ?]]; simpl in Hsuplen; try omega.
  inversion_clear H.
  - inversion H0;subst.
    + now rewrite <- PermutationA_Leibniz.
    + inversion H1. 
  - inversion H0;subst.
    + now rewrite <- PermutationA_Leibniz.
    + inversion H2. }
assert (Hpt : pt = pt1 \/ pt = pt2).
{ assert (Hin : In pt (pt1 :: pt2 :: nil)).
  { rewrite <- Hsup, <- InA_Leibniz, Spect.support_spec,
            <- (Spect.max_subset (!! config)), <- Spect.support_spec, Hmaj.
    now left. }
inversion_clear Hin; auto. inversion_clear H0; auto. inversion H1. }
apply (lt_irrefl (Nat.div2 N.nG)). destruct Hpt; subst pt.
- rewrite <- Hpt1 at 2. rewrite <- Hpt2. apply Spect.max_spec2; try now rewrite Hmax.
  rewrite Hmax. auto.
- rewrite <- Hpt1 at 1. rewrite <- Hpt2. apply Spect.max_spec2; now rewrite Hmax.
Qed.


Definition no_Majority conf := (Spect.size (Spect.max (!! conf)) > 1)%nat.

(* forbidden_support_length already proves the <- direction *)
Lemma forbidden_equiv : forall conf,
  forbidden conf <-> no_Majority conf /\ Spect.size (!! conf) = 2%nat.
Proof.
  intro conf. unfold no_Majority. split.
  - intro Hforbidden. split.
    + rewrite Spect.size_spec. destruct (Spect.support (Spect.max (!! conf))) as [| pt1 [| pt2 l]] eqn:Hmax.
      * exfalso. revert Hmax. apply support_max_non_nil.
      * exfalso. revert Hmax Hforbidden. rewrite <- MajTower_at_equiv. apply support_max_1_not_forbidden.
      * simpl. omega.
    + now apply forbidden_support_length.
  - intros [Hlen H2]. rewrite Spect.size_spec in *.
    destruct (Spect.support (!! conf)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try (now simpl in H2; omega); [].
    red.
    assert (Hlen':(Spect.size (Spect.max (!! conf)) = 2)%nat).
    { assert (Spect.size (Spect.max (!! conf)) <= 2)%nat.
      { unfold Spect.max.
        rewrite <- H2, <- Hsupp, <- Spect.size_spec.
        apply Spect.size_nfilter.
        now repeat intro; subst. }
      rewrite <- Spect.size_spec in Hlen. omega. }
    clear Hlen H2.
    (* let us reformulate this in a more convenient way *)
   cut (exists pt0 pt3 : Spect.elt,
      pt0 <> pt3 /\
      (!! conf)[pt0] = Nat.div2 N.nG /\ (!! conf)[pt3] = Nat.div2 N.nG /\ Nat.Even N.nG).
   { intros h.
     decompose [ex and] h; split; try assumption;split.
     apply nGge2.
     exists x, x0; intuition. }
   exists pt1, pt2.
   split.
    * assert (hnodup:NoDupA R2.eq (pt1 :: pt2 :: nil)). {
        rewrite <- Hsupp.
        apply Spect.support_NoDupA. }
      intro abs.
      subst.
      inversion hnodup;subst.
      elim H1.
      constructor.
      reflexivity.
    * assert (h:=@Spect.support_nfilter _ (Spect.eqb_max_mult_compat (!!conf)) (!! conf)).
      { change (Spect.nfilter (fun _ : R2.t => Nat.eqb (Spect.max_mult (!! conf))) (!! conf))
        with (Spect.max (!!conf)) in h.
        assert (Hlen'': length (Spect.support (!! conf)) <= length (Spect.support (Spect.max (!! conf)))).
        { rewrite Spect.size_spec in Hlen'. now rewrite Hsupp, Hlen'. }
        assert (h2:=@NoDupA_inclA_length_PermutationA
                      _ R2.eq _
                      (Spect.support (Spect.max (!! conf)))
                      (Spect.support (!! conf))
                      (Spect.support_NoDupA _)
                      (Spect.support_NoDupA _)
                      h Hlen'').
        assert (toto:=@Spect.cardinal_from_config conf).
        unfold N.nB in toto.
        rewrite <- plus_n_O in toto.
        assert (~ R2.eq pt1 pt2). {
          intro abs.
          repeat red in abs.
          rewrite abs in Hsupp.
          assert (hnodup:=Spect.support_NoDupA (!! conf)).
          rewrite  Hsupp in hnodup.
          inversion hnodup;subst.
          match goal with
          | H: ~ InA R2.eq pt2 (pt2 :: nil) |- _ => elim H
          end.
          constructor 1.
          reflexivity. }
        assert (heq_conf:Spect.eq (!!conf)
                                  (Spect.add pt1 ((!! conf)[pt1])
                                             (Spect.add pt2 ((!! conf)[pt2]) Spect.empty))).
      { red.
        intros x.
        destruct (R2.eq_dec x pt1) as [heqxpt1 | hneqxpt1].
        - rewrite heqxpt1.
          rewrite Spect.add_same.
          rewrite (Spect.add_other pt2 pt1).
          + rewrite Spect.empty_spec.
            omega.
          + assumption.
        - rewrite Spect.add_other;auto.
          destruct (R2.eq_dec x pt2) as [heqxpt2 | hneqxpt2].
          + rewrite heqxpt2.
            rewrite Spect.add_same.
            rewrite Spect.empty_spec.
            omega.
          + rewrite Spect.add_other;auto.
            rewrite Spect.empty_spec.
            rewrite <- Spect.not_In.
            rewrite <- Spect.support_spec.
            rewrite Hsupp.
            intro abs.
            inversion abs;try contradiction;subst.
            inversion H1;try contradiction;subst.
            rewrite InA_nil in H2.
            assumption. }
      rewrite heq_conf in toto.
      rewrite Spect.cardinal_fold_elements in toto.
      assert (fold_left (fun (acc : nat) (xn : Spect.elt * nat) => snd xn + acc)
                        ((pt1, (!! conf)[pt1])
                           :: (pt2, (!! conf)[pt2])
                           :: nil) 0
              = N.nG).
      { rewrite <- toto.
        eapply MMultiset.Preliminary.fold_left_symmetry_PermutationA with (eqA := Spect.eq_pair);auto.
        - apply Spect.eq_pair_equiv.
        - apply eq_equivalence.
        - repeat intro;subst.
          rewrite H1.
          reflexivity.
        - intros x y z. omega.
        - symmetry.
          transitivity ((pt1, (!! conf)[pt1]) :: (Spect.elements (Spect.add pt2 (!! conf)[pt2] Spect.empty))).
          eapply Spect.elements_add_out;auto.
          + rewrite heq_conf, Spect.add_same. cut ((!! conf)[pt1] > 0). omega.
            change (Spect.In pt1 (!! conf)). rewrite <- Spect.support_In, Hsupp. now left.
          + rewrite Spect.add_empty.
            rewrite Spect.In_singleton.
            intros [abs _].
            contradiction.
          + apply permA_skip.
            * reflexivity.
            * transitivity ((pt2, (!! conf)[pt2]) :: Spect.elements Spect.empty).
              eapply Spect.elements_add_out;auto.
              -- change (Spect.In pt2 (!! conf)). rewrite <- Spect.support_In, Hsupp. now right; left.
              -- apply Spect.In_empty.
              -- now rewrite Spect.elements_empty. }
      simpl in H0.
      rewrite <- plus_n_O in H0.

      assert ((!! conf)[pt2] = (!! conf)[pt1]).
      { assert (hfilter:= @Spect.nfilter_In _ (Spect.eqb_max_mult_compat (!! conf))).
        transitivity (Spect.max_mult (!! conf)).
        + specialize (hfilter pt2 (!!conf)).
          replace (Spect.nfilter (fun _ : Spect.elt => Nat.eqb (Spect.max_mult (!! conf))) (!!conf))
          with (Spect.max (!!conf)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply Spect.support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 2; constructor 1.
               reflexivity.
            -- symmetry.
               rewrite <- Nat.eqb_eq.
               assumption.
          * trivial.
        + specialize (hfilter pt1 (!!conf)).
          replace (Spect.nfilter (fun _ : Spect.elt => Nat.eqb (Spect.max_mult (!! conf))) (!!conf))
          with (Spect.max (!!conf)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply Spect.support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 1.
               reflexivity.
            -- rewrite <- Nat.eqb_eq.
               assumption.
          * trivial. }
      rewrite H1 in *|-*.
      assert ( 0 + 2 *(!! conf)[pt1] = N.nG).
      { omega. }
      assert (Nat.even N.nG = true).
      { rewrite <- H2.
        rewrite (Nat.even_add_mul_2 0 ((!! conf)[pt1])).
        apply Nat.even_0. }
      split;[| split].
      -- rewrite Nat.div2_odd in H2.
         rewrite <- Nat.negb_even in H2.
         rewrite H3 in H2.
         simpl negb in H2.
         simpl  Nat.b2n in H2.
         repeat rewrite <- plus_n_O,plus_O_n in H2.
         omega.
      -- rewrite Nat.div2_odd in H2.
         rewrite <- Nat.negb_even in H2.
         rewrite H3 in H2.
         simpl negb in H2.
         simpl  Nat.b2n in H2.
         repeat rewrite <- plus_n_O,plus_O_n in H2.
         omega.
      -- apply Even.even_equiv.
         apply Even.even_equiv.
         apply Nat.even_spec.
         assumption. }
Qed.

(* A third formulation of forbidden. *)
Lemma forbidden_spec_2: forall conf,
    forbidden conf <->
    (length (Spect.support (!! conf)) = 2) /\ (length (Spect.support (Spect.max(!! conf))) = 2).
Proof.
  intros conf.
  rewrite forbidden_equiv.
  split.
  - intros H.
    decompose [and] H;clear H.
    split.
    + red in H0.
      apply Nat.le_antisymm.
      rewrite <- Spect.size_spec.
      * rewrite H1. reflexivity.
      * transitivity (Spect.size (Spect.max (!! conf)));auto with arith.
        rewrite Spect.size_spec.
        apply Preliminary.inclA_length with (eqA:=R2.eq).
        -- apply R2.eq_equiv.
        -- apply Spect.support_NoDupA.
        -- apply Spect.support_nfilter.
           apply Spect.eqb_max_mult_compat.
    + red in H0.
      apply Nat.le_antisymm.
      rewrite <- Spect.size_spec.
      * transitivity (Spect.size (!! conf));auto with arith.
        setoid_rewrite Spect.size_spec.
        apply Preliminary.inclA_length with (eqA:=R2.eq).
        -- apply R2.eq_equiv.
        -- apply Spect.support_NoDupA.
        -- apply Spect.support_nfilter.
           apply Spect.eqb_max_mult_compat.
        -- rewrite H1. reflexivity.
      * rewrite <- Spect.size_spec. auto with arith.
  - intros H.
    decompose [and] H;clear H.
    split.
    + red.
      rewrite Spect.size_spec.
      omega.
    + rewrite Spect.size_spec.
      assumption.
Qed.


Theorem Majority_not_forbidden : forall pt config,
  Spect.support (Spect.max (!! config)) = pt :: nil -> ~forbidden config.
Proof.
intros pt config Hmaj. rewrite forbidden_equiv. unfold no_Majority. intros [Hmaj' _].
rewrite Spect.size_spec, Hmaj in Hmaj'. simpl in *. omega.
Qed.


Definition R2dec_bool (x y : R2.t) := if R2.eq_dec x y then true else false.

Lemma R2dec_bool_true_iff (x y : R2.t) : R2dec_bool x y = true <-> x = y.
Proof.
  unfold R2dec_bool.
  destruct (R2.eq_dec x y);split;try discriminate;auto.
Qed.

Lemma R2dec_bool_false_iff (x y : R2.t) : R2dec_bool x y = false <-> x <> y.
Proof.
  unfold R2dec_bool.
  destruct (R2.eq_dec x y);split;try discriminate;auto.
  intros abs.
  rewrite e in abs.
  elim abs;auto.
Qed.


(** Generic result of robograms using multiset spectra. *)
Lemma increase_move :
  forall r conf da pt,
    ((!! conf)[pt] < (!! (round r da conf))[pt])%nat ->
    exists id, round r da conf id = pt /\ round r da conf id <> conf id.
Proof.
  intros r conf da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (R2dec_bool ((round r da conf x))  pt)
                             (negb (R2dec_bool (conf x) pt)))) Names.names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id.
    rewrite andb_true_iff, negb_true_iff, R2dec_bool_true_iff, R2dec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, round r da conf id <> pt \/ conf id = pt).
    { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- R2dec_bool_false_iff, <- R2dec_bool_true_iff. apply Hex, Names.In_names. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt.
    do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
    induction Spect.Names.names as [| id l]; simpl; trivial.
    destruct (R2.eq_dec (round r da conf id) pt) as [Heq | Heq].
    + destruct (R2.eq_dec (conf id) pt); try omega. specialize (Hg id). intuition.
    + destruct (R2.eq_dec (conf id) pt); omega.
Qed.


(* Because of same_destination, we can strengthen the previous result as a equivalence. *)
Lemma increase_move_iff :
  forall conf da pt,
    ((!! conf)[pt] < (!! (round gatherR2 da conf))[pt])%nat <->
    exists id, round gatherR2 da conf id = pt /\ round gatherR2 da conf id <> conf id.
Proof.
intros conf da pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', In id' (moving gatherR2 da conf) -> round gatherR2 da conf id' = pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; rewrite moving_spec; auto. }
  assert (Hstay : forall id, conf id = pt -> round gatherR2 da conf id = pt).
  { intros id' Hid'. destruct (R2.eq_dec (round gatherR2 da conf id') pt) as [Heq | Heq]; trivial.
    assert (Habs := Heq). rewrite <- Hid', <- moving_spec in Habs. apply Hdest in Habs. contradiction. }
  do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
  assert (Hin : In id Spect.Names.names) by apply Names.In_names.
  induction Spect.Names.names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. destruct (R2.eq_dec (conf id) pt) as [Heq | Heq].
    - rewrite <- Hid in Heq. now elim Hroundid.
    - destruct (R2.eq_dec (round gatherR2 da conf id) pt ) as [Hok | Hko]; try contradiction; [].
      apply le_n_S. induction l; simpl.
      -- reflexivity.
      -- repeat R2dec_full; try now idtac + apply le_n_S + apply le_S; apply IHl.
         elim Hneq. now apply Hstay.
  + apply IHl in H. simpl. repeat R2dec_full; try omega.
    elim Hneq. apply Hdest. now rewrite moving_spec, Heq.
Qed.


Lemma not_forbidden_not_majority_length : forall conf,
  no_Majority conf -> ~forbidden conf -> (Spect.size (!! conf) >= 3)%nat.
Proof.
intros conf H1 H2.
assert (Spect.size (!! conf) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption.
  do 2 rewrite Spect.size_spec. apply (NoDupA_inclA_length _).
  - apply Spect.support_NoDupA.
  - unfold Spect.max. apply Spect.support_nfilter. repeat intro. now subst. }
 destruct (Spect.size (!! conf)) as [| [| [| ?]]] eqn:Hlen; try omega.
exfalso. apply H2. now rewrite forbidden_equiv.
Qed.

Lemma towers_elements_3 : forall config pt1 pt2,
  (Spect.size (!! config) >= 3)%nat ->
  Spect.In pt1 (!! config) -> Spect.In pt2 (!! config) -> pt1 <> pt2 ->
  exists pt3, pt1 <> pt3 /\ pt2 <> pt3 /\ Spect.In pt3 (!! config).
Proof.
intros config pt1 pt2 Hlen Hpt1 Hpt2 Hdiff12.
rewrite <- Spect.support_In in *. rewrite Spect.size_spec in Hlen.
apply (PermutationA_split _) in Hpt1. destruct Hpt1 as [supp1 Hperm].
rewrite Hperm in Hpt2. inversion_clear Hpt2; try (now elim Hdiff12); []. rename H into Hpt2.
apply (PermutationA_split _) in Hpt2. destruct Hpt2 as [supp2 Hperm2].
rewrite Hperm2 in Hperm. rewrite Hperm in Hlen.
destruct supp2 as [| pt3 supp]; try (now simpl in Hlen; omega); [].
exists pt3.
rewrite <- Spect.support_In. assert (Hnodup := Spect.support_NoDupA (!! config)).
rewrite Hperm in *. inversion_clear Hnodup. inversion_clear H0. repeat split.
- intro Habs. subst. apply H. now right; left.
- intro Habs. subst. apply H1. now left.
- now right; right; left.
Qed.


Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= N.nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace N.nG with (N.nG + N.nB) by (unfold N.nB; omega).
rewrite <- (Spect.cardinal_from_config config).
rewrite <- (@Spect.add_remove_id pt1 _ (!! config) (reflexivity _)) at 4.
rewrite Spect.cardinal_add.
rewrite <- (@Spect.add_remove_id pt2 _ (!! config) (reflexivity _)) at 6.
rewrite Spect.remove_add_comm, Spect.cardinal_add; trivial.
rewrite <- (@Spect.add_remove_id pt3 _ (!! config) (reflexivity _)) at 8.
rewrite Spect.remove_add_comm, Spect.remove_add_comm, Spect.cardinal_add; trivial.
omega.
Qed.

(* Taken from the gathering in R.
   Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_forbidden : forall da conf, ~forbidden conf -> ~forbidden (round gatherR2 da conf).
Proof.
intros da conf Hok.
(* Three cases for the robogram *)
destruct (Spect.support (Spect.max (!! conf))) as [| pt [| pt' l']] eqn:Hmaj.
- assert (Config.eq (round gatherR2 da conf) conf).
  { rewrite round_simplify;simpl;try rewrite Hmaj; simpl.
    unfold Config.eq. 
    intros id.
    destruct (step da id);reflexivity. }
  rewrite H.
  assumption.
  (* There is a majority tower *)
- apply Majority_not_forbidden with pt.
  rewrite <- ?MajTower_at_equiv in *.
  apply (@MajTower_at_forever pt conf da) in Hmaj.
  assumption.
- rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority conf). { unfold no_Majority. rewrite Spect.size_spec, Hmaj'. simpl. omega. }
  clear pt pt' l' Hmaj'.
  (* A robot has moved otherwise we have the same configuration before and it is forbidden. *)
  assert (Hnil := no_moving_same_conf gatherR2 da conf).
  destruct (moving gatherR2 da conf) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    clear Hnil.
    assert (Hmove : In rmove (moving gatherR2 da conf)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round robogram conf *)
    assert (Hforbidden := Habs). destruct Habs as [HnG [HsizeG[pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ round gatherR2 da conf rmove = pt).
    { assert (Hperm : Permutation (Spect.support (!! (round gatherR2 da conf))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
        + rewrite <- NoDupA_Leibniz. apply Spect.support_NoDupA.
        + simpl. now rewrite <- Spect.size_spec, forbidden_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz, Spect.support_spec. unfold Spect.In. rewrite Hpt1.
            apply Exp_prop.div2_not_R0. apply HsizeG.
          - inversion H; (now inversion H0) || subst. rewrite <- InA_Leibniz, Spect.support_spec.
            unfold Spect.In. rewrite Hpt2. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hpt : In (round gatherR2 da conf rmove) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, In g (moving gatherR2 da conf) -> round gatherR2 da conf g = pt).
    { intros id Hid.
      rewrite <- Hrmove_pt.
      apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 N.nG) <= (!! conf)[pt']).
    { transitivity ((!! (round gatherR2 da conf))[pt']).
      - decompose [and or] Hpt; subst; omega.
      - generalize (@increase_move_iff conf da pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. assumption. }
    assert (Hlt : forall p, p <> pt' -> (!! conf)[p] < div2 N.nG).
    { assert (Hpt'_in : Spect.In pt' (!! conf)).
      { unfold Spect.In. eapply lt_le_trans; try eassumption. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hle := not_forbidden_not_majority_length Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl N.nG).
      destruct (@towers_elements_3 conf pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 N.nG); try assumption. apply Exp_prop.div2_not_R0. apply HsizeG.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total conf Hp Hdiff13 Hdiff23); [].
        unfold Spect.In in Hpt3_in. rewrite <- ?Even.even_equiv in *.
        rewrite (even_double N.nG);simpl;auto.
        unfold Nat.double.
        omega. }
    assert (Hmaj' : MajTower_at pt' conf).
    { intros x Hx. apply lt_le_trans with (div2 N.nG); trivial. now apply Hlt. }
    apply MajTower_at_equiv in Hmaj'.
    red in Hmaj.
    rewrite Spect.size_spec in Hmaj.
    rewrite Hmaj' in Hmaj.
    simpl in Hmaj.
    omega.
Qed.

Axiom SEC_diameter: forall c (pt1 pt2:R2.t),
    c = SEC (pt1::pt2::nil) ->
    R2.dist pt1 pt2 = (c.(radius) * 2)%R.
Lemma diameter_spec1: forall c (pt1 pt2:R2.t),
    c = SEC (pt1::pt2::nil) ->
    R2.dist pt1 pt2 = (c.(radius) * 2)%R ->
    c.(center) = R2.middle pt1 pt2.
Proof.
  intros c pt1 pt2 H H0.
  assert (R2.dist pt1 c.(center) + R2.dist c.(center) pt2 >= R2.dist pt1 pt2)%R.
  { apply Rle_ge, R2.triang_ineq. }
  rewrite H0 in H1.
  destruct (R2.eq_dec pt1 pt2).
  ++ rewrite ?e in *.
     unfold R2.middle.
     rewrite R2.add_distr.
     rewrite R2.plus_morph.
     (assert (h_demi:(1 / 2 + 1 / 2 = 1)%R)).
     { rewrite <- double.
       field. }
     rewrite h_demi.
     rewrite R2.mul_1.
     rewrite R2_dist_defined_2 in H0.
     destruct (Rmult_integral (radius c) 2).
     ** symmetry;assumption.
     ** destruct (@SEC_reached (pt2 :: pt2 :: nil)) as [ x [h1 h2]].
        --- discriminate.
        --- simpl in h1.
            assert (pt2 = x).
            { tauto. }
            clear h1. subst.
            assert (R2.dist (center (SEC (x :: x :: nil))) x = 0%R).
            { unfold on_circle in h2.
              rewrite H2 in h2.
              apply Rdec_bool_true_iff in h2.
              rewrite R2.dist_sym.
              assumption. }
            apply R2.dist_defined.
            assumption.
     ** absurd (0%R = 2%R);auto.
        apply Rlt_not_eq.
        apply Rlt_R0_R2.
  ++ destruct (@SEC_reached_twice (pt1 :: pt2 :: nil)).
     ** auto.
     ** repeat constructor.
        --- intro Habs. inversion Habs.
            +++ symmetry in H2. contradiction.
            +++ inversion H2.
        --- intro Habs. inversion Habs.
     ** decompose [ex and ] H2; clear H2.
        assert (Hpt : x = pt1 /\ x0 = pt2 \/ x0 = pt1 /\ x = pt2).
        { inversion H3; inversion H4;
          repeat match goal with
          | H : In ?x nil  |- _ => inversion H
          | H : In ?x (?y :: nil) |- _ => inversion_clear H; auto
          end; now subst; elim H5.
         }
        assert (on_circle (SEC (pt1 :: pt2 :: nil)) pt1 = true).
        { decompose [and or] Hpt ; subst ; assumption. }
        assert (on_circle (SEC (pt1 :: pt2 :: nil)) pt2 = true).
        { decompose [and or] Hpt ; subst ; assumption. }
        clear dependent x.
        clear dependent x0.
        assert (h_middle: is_middle pt1 pt2 (center c)).
        { red.
          admit. }
        apply (@middle_unique pt1 pt2 (center c) (R2.middle pt1 pt2)).
        assumption.
        apply middle_spec.
Admitted.



Lemma multiplicity_le_nG : forall pt conf, (!! conf)[pt] <= N.nG.
Proof.
intros pt conf. etransitivity.
- apply Spect.cardinal_lower.
- rewrite Spect.cardinal_from_config. unfold N.nB. omega.
Qed.

Lemma next_target_same : forall da conf pt1 pt2 pt3,
    ~(is_clean (!! conf) = true /\ Spect.support (!! conf) = pt1 :: pt2 :: pt3 :: nil
      /\ classify_triangle pt1 pt2 pt3 = Equilateral) ->
    target (!! (round gatherR2 da conf)) = target (!! conf).
Proof.
  intros da conf pt1 pt2 pt3 Hexcluded. unfold target.
  destruct (filter (on_circle (SEC (Spect.support (!! conf))))
                   (Spect.support (!! conf))) as [| ptx [| pty [| ptz [| ptt ?]]]] eqn:Hfilter.
  * (* No robots *)
    destruct (@SEC_reached (Spect.support (!! conf))) as [pt Hpt].
    + apply support_non_nil.
    + exfalso. cut (In pt nil).
      - intro H. inversion H.
      - rewrite <- Hfilter. rewrite filter_In. assumption.
  * (* A majority tower *)
    assert (Heq : Spect.support (!! conf) = ptx :: nil).
    { apply SEC_singleton_is_singleton.
      - rewrite <- NoDupA_Leibniz. apply Spect.support_NoDupA.
      - assumption. }
    assert (Hconfig : Config.eq (round gatherR2 da conf) (fun id => ptx)).
    { intro id. rewrite (round_simplify_Majority da conf (pt := ptx)).
      + destruct (step da id).
        - reflexivity.
        - assert (Hin : Spect.In (conf id) (!! conf)) by apply Spect.pos_in_config.
          rewrite <- Spect.support_In, Heq in Hin. inversion_clear Hin; trivial. now rewrite InA_nil in *.
      + assert (Hsingl : Spect.eq (!! conf) (Spect.singleton ptx (!!conf)[ptx])).
        { eapply proj1. rewrite <- Spect.support_1, Heq. reflexivity. }
        apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz.
        rewrite Hsingl, Spect.max_singleton, Spect.support_singleton; try reflexivity.
        change (Spect.In ptx (!! conf)). rewrite <- Spect.support_In, Heq. now left. }
    assert (Hfilter_round : filter (on_circle (SEC (Spect.support (!! (round gatherR2 da conf)))))
                         (Spect.support (!! (round gatherR2 da conf))) = ptx :: nil).
    { apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz.
      apply SEC_singleton_is_singleton in Hfilter; try now rewrite <- NoDupA_Leibniz; apply Spect.support_NoDupA.
      (* setoid_rewrite Hconfig. -> Fails! *)
      setoid_rewrite Hconfig at 2; setoid_rewrite Hconfig.
      unfold Spect.from_config. rewrite Config_list_alls.
      (* Idem here! *)
      assert (HnG : N.nG > 0). { apply lt_le_trans with 3. omega. apply nG_conf. }
      rewrite Spect.multiset_alls at 2; rewrite Spect.multiset_alls.
      rewrite Spect.support_singleton at 2; try rewrite Spect.support_singleton; trivial.
      rewrite SEC_singleton. unfold on_circle. cbn. destruct (Rdec_bool (R2.dist ptx ptx) 0) eqn:Htest.
      + reflexivity.
      + exfalso. rewrite Rdec_bool_false_iff in Htest. apply Htest. rewrite R2.dist_defined. reflexivity. }
    now rewrite Hfilter_round.
  * (* Two points on the SEC *)
    
  * (* Three points on the SEC *)
    
  * (* Generic case *)
    
Admitted.

Theorem round_lt_config : forall da conf,
  ~forbidden conf -> moving gatherR2 da conf <> nil ->
  lt_config (round gatherR2 da conf) conf.
Proof.
  intros da conf Hforbidden Hmove. unfold lt_config.
  apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
  assert (Hstep : step da gmove <> None).
  { apply moving_active in Hmove. now rewrite active_spec in Hmove. }
  rewrite moving_spec in Hmove.
  destruct (Spect.support (Spect.max (!! conf))) as [| pt [| pt' smax]] eqn:Hmaj.
  - (* No robots *)
    rewrite Spect.support_nil, Spect.max_empty in Hmaj. elim (spect_non_nil _ Hmaj).
  - (* A majority tower *)
    assert (Hmajnext : Spect.support (Spect.max (!! (round gatherR2 da conf))) = pt :: nil).
    { rewrite <- MajTower_at_equiv. apply (MajTower_at_forever da). now rewrite MajTower_at_equiv. }
    unfold measure. rewrite Hmaj, Hmajnext.
    apply right_lex.
    assert ((!! (round gatherR2 da conf))[pt] <= N.nG).
    { rewrite <- plus_0_r. change 0 with N.nB.
      rewrite <- (Spect.cardinal_from_config (round gatherR2 da conf)).
      apply Spect.cardinal_lower. }
    cut ((!! conf)[pt] < (!! (round gatherR2 da conf))[pt]). omega.
    rewrite increase_move_iff. exists gmove. split; trivial.
    rewrite (round_simplify_Majority _ _ Hmaj). destruct (step da gmove); trivial. now elim Hstep.
  - (* Computing the SEC *)
    assert (Hlen : 2 <= length (Spect.support (Spect.max (!! conf)))).
    { rewrite Hmaj. simpl. omega. }
    destruct (is_clean (!! conf)) eqn:Hclean.
    (** Clean case *)
    + pose (l := Spect.support (!! conf)).
      destruct (filter (on_circle (SEC (l))) l) as [| pt1 [| pt2 [| pt3 [| pt4 sec]]]] eqn:Hsec;
        unfold measure at 2; rewrite Hmaj; unfold l in Hsec; rewrite Hsec, ?Hclean.
      (* There must be at least two point on the SEC, so the first two cases are absurd. *)
      -- assert (h_all_target:forall g, (conf g) = target (!! conf)). 
         { unfold is_clean in Hclean.
           apply if_true in Hclean.
           destruct Hclean as [Hclean _].
           setoid_rewrite inclA_bool_true_iff in Hclean.
           unfold SECT in Hclean.
           rewrite Hsec in Hclean.
           intros g.
           unfold inclA in Hclean.
           assert (h:=Spect.pos_in_config conf g).
           rewrite <- Spect.support_spec in h.
           apply Hclean in h.
           inversion h;subst. 
           - assumption. 
           - inversion H0. }
         elim Hmove.
         
         rewrite destination_is_target;auto.
         ++ symmetry. 
            apply h_all_target.
         ++ apply moving_spec.
            assumption.
      -- apply SEC_singleton_is_singleton in Hsec.
         exfalso.
         cut (inclA R2.eq (pt :: pt' :: smax) (pt1 :: nil)).
         ++ intros Hincl. cut (pt = pt').
            ** assert (Hnodup : NoDupA R2.eq (pt :: pt' :: smax)).
               { rewrite <- Hmaj. apply Spect.support_NoDupA. }
               inversion_clear Hnodup. intro. subst. apply H. now left.
            ** transitivity pt1.
               --- specialize (Hincl pt $(now left)$). inversion Hincl; trivial.
                   inversion H0.
               --- specialize (Hincl pt' $(now right; left)$). symmetry.
                   inversion Hincl; trivial. inversion H0.
         ++ rewrite <- Hmaj, <- Hsec. apply Spect.support_sub_compat, Spect.max_subset.
      -- (** Three aligned towers *)
        assert (target (!! conf) = R2.middle pt1 pt2).
        { unfold target.
          rewrite Hsec.
          reflexivity. }
        remember ((!! (round gatherR2 da conf))) as f.
        functional induction (measure f); try now (constructor 1; auto; try omega).
        ++ constructor 2.        
           unfold measure_reduce.
           assert (N.nG >= (!! (round gatherR2 da conf))[target (!! (round gatherR2 da conf))]).
           { apply multiplicity_le_nG. }
           assert (N.nG >= (!! conf)[target (!! conf)]).
           { apply multiplicity_le_nG. }
           assert ((!! conf)[target (!! conf)]
                   < (!! (round gatherR2 da conf))[target (!! (round gatherR2 da conf))]).
           { (* We need  to prove that both targets are the same, but this is not always true. *)
             apply increase_move_iff.
             exists gmove.
             split.
             - rewrite round_simplify_clean; trivial.
               destruct (step da gmove).
               + reflexivity.
               + elim Hstep;reflexivity.
             - apply Hmove. }
           omega.

        ++ admit. (* is_clean = false is absurd. *)

        constructor 1.
        destruct (step da id).
          
        

        
      -- destruct (classify_triangle pt1 pt2 pt3) as [| v |] eqn:Htriangle.
         { (** Equilateral triangle *)
           admit. }
         { (** Isosceles triangle *)
           admit. }
         { (** Scalene triangle *)
           admit. }
      -- (** General case *)
        admit.
    (** Dirty case *)
    + rewrite round_simplify_dirty; trivial.
      (* TODO: same decomposition as before *)
      admit.
Admitted.

End GatheringinR2.

