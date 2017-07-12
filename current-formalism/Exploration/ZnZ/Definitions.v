(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Pactole.Preliminary.
Require Import Arith.Div2.
Require Import Omega.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
Require Import Pactole.DiscreteSimilarity.
Require Pactole.CommonDiscreteFormalism.
Require Pactole.DiscreteRigidFormalism.
Require Import Pactole.MultisetSpectrum.
Require Import Morphisms.
Require Import Stream.


Close Scope Z_scope.
Set Implicit Arguments.


Module ExplorationDefs (Loc : RingSig)
                       (N : Size)
                       (Info : DecidableTypeWithApplication(Loc)).

Module Names := Robots.Make(N).
Module Config := Configurations.Make(Loc)(N)(Names)(Info).

Module Spect := MultisetSpectrum.Make(Loc)(N)(Names)(Info)(Config).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".


Module Export Common := CommonDiscreteFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect).
Module Export Rigid := DiscreteRigidFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect)(Common).

Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.

Module Sim := Common.Sim.

Definition bij_id := Bijection.id.

(** Unlike what the name suggest, this is not a translation but a reflection with center c/2.
    A translation would be x ↦ x - c and not x ↦ c - x. *)
Definition bij_trans (c : Loc.t) : Bijection.t Loc.eq.
refine {|
  Bijection.section := fun x => Loc.add c (Loc.opp x);
  Bijection.retraction := fun x => Loc.add c (Loc.opp x) |}.
Proof.
abstract (intros x y; split; intro Heq; rewrite <- Heq;
          now rewrite Loc.opp_distr_add, Loc.add_assoc, Loc.add_opp, Loc.opp_opp, Loc.add_comm, Loc.add_origin).
Defined.

Definition id_s : Sim.t.
refine {| Sim.sim_f := bij_id Loc.eq_equiv;
          Sim.center := Loc.origin;
          Sim.center_prop := reflexivity _ |}.
Proof. abstract (intros; auto). Defined.

Definition trans (c : Loc.t) : Sim.t.
refine {|
  Sim.sim_f := bij_trans c;
  Sim.center := c |}.
Proof.
- abstract (compute; apply Loc.add_opp).
- intros. simpl. setoid_rewrite Loc.add_comm.
  rewrite translation_hypothesis. 
rewrite <- (translation_hypothesis (Loc.add x y)).
rewrite Loc.add_assoc, (Loc.add_comm _ x), Loc.add_opp, Loc.add_comm, Loc.add_origin.
rewrite Loc.add_comm, <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
apply Loc.dist_sym.
Defined.


Instance trans_compat : Proper (Loc.eq ==> Sim.eq) trans.
Proof. intros c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.


Definition forbidden (config : Config.t) :=
(* forall id, 
    exists id1, Loc.eq (Config.loc (config id)) 
                       (Loc.add (Config.loc (config id1)) (Loc.mul (Z_of_nat N.nG) Loc.unit)). *)
let m := Spect.from_config(config) in
  forall loc, m[loc] <=1 /\ 
   m[loc] = m[Loc.add loc (Loc.mul (Z_of_nat N.nG /Loc.n ) Loc.unit)].

Instance forbidden_compat: Proper (Config.eq ==> iff) forbidden.
Proof.
intros c1 c2 Hc. split; intros H loc.
- rewrite <- Hc. apply H.
- rewrite Hc. apply H.
Qed.

Definition ValidInitialConfig (config : Config.t) :=
let m := Spect.from_config(config) in
  forall pt, m[pt] <=1.

Instance ValidInitialConfig_compat: Proper (Config.eq ==> iff) ValidInitialConfig.
Proof.
intros c1 c2 Hc.
split; intros Hv pt; destruct (Hv pt).
now rewrite Hc. rewrite <- Hc. auto.
now rewrite Hc. rewrite Hc. auto.
Qed.

Definition is_visited (loc : Loc.t) (e : execution) :=
  let conf := Stream.hd e in 
    exists g : Names.G, Loc.eq (conf (Good g)).(Config.loc) loc .
    
Instance is_visited_compat : Proper (Loc.eq ==> eeq ==> iff) is_visited.
Proof.
intros l1 l2 Hl c1 c2 Hc.
split; intros Hv; unfold is_visited in *; destruct Hv as (g, Hv); exists g.
rewrite <- Hl, <- Hv; symmetry; now rewrite Hc.
rewrite Hl, <- Hv; now rewrite Hc.
Qed.
(*
CoInductive has_been_visited (loc : Loc.t) (e : execution) : Prop :=
Visit : is_visited loc (execution_head e) -> has_been_visited loc (execution_tail e) -> has_been_visited loc e.

Instance has_been_visited_compat : Proper (Loc.eq ==> eeq ==> iff) has_been_visited.
Proof.
intros l1 l2 Hl e1 e2 He. split. 
+ revert e1 e2 He. coinduction rec.
  - rewrite <- Hl, <- He. now destruct H.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
+ revert e1 e2 He. coinduction rec.
  - rewrite Hl, He. now destruct H.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
  Qed.
*)
Definition stop_now (e : execution) :=
    Config.eq (Stream.hd e) (Stream.hd (Stream.tl e)).

Instance stop_now_compat : Proper (eeq ==> iff) stop_now.
Proof.
intros e1 e2 He. split; intros Hs;
unfold stop_now in *.
now rewrite <- He.
now rewrite He.
Qed.

Definition Stopped (e : execution) : Prop :=
  Stream.forever ((stop_now)) e.

Instance Stopped_compat : Proper (eeq ==> iff) Stopped.
Proof.
intros e1 e2 He. split; revert e1 e2 He ; coinduction rec.
  - destruct H. now rewrite <- He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
  - destruct H. now rewrite He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.

Definition Will_be_visited (loc : Loc.t) (e : execution) : Prop :=
  Stream.eventually (is_visited loc) e.

Definition Will_stop (e : execution) : Prop :=
  Stream.eventually Stopped e.
 
Instance Will_be_visited_compat : Proper (Loc.eq ==> eeq ==> iff) Will_be_visited.
Proof.
intros l1 l2 Hl. now apply Stream.eventually_compat, is_visited_compat. 
Qed.

Instance Will_stop_compat : Proper (eeq ==> iff) Will_stop.
Proof.
  apply Stream.eventually_compat, Stopped_compat.
Qed.

(* [Exploration_with_stop e] mean that after a finite time, every node of the space has been
  visited, and after that time, all robots will stay at the same place forever*)
Definition FullSolExplorationStop  (r : robogram) (d : demon) := 
forall config, (forall l, Will_be_visited l (execute r d config)) /\ Will_stop (execute r d config).

Definition ValidSolExplorationStop (r : robogram) (d : demon) :=
forall (config : Config.t), ~(forbidden config) ->
         (forall l, Will_be_visited l (execute r d config))
         /\ Will_stop (execute r d config).

End ExplorationDefs.