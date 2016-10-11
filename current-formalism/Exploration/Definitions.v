(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Pactole.Preliminary.
Require Import Arith.Div2.
Require Import Omega.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSimilarity.
Require Pactole.CommonDiscreteFormalism.
Require Pactole.DiscreteRigidFormalism.
Require Import Pactole.DiscreteMultisetSpectrum.
Require Import Morphisms.


Close Scope Z_scope.
Set Implicit Arguments.


Module ExplorationDefs(Loc : RingSig)(N : Size).

Module Names := Robots.Make(N).
Module Config := Configurations.Make(Loc)(N)(Names).

Module Spect := DiscreteMultisetSpectrum.Make(Loc)(N)(Names)(Config).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".


Module Export Common := CommonDiscreteFormalism.Make(Loc)(N)(Names)(Config)(Spect).
Module Export Rigid := DiscreteRigidFormalism.Make(Loc)(N)(Names)(Config)(Spect)(Common).

Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.

Module Sim := Common.Sim. 

Definition bij_id := DiscreteSimilarity.bij_id.

Definition bij_trans (c : Loc.t) : DiscreteSimilarity.bijection Loc.eq.
refine {|
  DiscreteSimilarity.section := fun x => Loc.add c (Loc.opp x);
  DiscreteSimilarity.retraction := fun x => Loc.add c (Loc.opp x) |}.
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

Definition is_visited (loc : Loc.t) (conf : Config.t) := 
    exists g : Names.G, Loc.eq (conf (Good g)).(Config.loc) loc .
    
Instance is_visited_compat : Proper (Loc.eq ==> Config.eq ==> iff) is_visited.
Proof.
intros l1 l2 Hl c1 c2 Hc.
split; intros Hv; unfold is_visited in *; destruct Hv as (g, Hv); exists g.
rewrite <- Hl, <- Hv; symmetry; apply Hc.
rewrite Hl, <- Hv; apply Hc.
Qed.

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

Definition stop_now e :=
    Config.eq (execution_head e) (execution_head (execution_tail e)).

Instance stop_now_compat : Proper (eeq ==> iff) stop_now.
Proof.
intros e1 e2 He. split; intros Hs;
unfold stop_now in *.
now rewrite <- He.
now rewrite He.
Qed.

CoInductive Stopped (e : execution) : Prop :=
Stop : stop_now e -> Stopped (execution_tail e) -> Stopped e.

Instance Stopped_compat : Proper (eeq ==> iff) Stopped.
Proof.
intros e1 e2 He. split; revert e1 e2 He ; coinduction rec.
  - destruct H. now rewrite <- He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
  - destruct H. now rewrite He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.

Inductive Will_be_visited (loc: Loc.t) (e : execution) : Prop :=
 | Now_v: has_been_visited loc e -> Will_be_visited loc e
 | Later_v : Will_be_visited loc (execution_tail e) -> Will_be_visited loc e.
 
Inductive Will_stop (e : execution) : Prop :=
 | Now_s : Stopped e -> Will_stop e
 | Later_s : Will_stop (execution_tail e) -> Will_stop e.
 
Instance Will_be_visited_compat : Proper (Loc.eq ==> eeq ==> iff) Will_be_visited.
Proof.
intros l1 l2 Hl e1 e2 He. split; intros Hw. 
+ revert e2 He. induction Hw as [ e1 | e1 He1 IHe1]; intros e2 He.
  - apply Now_v. now rewrite <- Hl, <- He.
  - apply Later_v, IHe1, He.
+ revert e1 He. induction Hw as [ e2 | e2 He2 IHe2]; intros e1 He.
  - apply Now_v. now rewrite Hl, He.
  - apply Later_v, IHe2, He.
Qed.

Instance Will_stop_compat : Proper (eeq ==> iff) Will_stop.
Proof.
intros e1 e2 He. split; intros Hw.
+ revert e2 He. induction Hw as [e1 | e1 He1 IHe1]; intros e2 He.
  - apply Now_s. now rewrite <-He.
  - apply Later_s, IHe1, He.
+ revert e1 He. induction Hw as [e2 | e2 He2 IHe2]; intros e1 He.
  - apply Now_s. now rewrite He.
  - apply Later_s, IHe2, He.
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