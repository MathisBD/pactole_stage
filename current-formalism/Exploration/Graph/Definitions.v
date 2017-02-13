(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Reals.
Require Import Omega.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.AtomicGraphFormalism.
Require Import Arith.Div2.
Require Import Pactole.DiscreteSimilarity.
Require Import Pactole.CommonDiscreteFormalism.
Require Import Pactole.DiscreteRigidFormalism.
Require Import Pactole.DiscreteMultisetSpectrum.


Close Scope Z_scope.
Set Implicit Arguments.


Module ExplorationDefs(Graph : GraphDef)(Loc : LocationADef(Graph))(N : Size).

Module Names := Robots.Make(N).
Module Config := Configurations.Make(Loc)(N)(Names).


Module Export Atom := AtomicGraphFormalism.AGF(Graph)(N)(Names)(Loc)(Config).

Module Spect := Atom.Spect.

Module View := Atom.View.  
(* Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").  *)
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".


(* Module Export Common := CommonFormalism.Make(Loc)(N)(Names)(Config)(Spect). *)

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

(* Definition ValidSolExplorationStop (r : robogram) (d : demon) :=
forall (config : Config.t), ~(forbidden config) ->
         (forall l, Will_be_visited l (execute r d config))
         /\ Will_stop (execute r d config).
*)

End ExplorationDefs.