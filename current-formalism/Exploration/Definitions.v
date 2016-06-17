(* essai sur la définition de l'exploration*)

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

Module Spect := DiscreteMultisetSpectrum.Make(Loc)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".


Module Export Common := CommonDiscreteFormalism.Make(Loc)(N)(Spect).
Module Export Rigid := DiscreteRigidFormalism.Make(Loc)(N)(Spect)(Common).

Module Sim := Common.Sim. 

(* already done in DiscreteMultisetSpectrum.

Definition count (location : Loc.t) (conf : Config.t)  (n : nat) (id : Names.ident): nat := 
    if Loc.eq_dec (conf id).(Config.loc) location then (n+1)%nat else n.

Instance count_compat : Proper (Loc.eq ==> Config.eq ==> eq ==> eq ==> eq) count.
Proof.
intros loc1 loc2 Hl conf1 conf2 Hc n1 n2 Hn id1 id2 Hid.
unfold count.
assert (Heqc: Loc.eq (Config.loc (conf1 id2)) (Config.loc (conf2 id2))).
  { f_equiv. apply Hc. }
rewrite Hid, Hn. destruct (Loc.eq_dec (Config.loc (conf1 id2)) loc1) .
+ rewrite Hl, Heqc in e.
  destruct (Loc.eq_dec (Config.loc (conf2 id2)) loc2).
    reflexivity.
    contradiction.
+ rewrite Hl, Heqc in n.
  destruct (Loc.eq_dec (Config.loc (conf2 id2)) loc2).
    contradiction.
    reflexivity.
Qed.
(* with the strong multiplicity,  we can know the exact numbur of robots on a location*)
Definition multiplicity_strong (loc : Loc.t) (conf : Config.t) : nat := 
  List.fold_left (count loc conf) Names.names 0.


Instance multiplicity_strong_compat : Proper (Loc.eq ==> Config.eq ==> eq) multiplicity_strong.
Proof.
intros loc1 loc2 Hl conf1 conf2 Hc. unfold multiplicity_strong.
assert (Hcount := count_compat Hl Hc). f_equiv.  admit.
Admitted.

(* a location contain a tower if more than 2 robots are on this location*)
Definition is_a_tower (conf : Config.t) (loc : Loc.t) := match multiplicity_strong loc conf with
  |0 => false
  | 1%nat => false
  | _ => true
  end.

Instance is_a_tower_compat : Proper (Config.eq ==> Loc.eq ==> eq) is_a_tower.
Proof.
intros conf1 conf2 Hconf loc1 loc2 Hloc.
unfold is_a_tower.
assert (Hm := multiplicity_strong_compat Hloc Hconf).
rewrite Hm. reflexivity.
Qed.
 *)

(*in this probleme, we consider a configuration as a potial initial configuration iff there
  is no tower in it*)
  
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

Definition stop_now (conf : Config.t) :=
    forall g : Names.G, Loc.eq (conf (Good g)).(Config.loc)
                               (conf (Good g)).(Config.robot_info).(Config.target).

Instance stop_now_compat : Proper (Config.eq ==> iff) stop_now.
Proof.
intros c1 c2 Hc. split; intros Hs; unfold stop_now in *; intros g;
specialize (Hs g); destruct (Hc (Good g)) as (Hloc, Hrinfo), Hrinfo as (_,Htar).
now rewrite <- Hloc, <- Htar.
now rewrite Hloc, Htar.
Qed.

CoInductive Stopped (e : execution) : Prop :=
Stop : stop_now (execution_head e) -> Stopped (execution_tail e) -> Stopped e.

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
forall l config, Will_be_visited l (execute r d config) -> Will_stop (execute r d config).

Definition ValidSolExplorationStop (r : robogram) (d : demon) :=
forall (config : Config.t) l, ~(forbidden config) -> Will_be_visited l (execute r d config) 
                                           -> Will_stop (execute r d config).

End ExplorationDefs.