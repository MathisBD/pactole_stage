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
Require Import Pactole.CommonIsoGraphFormalism.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.

Close Scope Z_scope.
Set Implicit Arguments.

Module Graph := MakeRing.

Module ExplorationDefs(N : Size).

Module Names := Robots.Make(N).

Module Loc <: DecidableType.
  Definition t := LocationA.t.
  Definition eq := LocationA.eq.
  Definition eq_dec : forall x y, {eq x y} + {~eq x y} := LocationA.eq_dec.
  Definition eq_equiv : Equivalence eq := LocationA.eq_equiv.
  Definition origin := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.origin.
  
  Definition add (x y : t) := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add x y.
  Definition mul (x y : t) := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.mul x y.
  Definition unit := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.unit.
  Definition opp (x : t) := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp x.
  Definition add_reg_l := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_reg_l.
  Definition add_comm := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_comm.
  Definition opp_distr_add := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp_distr_add.
  Definition add_assoc := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_assoc.
  Definition add_origin := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_origin.
  Definition add_opp := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_opp.
  Definition opp_opp := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp_opp.
  
End Loc.

Module Config := Configurations.Make(Loc)(N)(Names).
Module Iso := CommonIsoGraphFormalism.Make(Graph)(Loc).

Module Export Atom := AtomicGraphFormalism.AGF(Graph)(N)(Names)(Loc)(Config)(Iso).

Module Spect := Atom.Spect.

Module View := Atom.View.  
(* Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").  *)
Import Iso.


Definition bij_trans_V (c : Loc.t) : Isomorphism.bijection Loc.eq.
refine {|
  Isomorphism.section := fun x => Loc.add c (Loc.opp x);
  Isomorphism.retraction := fun x => Loc.add c (Loc.opp x) |}.
Proof.
abstract (intros x y; split; intro Heq; rewrite <- Heq;
          now rewrite Loc.opp_distr_add, Loc.add_assoc, Loc.add_opp, Loc.opp_opp, Loc.add_comm, Loc.add_origin).
Defined.

Definition bij_trans_E (c : Loc.t) : Isomorphism.bijection Graph.Eeq.
  refine {|
      Isomorphism.section := fun x => ( Loc.add c (Loc.opp (fst x)), match snd x with
                                          | GraphFromZnZ.Forward => GraphFromZnZ.Backward
                                          | GraphFromZnZ.Backward => GraphFromZnZ.Forward
                                          end);
      Isomorphism.retraction := fun x => (Loc.add c (Loc.opp (fst x)),
                                          match snd x with
                                          | GraphFromZnZ.Forward => GraphFromZnZ.Backward
                                          | GraphFromZnZ.Backward => GraphFromZnZ.Forward
                                          end) |}.
Proof.
  + intros e1 e2 He_eq.
    unfold Graph.Eeq.
    split.
    unfold Graph.src.
    simpl.
    now rewrite He_eq.
    simpl.
    destruct He_eq.
    Set Printing Implicit.
    unfold Loc.t, LocationA.t, Graph.V, Graph.E, Graph.dir in *.
    rewrite H0.
    reflexivity.
  + intros.
    unfold Loc.t, LocationA.t, Graph.V, Graph.E, Graph.dir in *.
    split.
    intros.
    unfold Graph.Eeq, Graph.src in *; destruct H; split; simpl in *.
    rewrite <- H.
    rewrite Loc.opp_distr_add,Loc.opp_opp, Loc.add_assoc, Loc.add_opp,Loc.add_comm,Loc.add_origin.
    reflexivity.
    destruct (snd y) eqn : Hy, (snd x) eqn : Hx;
    unfold Loc.t, LocationA.t, Graph.V, Graph.E, Graph.dir in *;
    try discriminate.
    rewrite Hy in H0.
    discriminate.
    rewrite Hx.
    reflexivity.
    rewrite Hx.
    reflexivity.
    rewrite Hy in H0.
    discriminate.
    intros.
    unfold Graph.Eeq, Graph.src in *; destruct H; split; simpl in *.
    rewrite <- H.
    rewrite Loc.opp_distr_add,Loc.opp_opp, Loc.add_assoc, Loc.add_opp,Loc.add_comm,Loc.add_origin.
    reflexivity.
    destruct (snd y) eqn : Hy, (snd x) eqn : Hx;
    unfold Loc.t, LocationA.t, Graph.V, Graph.E, Graph.dir in *;
    try (rewrite Hx in H0; discriminate);
    try (rewrite Hy; reflexivity).
Defined.


(* Definition bij_trans_T := Isomorphism.bij_id Iso.Req_equiv. *)
Parameter bij_trans_T : Loc.t -> Isomorphism.bijection Iso.Req.
Axiom bT_morph : forall c (e:Graph.E),
    (Isomorphism.section (bij_trans_T c)) (Graph.threshold e) =
    Graph.threshold ((Isomorphism.section (bij_trans_E c)) e).
Axiom bT_bound : forall c r, (0 < r < 1)%R <->
                             (0 < (Isomorphism.section (bij_trans_T c) r) < 1)%R.
Axiom bT_crois : forall c a b, (a < b)%R ->
                               ((Isomorphism.section (bij_trans_T c) a) <
                                (Isomorphism.section (bij_trans_T c) b))%R.
Axiom bT_compat : forall c1 c2, Isomorphism.bij_eq (bij_trans_T c1) (bij_trans_T c2).

Definition id_s := Iso.id.

Definition trans (c : Loc.t) : Iso.t.
refine {|
    Iso.sim_V := bij_trans_V c;
    Iso.sim_E := bij_trans_E c;
    Iso.sim_T := bij_trans_T c |}.
Proof.
- intros e; split; unfold Graph.src in *.
  simpl. reflexivity.
  unfold Graph.tgt in *.
  simpl in *.
  unfold Loc.t, LocationA.t, MakeRing.V, Graph.E, MakeRing.E, Graph.dir in *.
  destruct (snd e) eqn : Hsnd.
  rewrite Loc.opp_distr_add.
  rewrite Loc.add_assoc.
  f_equiv.
  unfold ImpossibilityKDividesN.Loc.eq,ImpossibilityKDividesN.Loc.opp.
  set (N :=  ImpossibilityKDividesN.def.n).
  rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same, Z.mod_mod;
  simpl.
  reflexivity.
  generalize ImpossibilityKDividesN.n_sup_1; unfold ImpossibilityKDividesN.def.n in *.
  unfold N.
  omega.
  generalize ImpossibilityKDividesN.n_sup_1; unfold ImpossibilityKDividesN.def.n in *.
  unfold N.
  omega.
  rewrite Loc.opp_distr_add.
  rewrite Loc.add_assoc.
  f_equiv.
  unfold ImpossibilityKDividesN.Loc.eq,ImpossibilityKDividesN.Loc.opp.
  set (N :=  ImpossibilityKDividesN.def.n).
  rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same, Z.mod_mod;
  simpl.
  reflexivity.
  generalize ImpossibilityKDividesN.n_sup_1; unfold ImpossibilityKDividesN.def.n in *.
  unfold N.
  omega.
  generalize ImpossibilityKDividesN.n_sup_1; unfold ImpossibilityKDividesN.def.n in *.
  unfold N.
  omega.
- intros.
  apply bT_morph.
- apply bT_crois.
- apply bT_bound.
Defined.


Instance trans_compat : Proper (Loc.eq ==> Iso.eq) trans.
Proof.
  intros c1 c2 Hc. unfold Iso.eq, trans. simpl in *.
  repeat split; try apply Isomorphism.section_compat.
  now f_equiv.
  unfold bij_trans_E in *; simpl in *.  
  unfold Loc.add, ImpossibilityKDividesN.Loc.add.
  rewrite <- Zdiv.Zplus_mod_idemp_l.
  rewrite Hc, Zdiv.Zplus_mod_idemp_l.
  unfold Graph.Eeq in *.
  destruct H.
  unfold Loc.t, LocationA.t, Graph.V.
  unfold Loc.opp, ImpossibilityKDividesN.Loc.opp, Graph.dir in *.
  rewrite <- Zdiv.Zminus_mod_idemp_r, H, Zdiv.Zminus_mod_idemp_r.
  reflexivity.
  simpl.
  unfold Graph.Eeq in *.
  destruct H.
  unfold Loc.t, LocationA.t, Graph.V.
  unfold Loc.opp, ImpossibilityKDividesN.Loc.opp, Graph.dir in *.
  rewrite H0.
  reflexivity.
  apply bT_compat.
Qed.

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