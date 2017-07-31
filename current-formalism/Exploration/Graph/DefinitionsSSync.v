(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms
      T. Balabonski, R. Pelle , L. Rieg, X. Urbain
               
      PACTOLE project                                                      
                                                                          
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
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
Require Import Pactole.Bijection.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.DiscreteGraphFormalismSSync.
Require Import Arith.Div2.
Require Import Pactole.DiscreteSimilarity.
Require Import Pactole.CommonDiscreteFormalism.
Require Import Pactole.DiscreteRigidFormalism.
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.CommonIsoGraphFormalism.
Require Import Stream.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.


Close Scope Z_scope.
Set Implicit Arguments.

Module Graph := MakeRing.
Import Graph.

Module ExplorationDefs(N : Size).

Module Names := Robots.Make(N).
Module Iso := CommonIsoGraphFormalism.Make(Graph)(Graph.Loc).
Module MkUnit := CommonGraphFormalism.MakeUnit(Graph)(LocationA).
Module Info := MkUnit.Info.
Module Config := Configurations.Make(Loc)(N)(Names)(Info).
Module Spect := PointedMultisetSpectrum.Make(Loc)(N)(Names)(Info)(Config).
Module DGF := DGF(Graph)(N)(Names)(Loc)(MkUnit)(Config)(Spect)(Iso).
Import Iso DGF.


Notation "s [ pt ]" := (Spect.M.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

(** Definition of the isomorphism of translation on the ring *)
Definition bij_trans_V (c : Loc.t) : Bijection.t Veq.
refine {|
  Bijection.section := fun x => (Loc.add x (Loc.opp c));
  Bijection.retraction := fun x => Loc.add x c |}.
Proof.
  + intros x y Hxy. unfold Veq, Loc.add, Loc.opp in *.
    rewrite <- 3 loc_fin.
    rewrite <- (Zdiv.Zplus_mod_idemp_l), Hxy,
    Zdiv.Zplus_mod_idemp_l.
    reflexivity.
  + intros x y; split;
    intro Heq;
    rewrite <- Heq;
    try now rewrite <- Loc.add_assoc, Loc.add_opp', Loc.add_origin.
    now rewrite <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
Defined.

Definition bij_trans_E (c : Loc.t) : Bijection.t Graph.Eeq.
  refine {|
      Bijection.section := fun x =>  (Loc.add (fst x) (Loc.opp c), snd x);
      Bijection.retraction := fun x => (Loc.add (fst x) c, snd x) |}.
Proof.
  + intros e1 e2 He_eq.
    unfold Graph.Eeq.
    split; unfold Veq, Loc.t in *; simpl;
    destruct He_eq;
    destruct (Nat.eq_dec n 2);
    destruct (snd e1), (snd e2); try easy;
      try now rewrite (Loc.add_compat H (reflexivity _)).
  + intros.
    unfold Loc.t in *.
    split; intro; split; destruct H; simpl in *.
    now rewrite <- H, <- Loc.add_assoc, Loc.add_opp', Loc.add_origin.
    destruct (Nat.eq_dec n 2), (snd y), (snd x); try easy.
    now rewrite <- H, <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
    destruct (Nat.eq_dec n 2), (snd y), (snd x); try easy.
Defined.


(* Definition bij_trans_T := Bijection.bij_id Iso.Req_equiv. *)
Parameter bij_trans_T : Loc.t -> Bijection.t Iso.Req.
Axiom bT_morph : forall c (e:Graph.E),
    (Bijection.section (bij_trans_T c)) (Graph.threshold e) =
    Graph.threshold ((Bijection.section (bij_trans_E c)) e).
Axiom bT_bound : forall c r, (0 < r < 1)%R <->
                             (0 < (Bijection.section (bij_trans_T c) r) < 1)%R.
Axiom bT_crois : forall c a b, (a < b)%R ->
                               ((Bijection.section (bij_trans_T c) a) <
                                (Bijection.section (bij_trans_T c) b))%R.
Axiom bT_compat : forall c1 c2, Bijection.eq (bij_trans_T c1) (bij_trans_T c2).

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
  unfold Loc.t in *.
  destruct (snd e); simpl.
  now rewrite <- Loc.add_assoc, (Loc.add_comm (Z2V 1)), Loc.add_assoc.
  now rewrite <- Loc.add_assoc, (Loc.add_comm (Z2V (-1))), Loc.add_assoc.
  reflexivity.
- intros.
  apply bT_morph.
- apply bT_crois.
- apply bT_bound.
Defined.


Instance trans_compat : Proper (Loc.eq ==> Iso.eq) trans.
Proof.
  intros c1 c2 Hc. unfold Iso.eq, trans. simpl in *.
  repeat split; try apply section_compat.
  unfold Bijection.eq.
  intros x y Hxy. simpl.
  now rewrite Hxy, Hc.
  now simpl; rewrite H, Hc.
  simpl.
  unfold Loc.t.
  destruct H.
  destruct (Nat.eq_dec n 2), (snd y), (snd x); try easy.
  apply bT_compat.
Qed.


(** Formalisation of the exploration with stop *)

Definition Visited_now (loc : Loc.t) (e : execution) :=
  let conf := Stream.hd e in 
    exists g : Names.G, Loc.eq (conf (Good g)).(Config.loc) loc .
    
Instance Visited_now_compat : Proper (Loc.eq ==> eeq ==> iff) Visited_now.
Proof.
intros l1 l2 Hl c1 c2 Hc.
split; intros Hv; unfold Visited_now in *; destruct Hv as (g, Hv); exists g.
rewrite <- Hl, <- Hv; symmetry; now rewrite Hc.
rewrite Hl, <- Hv; now rewrite Hc.
Qed.

Definition Stall (e : execution) :=
    Config.eq (Stream.hd e) (Stream.hd (Stream.tl e)).

Instance Stall_compat : Proper (eeq ==> iff) Stall.
Proof.
intros e1 e2 He. split; intros Hs;
unfold Stall in *.
now rewrite <- He.
now rewrite He.
Qed.

Definition Stopped (e : execution) : Prop :=
  Stream.forever (Stall) e.

Instance Stopped_compat : Proper (eeq ==> iff) Stopped.
Proof.
intros e1 e2 He. split; revert e1 e2 He ; coinduction rec.
  - destruct H. now rewrite <- He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
  - destruct H. now rewrite He.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.

Definition Will_be_visited (loc : Loc.t) (e : execution) : Prop :=
  Stream.eventually (Visited_now loc) e.

Definition Will_stop (e : execution) : Prop :=
  Stream.eventually Stopped e.
 
Instance Will_be_visited_compat : Proper (Loc.eq ==> eeq ==> iff) Will_be_visited.
Proof.
intros l1 l2 Hl. now apply Stream.eventually_compat, Visited_now_compat. 
Qed.

Instance Will_stop_compat : Proper (eeq ==> iff) Will_stop.
Proof.
  apply Stream.eventually_compat, Stopped_compat.
Qed.

(** [Exploration_with_stop e] means that after a finite time, every node of the space has been
  visited, and after that time, all robots will stay at the same place forever*)
Definition FullSolExplorationStop  (r : robogram) := 
forall d config, (forall l, Will_be_visited l (execute r d config)) /\ Will_stop (execute r d config).

Definition Valid_starting_conf conf :=
  forall l',
    (exists l : Loc.t,
    let m := Spect.from_config(conf) l' in
    (snd m)[l] > 1)%nat -> False.

Instance Valid_starting_conf_compat : Proper (Config.eq ==> iff) Valid_starting_conf.
Proof.
  intros c1 c2 Hc.
  split; intros Hv l' Hf; unfold Valid_starting_conf in *;
  destruct (Hv l'), Hf  as (l ,Hf); exists l; simpl in *; try now rewrite <- Hc.
  now rewrite Hc.
Qed.
  
Definition Explores_and_stop (r : robogram) :=
  forall d config,
    Valid_starting_conf config ->
    Fair d -> 
    (forall l, Will_be_visited l (execute r d config)) /\
    Will_stop (execute r d config).

Definition HasBeenVisited loc e :=
  forall (conf : Config.t) r d,
    e = execute r d conf -> 
  exists conf_start,
    let e_start := execute r d conf_start in
    Stream.eventually (fun e1 => Config.eq (Stream.hd e1) conf) e_start
    -> forall l, (((snd (Spect.from_config(conf_start) l))[loc])>0)%nat.

End ExplorationDefs.



 
                                                                            