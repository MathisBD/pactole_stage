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
(*
Lemma Loc_eq_mod : forall x, ImpossibilityKDividesN.Loc.eq x (x mod Z.of_nat n).
Proof.
  intros; unfold ImpossibilityKDividesN.Loc.eq; rewrite Z.mod_mod;
    generalize ImpossibilityKDividesN.n_sup_1; unfold ImpossibilityKDividesN.def.n;
      lia.
Qed.

Module Loc <: DecidableType.
  Definition t := LocationA.t.
  Definition eq := LocationA.eq.
  Definition eq_dec : forall x y, {eq x y} + {~eq x y} := LocationA.eq_dec.
  Definition eq_equiv : Equivalence eq := LocationA.eq_equiv.
  Definition origin := Loc_inv Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.origin.

  Definition add (x y : t) := Loc_inv ((ZnZ.ImpossibilityKDividesN.Loc.add (Loc x) (Loc y)) mod Z.of_nat n)%Z.
  Definition mul (x y : t) := Loc_inv ((ZnZ.ImpossibilityKDividesN.Loc.mul (Loc x) (Loc y)) mod (Z.of_nat n))%Z.
  Definition unit := Loc_inv (ZnZ.ImpossibilityKDividesN.Loc.unit mod Z.of_nat n)%Z.
  Definition opp (x : t) := Loc_inv ((ZnZ.ImpossibilityKDividesN.Loc.opp (Loc x)) mod Z.of_nat n)%Z.

  Instance add_compat : Proper (eq ==> eq ==> Veq) add.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold Veq, add.
    rewrite <- 2 loc_fin.
    unfold ImpossibilityKDividesN.Loc.eq.
    rewrite <- 4 Loc_eq_mod.
    now rewrite (ImpossibilityKDividesN.Loc.add_compat _ _ (Loc_compat Hx)
                                                   _ _ (Loc_compat Hy)).
  Qed.

  Instance mul_compat : Proper (eq ==> eq ==> Veq) mul.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold Veq, mul.
    rewrite <- 2 loc_fin.
    unfold ImpossibilityKDividesN.Loc.eq.
    rewrite <- 4 Loc_eq_mod.
    unfold ImpossibilityKDividesN.Loc.mul.
    rewrite 2 (Z.mul_mod (Loc _) _), (Loc_compat Hx), (Loc_compat Hy);
      try (generalize ImpossibilityKDividesN.n_sup_1;
           unfold ImpossibilityKDividesN.def.n, n; lia).
  Qed.

  Instance opp_compat : Proper (eq ==> Veq) opp.
  Proof.
    intros x y Hxy.
    unfold Veq, opp.
    rewrite <- 2 loc_fin.
    unfold ImpossibilityKDividesN.Loc.eq.
    rewrite <- 4 Loc_eq_mod.
    now rewrite (ImpossibilityKDividesN.Loc.opp_compat _ _ (Loc_compat Hxy)).
  Qed.

  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, add in *.
    repeat rewrite <- loc_fin in *.
    apply (Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_reg_l (Loc w)).
    unfold ImpossibilityKDividesN.Loc.add in *.
    unfold ImpossibilityKDividesN.Loc.eq in *; 
    rewrite 6 Z.mod_mod in *;
    generalize ImpossibilityKDividesN.n_sup_1;
    unfold ImpossibilityKDividesN.def.n; try omega.
    intros; assumption.
  Qed.

  
  Lemma add_comm : forall u v, eq (add u v) (add v u). 
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, add.
    rewrite <- 2 loc_fin.
    unfold ImpossibilityKDividesN.Loc.eq, n.
    rewrite 2 Z.mod_mod;
      unfold Loc.eq, ImpossibilityKDividesN.def.n in *;
      try rewrite 2 Z.mod_mod in *;
      try (generalize ImpossibilityKDividesN.n_sup_1;
           unfold ImpossibilityKDividesN.def.n; lia).
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_comm.
  Qed.
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v))
                                       (add (opp u) (opp v)).
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq.
    unfold opp, add.
    unfold n.
    repeat rewrite <- loc_fin.
    unfold ImpossibilityKDividesN.Loc.eq, ImpossibilityKDividesN.def.n.
    repeat fold n Loc.opp.
    rewrite 7 Z.mod_mod;
    unfold ImpossibilityKDividesN.Loc.add;
      try (rewrite <- Zdiv.Zplus_mod);
      try (generalize ImpossibilityKDividesN.n_sup_1;
           unfold n, ImpossibilityKDividesN.def.n; lia).
    generalize (Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp_distr_add (Loc u) (Loc v)).
    unfold ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.eq, n,
      ImpossibilityKDividesN.def.n in *;
      intros Hfin; rewrite 2 Z.mod_mod in *; try apply Hfin;
        try (generalize ImpossibilityKDividesN.n_sup_1;
             unfold n, ImpossibilityKDividesN.def.n; lia).
  Qed.


    
  Lemma add_assoc : forall u v w, eq (add u (add v w))
                                     (add (add u v) w).
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, opp, add.
    repeat rewrite <- loc_fin.
    repeat rewrite <- Loc_eq_mod.
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_assoc.
  Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, origin, add.
    repeat rewrite <- loc_fin.
    repeat rewrite <- Loc_eq_mod.
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_origin.
  Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, origin, add, opp.
    repeat rewrite <- loc_fin; repeat rewrite <- Loc_eq_mod.
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add_opp.
  Qed.
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof.
    intros.
    unfold eq, LocationA.eq, MakeRing.Veq, origin, add, opp.
    repeat rewrite <- loc_fin.
    repeat rewrite <- Loc_eq_mod.
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp_opp.
  Qed.
  
End Loc.

  
Module N : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End N.

Module Names := Robots.Make (N).

Module ConfigA := Configurations.Make (LocationA)(N)(Names).

*)
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



(* Module Export Common := CommonFormalism.Make(Loc)(N)(Names)(Config)(Spect). *)
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
  Stream.forever (stop_now) e.

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
Definition FullSolExplorationStop  (r : robogram) := 
forall d config, (forall l, Will_be_visited l (execute r d config)) /\ Will_stop (execute r d config).

Definition ValidStartingConf conf :=
  forall l',
    (exists l : Loc.t,
    let m := Spect.from_config(conf) l' in
    (snd m)[l] > 1)%nat -> False.

Instance ValidStartingConf_compat : Proper (Config.eq ==> iff) ValidStartingConf.
Proof.
  intros c1 c2 Hc.
  split; intros Hv l' Hf; unfold ValidStartingConf in *;
  destruct (Hv l'), Hf  as (l ,Hf); exists l; simpl in *; try now rewrite <- Hc.
  now rewrite Hc.
Qed.
  
Definition ValidStartingConfSolExplorationStop (r : robogram) :=
  forall d config,
    ValidStartingConf config -> 
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



 
                                                                            