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
Require Import Pactole.DiscreteGraphFormalism.
Require Import Arith.Div2.
Require Import Pactole.DiscreteSimilarity.
Require Import Pactole.CommonDiscreteFormalism.
Require Import Pactole.DiscreteRigidFormalism.
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.CommonIsoGraphFormalism.
Require Import Stream.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.
Require Import Pactole.GraphEquivalence.

Close Scope Z_scope.
Set Implicit Arguments.

Module Graph := MakeRing.
Import Graph.

Module ExplorationDefs(N : Size).

Module Names := Robots.Make(N).
  
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

  Definition add (x y : t) := Loc_inv ((Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.add (Loc x) (Loc y)) mod Z.of_nat n)%Z.
  Definition mul (x y : t) := Loc_inv ((Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.mul (Loc x) (Loc y)) mod (Z.of_nat n))%Z.
  Definition unit := Loc_inv (Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.unit mod Z.of_nat n)%Z.
  Definition opp (x : t) := Loc_inv ((Pactole.Exploration.ZnZ.ImpossibilityKDividesN.Loc.opp (Loc x)) mod Z.of_nat n)%Z.

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

Module Iso := CommonIsoGraphFormalism.Make(Graph)(Loc).
Module MkInfo := CommonGraphFormalism.Make(Graph)(LocationA).
Module Info := MkInfo.Info.
Module Config := Configurations.Make(Loc)(N)(Names)(Info).
Module Equiv := GraphEquivalence (Graph)(N)(Names)(Loc)(MkInfo)(Config)(Iso).
Import Equiv Iso.
Import Equiv.DGF.


Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Definition bij_trans_V (c : Loc.t) : Isomorphism.bijection Veq.
refine {|
  Isomorphism.section := fun x => (Loc.add x (Loc.opp c));
  Isomorphism.retraction := fun x => Loc.add x c |}.
Proof.
  + intros x y Hxy. unfold Veq, Loc.add, Loc.opp in *.
    rewrite <- 3 loc_fin.
    unfold Loc.add, ImpossibilityKDividesN.Loc.add.
    rewrite <- (Zdiv.Zplus_mod_idemp_l), Hxy,
    Zdiv.Zplus_mod_idemp_l.
    reflexivity.
  + intros x y; split; unfold Veq, Loc.opp, Loc.add;
      repeat rewrite <- loc_fin in *; intro Heq;
    repeat rewrite <- Loc_eq_mod in *;
    rewrite <- Heq;
    try (rewrite <- ImpossibilityKDividesN.Loc.add_assoc).
    rewrite (ImpossibilityKDividesN.Loc.add_comm (ImpossibilityKDividesN.Loc.opp _)).
    rewrite ImpossibilityKDividesN.Loc.add_opp, ImpossibilityKDividesN.Loc.add_origin.
    easy.
    unfold Loc.add, Loc.opp in *.
    repeat rewrite <- loc_fin in *.
    rewrite ImpossibilityKDividesN.Loc.add_opp.
    apply ImpossibilityKDividesN.Loc.add_origin.
Defined.


Lemma Loc_opp_mod : forall x,
    ImpossibilityKDividesN.Loc.eq
      ((ImpossibilityKDividesN.Loc.opp x) mod Z.of_nat ImpossibilityKDividesN.def.n)
      (ImpossibilityKDividesN.Loc.opp x).
Proof.
  intros.
  unfold ImpossibilityKDividesN.Loc.eq.
  rewrite Z.mod_mod; generalize ImpossibilityKDividesN.n_sup_1;
    unfold ImpossibilityKDividesN.def.n; omega.
Qed.

Definition bij_trans_E (c : Loc.t) : Isomorphism.bijection Graph.Eeq.
  refine {|
      Isomorphism.section := fun x =>  (Loc.add (fst x) (Loc.opp c), snd x);
      Isomorphism.retraction := fun x => (Loc.add (fst x) c, snd x) |}.
Proof.
  + intros e1 e2 He_eq.
    unfold Loc.add, Loc.opp.
    unfold Graph.Eeq.
    split; unfold Veq; simpl. repeat rewrite <- loc_fin.
    destruct He_eq.
    unfold Loc.t, LocationA.t,V in *.
    unfold n, MakeRing.n, ImpossibilityKDividesN.Loc.add in *.
    now rewrite <- Zdiv.Zplus_mod_idemp_l, H, Zdiv.Zplus_mod_idemp_l.
    destruct He_eq.
    now unfold Loc.t, LocationA.t in *.
  + intros.
    unfold Loc.t, LocationA.t, Graph.V, Graph.E, Graph.dir in *.
    unfold Eeq, Veq; simpl.
    repeat rewrite <- loc_fin.
    split;
    intros;
    unfold Graph.Eeq, Graph.src in *; destruct H; split; simpl in *;
      unfold Loc.add,V,n, Loc.opp in *; try rewrite <- loc_fin in *;
        try rewrite <- Loc_eq_mod in *; try rewrite <- loc_fin in *;
          try rewrite <- Loc_eq_mod in *.
    rewrite <- H.
    rewrite ImpossibilityKDividesN.Loc.add_comm,
    (ImpossibilityKDividesN.Loc.add_comm (Loc (fst x))).
    unfold ImpossibilityKDividesN.Loc.eq.
    assert (Hac := ImpossibilityKDividesN.Loc.add_compat).
    specialize (Hac (ImpossibilityKDividesN.Loc.opp (Loc c)
                                                    mod Z.of_nat ImpossibilityKDividesN.def.n)%Z
                    (ImpossibilityKDividesN.Loc.opp (Loc c))
                    (symmetry (Loc_eq_mod (ImpossibilityKDividesN.Loc.opp (Loc c))))
    (Loc (fst x)) _ (reflexivity _)).
    rewrite Hac.
    assert (Hl := (Loc_eq_mod)).
    unfold n in Hl.
    fold ImpossibilityKDividesN.def.n in Hl.
    clear Hac.
    rewrite Loc_eq_mod.
    unfold n; fold ImpossibilityKDividesN.def.n.
    unfold ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp.
    rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same; simpl;
    try (rewrite Zdiv.Zplus_mod_idemp_l, 2 Zdiv.Zplus_mod_idemp_r, 2 Z.mod_mod);
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold ImpossibilityKDividesN.def.n; omega).
    now rewrite Z.add_opp_l, Zplus_minus.
    now symmetry.
    rewrite (ImpossibilityKDividesN.Loc.add_compat _ _ (symmetry H)
                                                   _ _ (reflexivity _)).
    unfold ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp.
    rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same;
    try (rewrite 2 Z.mod_mod, <- Zdiv.Zplus_mod); simpl;
    replace (Loc (fst y) + Loc c + - Loc c)%Z with (Loc (fst y)) by lia;
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold ImpossibilityKDividesN.def.n; lia);
    try now rewrite <- Loc_eq_mod.
    now symmetry.
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
  unfold Loc.t, V, LocationA.t, MakeRing.V, Graph.E, MakeRing.E, Graph.dir, Veq,
    Loc.add, Loc.opp in *.
  repeat rewrite <- loc_fin.
  destruct (snd e) eqn : Hsnd;
    unfold V in *;
    rewrite Hsnd in *;
    simpl in *;
    unfold ImpossibilityKDividesN.Loc.eq;
      repeat rewrite <- loc_fin;
    unfold ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp;
    repeat (rewrite <- (Zdiv.Zplus_mod_idemp_l (Loc (Loc_inv _))), <- loc_fin,
           Zdiv.Zplus_mod_idemp_l);
    repeat (rewrite <- (Zdiv.Zplus_mod_idemp_r (Loc (Loc_inv _))), <- loc_fin,
            Zdiv.Zplus_mod_idemp_r);
    set (N := Z.of_nat ImpossibilityKDividesN.def.n);
    try (rewrite <- Zdiv.Zplus_mod_idemp_r with (a := (N - Loc c)%Z);
    (rewrite <- (Zdiv.Zminus_mod_idemp_l N), Z.mod_same);
    repeat rewrite Z.mod_mod; try (unfold N, ImpossibilityKDividesN.def.n;
      generalize ImpossibilityKDividesN.n_sup_1; lia)); simpl;
      try rewrite Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l;
      try (repeat rewrite Z.mod_mod; try (unfold N, n, ImpossibilityKDividesN.def.n;
      generalize ImpossibilityKDividesN.n_sup_1; lia)).
  repeat rewrite Zdiv.Zplus_mod_idemp_l; repeat rewrite Zdiv.Zplus_mod_idemp_r.
  now rewrite 2 Z.add_comm with (m := 1%Z), <- Zplus_assoc_reverse,
                            Zdiv.Zplus_mod_idemp_r.
  repeat rewrite Zdiv.Zplus_mod_idemp_l; repeat rewrite Zdiv.Zplus_mod_idemp_r.
  now rewrite 2 Z.add_comm with (m := (-1)%Z), <- Zplus_assoc_reverse,
                                  Zdiv.Zplus_mod_idemp_r.
- intros.
  apply bT_morph.
- apply bT_crois.
- apply bT_bound.
Defined.


Instance trans_compat : Proper (Loc.eq ==> Iso.eq) trans.
Proof.
  intros c1 c2 Hc. unfold Iso.eq, trans. simpl in *.
  repeat split; try apply Isomorphism.section_compat.
  unfold Isomorphism.bij_eq.
  intros x y Hxy. simpl.
  unfold Iso.eq;
  unfold Loc.eq, LocationA.eq, MakeRing.Veq, Loc.add, Loc.opp in *;
  repeat rewrite <- loc_fin.
  unfold n; fold ImpossibilityKDividesN.def.n.
  rewrite ( (ImpossibilityKDividesN.Loc.opp_compat (Loc c1) (Loc c2) Hc)).
  rewrite (ImpossibilityKDividesN.Loc.add_compat
               (Loc x) (Loc y) Hxy
               _ _ (reflexivity _)).
  reflexivity.
  destruct H.
  simpl.
  unfold Loc.eq, LocationA.eq, Veq, Loc.add, Loc.opp in *; repeat rewrite <- loc_fin.
  simpl.
  unfold n; fold ImpossibilityKDividesN.def.n.
  rewrite ( (ImpossibilityKDividesN.Loc.opp_compat (Loc c1) (Loc c2) Hc)).
  rewrite (ImpossibilityKDividesN.Loc.add_compat
               (Loc (fst x)) (Loc (fst y)) H
               _ _ (reflexivity _)).
  reflexivity.
  unfold bij_trans_E in *; simpl in *.  
  unfold Loc.add, ImpossibilityKDividesN.Loc.add.
  now destruct H.
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
    Config.eq (Stream.hd e) (Stream.hd (Stream.tl (Stream.tl e))).

Instance stop_now_compat : Proper (eeq ==> iff) stop_now.
Proof.
intros e1 e2 He. split; intros Hs;
unfold stop_now in *.
now rewrite <- He.
now rewrite He.
Qed.

Definition Stopped (e : execution) : Prop :=
  Stream.next_forever ((stop_now)) e.

Instance Stopped_compat : Proper (eeq ==> iff) Stopped.
Proof.
intros e1 e2 He. split; revert e1 e2 He ; coinduction rec.
  - destruct H. now rewrite <- He.
  - destruct H as [_ H], He as [_ [_ He]]. apply (rec _ _ He H).
  - destruct H. now rewrite He.
  - destruct H as [_ H], He as [_ [_ He]]. apply (rec _ _ He H).
Qed.

Definition Will_be_visited (loc : Loc.t) (e : execution) : Prop :=
  Stream.eventually (is_visited loc) e.

Definition Will_stop (e : execution) : Prop :=
  Stream.next_eventually Stopped e.
 
Instance Will_be_visited_compat : Proper (Loc.eq ==> eeq ==> iff) Will_be_visited.
Proof.
intros l1 l2 Hl. now apply Stream.eventually_compat, is_visited_compat. 
Qed.

Instance Will_stop_compat : Proper (eeq ==> iff) Will_stop.
Proof.
  apply Stream.next_eventually_compat, Stopped_compat.
Qed.

(* [Exploration_with_stop e] mean that after a finite time, every node of the space has been
  visited, and after that time, all robots will stay at the same place forever*)
Definition FullSolExplorationStop  (r : robogram) (d : demon) := 
forall config, (forall l, Will_be_visited l (execute r d config)) /\ Will_stop (execute r d config).

Definition ValidStartingConf conf :=
  exists l : Loc.t,
    let m := Spect.from_config(conf) in
    m[l] > 1 -> False.

Instance ValidStartingConf_compat : Proper (Config.eq ==> iff) ValidStartingConf.
Proof.
  intros c1 c2 Hc.
  split; intros Hv; unfold ValidStartingConf in *;
  destruct Hv as (l, Hv); exists l; try now rewrite <- Hc.
  now rewrite Hc.
Qed.
  
Definition ValidStartingConfSolExplorationStop (r : robogram) (d : demon) :=
  forall config,
    ValidStartingConf config -> 
    (forall l, Will_be_visited l (execute r d config)) /\
    Will_stop (execute r d config).

Definition HasBeenVisited loc e :=
  forall (conf : Config.t) r d,
    e = execute r d conf -> 
  exists conf_start,
    let e_start := execute r d conf_start in
    Stream.eventually (fun e1 => Config.eq (Stream.hd e1) conf) e_start
    -> ((Spect.from_config(conf_start))[loc])>0.

End ExplorationDefs.

 
                                                                            