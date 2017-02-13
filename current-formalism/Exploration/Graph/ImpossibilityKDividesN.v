(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain, R. Pelle                  *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* 

1/ Spécifier/utiliser Config1 non plus en dur mais en fonction des hypothèses qui la caractérisent.

2/ Faire plus de lemmes intermédiaires.

3/ Bien nommer tous mes lemmes, objets et asserts.

4/ Commenter le code : - dire ce que fait chaque lemme important
                       - commecer par la fin (comme avec la preuve)
*)

Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
(* Require Import List SetoidList. *)
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid Compare_dec Morphisms FinFun.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.ZnZ.Definitions.
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
Require Import Pactole.Exploration.Graph.Definitions.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.

Set Implicit Arguments.
(* taille de l'anneau*)


Definition n := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.n.
Definition kG := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.kG.

Module K := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.K.

Module def : RingDef with Definition n := n.
 Definition n:= n.
 Lemma n_pos : n <> 0. Proof. unfold n, Top.n. generalize n_sup_1. omega. Qed.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
End def.

Module Gra := MakeRing.
(** The setting is a ring. *)
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
End Loc.
  (** There are KG good robots and no byzantine ones. *)


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(Gra)(Loc)(K).
Export DefsE.

Ltac ImpByz b := 
  assert (Hfalse := Names.Bnames_length);
  assert (Hfalse' := Names.In_Bnames b);
  unfold Names.Bnames, K.nB in *;
  apply length_0 in Hfalse;
  rewrite Hfalse in Hfalse';
  apply in_nil in Hfalse';
  now exfalso.

(* As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_conf {A} (conf : Names.G -> A) : Names.ident -> A := fun id =>
  match id with
    | Good g => conf g
    | Byz b => Fin.case0 _ b
  end.

Section Exploration.
Open Scope Z_scope.

  
Definition create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (((Z_of_nat ((proj1_sig (Fin.to_nat f))*(n / kG))))) Loc.unit.


(* the starting configuration where a robots is on the origin, 
   and every other robot is at a distance of [x*(kG/n)] where x is between 1 and kG *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := Loc.add Loc.unit pos |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
            end.

Lemma conf1_new_aux:
  forall gg: nat,  
    (Loc.mul (((Z_of_nat (gg*(n / kG))))) Loc.unit) mod Z.of_nat (n/kG) = 0.
Proof.
  intros.  
  unfold Loc.unit, Loc.mul.
  apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_new_aux.
Qed.



(* A position where a robot is in config1 divied [k/n] *)
Lemma conf1_new_1 : forall g0: Names.G, (create_conf1 g0) mod Z.of_nat (n/kG) = 0. 
Proof.
  intros g0.
  unfold create_conf1.
  apply conf1_new_aux.
Qed.


Lemma conf_aux : forall m k, (1 < k)%nat -> (m < k)%nat ->
                             exists g: Fin.t k, proj1_sig (Fin.to_nat g) = m.
Proof.
  intros n m  Hk Hm.
  exists (Fin.of_nat_lt Hm).
  rewrite Fin.to_nat_of_nat.
  simpl in *.
  reflexivity.
Qed.


(* if a position divides [n/kG] then a robot is at this position in config1 *)
Lemma conf1_new_2 : forall loc, loc mod Z.of_nat (n / kG) = 0 ->
                                exists g:Names.G, Loc.eq (create_conf1 g) loc.
Proof.
  intros loc Hmod.
  generalize Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_new_2.
  intros.
  specialize (H loc).
  unfold Loc.eq, LocationA.eq, MakeRing.Veq.
  apply H.
  unfold n, kG; apply Hmod.
Qed.



Lemma conf1_inf_n : forall g:Names.G,
    (Z.of_nat ((proj1_sig (Fin.to_nat g)) * (n / kG)) * 1) < Z.of_nat n.
Proof.
  unfold n, kG; apply
                  Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_inf_n.
Qed.


(* an Injection theorem about config1 *)
Lemma unique_g : forall g1 g2,
               g1 <> g2 -> Loc.eq (Config.loc (config1 (Good g1)))
                                  (Config.loc (config1 (Good g2))) -> False.
Proof.
  unfold Loc.eq, LocationA.eq, MakeRing.Veq.
  apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.unique_g.
Qed.


(* The same that [NoDup_count_occ'] but with the abstraction. *)

Parameter g : Names.G.


Variable r : Atom.robogram.
Definition move := r (!! config1).

Parameter m : Z.
Hypothesis Hmove : move = m.

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Lemma conf1_1 : forall idg g0: Names.G, exists g2:Names.G,
      Loc.eq (create_conf1 idg)
             (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g2))).
Proof.                                                                    
  unfold Loc.eq, LocationA.eq, MakeRing.Veq;
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_1.
Qed.

Lemma mod_min_eq : forall a b c, (a-b)mod Z.of_nat n = (a-c) mod Z.of_nat n ->
                                 - Z.of_nat n < a - c < Z.of_nat n ->
                                 - Z.of_nat n < a - b < Z.of_nat n ->
                                 c mod Z.of_nat n = b mod Z.of_nat n.
Proof.
  unfold n; apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.mod_min_eq.
Qed.

Lemma unique_g_2 : forall g0 g1 g2 : Names.G,
    g1 <> g2 -> Loc.eq (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g1)))
                       (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g2)))
    -> False.
Proof.
  unfold Loc.eq, LocationA.eq, MakeRing.Veq;
    apply Pactole.Exploration.ZnZ.ImpossibilityKDividesN.unique_g_2.
Qed.


(* The spectre of the initial configuration is the same that the one during 
   its computaion [round]. *)




Definition da1 : demonic_action.

simple refine {|
  relocate_byz := fun b => Loc.origin;
  step :=  (lift_conf (fun (_ : Names.G) Rconf =>
                           if Loc.eq_dec (Config.loc (Rconf))
                                  (Config.target (Config.robot_info (Rconf)))
                           then Active _ 
                           else Moving true ))|}.
Proof.
  - intuition.
  - intros.
    unfold lift_conf in *.
    destruct (Loc.eq_dec (Config.loc Rconfig) (Config.target (Config.robot_info Rconfig))).
    unfold Location.eq, Gra.Veq, Loc.eq, LocationA.eq, MakeRing.Veq in *.
    assumption.
    discriminate.
  - intros [g1|b1] [g2|b2] Hg rc1 rc2 Hrc; try discriminate; simpl in *.
    destruct Hrc, H0, (Loc.eq_dec (Config.loc rc1) (Config.target (Config.robot_info rc1))) , (Loc.eq_dec (Config.loc rc2) (Config.target (Config.robot_info rc2))); try (now auto);
    unfold Gra.Veq, Loc.eq, LocationA.eq, MakeRing.Veq in *.
    rewrite H, H1 in e.
    contradiction.
    rewrite <-H, <-H1 in e.
    contradiction.
    apply Fin.case0. exact b1.    
Defined.

CoFixpoint bad_demon1 : demon := NextDemon da1 bad_demon1.

Lemma bad_demon1_tail : demon_tail bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.

Lemma bad_demon1_head : demon_head bad_demon1 = da1.
Proof. reflexivity. Qed.

(*
Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof.
coinduction bad_fair1.
intros id1 id2. constructor. destruct id1; simpl. discriminate. apply Fin.case0. exact b.
Qed.

Theorem kFair_bad_demon : kFair 1 bad_demon1.
Proof.
intros. unfold bad_demon1.
- apply kFair_mon with 0%nat. exact kFair_bad_demon1. omega.
Qed.

Theorem kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon1.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon;auto.
- auto.
Qed.
*)
Lemma config1_ne_unit : Z_of_nat (n mod kG) = 0 ->
      forall g:Names.G, ~ Loc.eq (create_conf1 g) Loc.unit.
Proof.
  intros Hmod g.
  induction g.
  + simpl in *.
    unfold create_conf1.
    simpl in *.
    unfold Loc.mul, Loc.eq, Loc.unit, def.n.
    rewrite Z.mod_mod.
    simpl in *.
    rewrite Z.mod_0_l, Z.mod_1_l.
    omega.
    generalize n_sup_1; omega.
    generalize n_sup_1; omega.
    generalize n_sup_1; omega.
  +  simpl in *.
     generalize k_sup_1, k_inf_n, n_sup_1.
     intros.
     unfold create_conf1.
     unfold Loc.eq, Loc.mul, Loc.unit, def.n. 
     rewrite Zdiv.mod_Zmod in Hmod; try omega.
     rewrite Zdiv.Zmod_divides in *; try omega.
     rewrite Z.mod_mod.
     destruct Hmod.
     rewrite Nat2Z.inj_mul, Zdiv.div_Zdiv; try omega.
     rewrite H2 in *.
     replace (Z.of_nat kG * x ) with (x * Z.of_nat kG) by intuition.
     rewrite Zdiv.Z_div_mult_full.
     replace (x * Z.of_nat kG) with (Z.of_nat kG * x) by intuition.
     rewrite Z.mul_1_r.
     rewrite Zdiv.Zmult_mod_distr_r.
     assert (1 < x).
     assert (Z.of_nat kG < Z.of_nat n) by omega.
     apply Zmult_lt_reg_r with (p := Z.of_nat kG); try omega.
     rewrite Z.mul_comm with (n:= x).
     rewrite <- H2.
     omega.
     rewrite Zdiv.Zmod_1_l; try omega.
     intuition.
     rewrite Z.mul_comm in H4.
     apply Z.eq_mul_1 in H4.
     destruct H4; omega.
     omega.
     omega.
Qed.

(** **  First case: the robots moves **)

Lemma neq_a_1a : forall a, ~Loc.eq a (Loc.add Loc.unit a).
Proof.
generalize n_sup_1.
intros.
unfold Loc.eq, Loc.add, def.n, Loc.unit.
rewrite Z.mod_mod, <- Zdiv.Zplus_mod_idemp_r; try omega.
destruct (a mod Z.of_nat n ?= Z.of_nat n) eqn : Hn;
try rewrite Z.compare_lt_iff in *;
try rewrite Z.compare_eq_iff in *;
try rewrite Z.compare_gt_iff in *.
+ rewrite Hn, <- Zdiv.Zplus_mod_idemp_r, Zdiv.Z_mod_same_full.
  simpl in *; rewrite Z.mod_1_l;
  omega.
+ destruct (a mod Z.of_nat n) eqn : Hp.
  - simpl in *.
    rewrite Z.mod_1_l; omega.
  - apply Zlt_le_succ in Hn.
    unfold Z.succ in Hn.
    apply Zle_lt_or_eq in Hn.
    destruct Hn.
    rewrite Zdiv.Zmod_small; try split; try omega.
    apply Zle_0_pos.
    rewrite Z.add_comm, H0, Zdiv.Z_mod_same_full.
    generalize Zle_0_pos.
    omega.
  - assert (Hn0: 0 < Z.of_nat n) by omega.
    generalize (Z.mod_pos_bound a (Z.of_nat n) Hn0); intros.
    rewrite Hp in H0.
    generalize (Pos2Z.neg_is_neg p).
    omega.
+ assert (Hn0: 0 < Z.of_nat n) by omega.
  generalize (Z.mod_pos_bound a (Z.of_nat n) Hn0); intros.
  omega.
Qed.

Section Move1.
  
Hypothesis Hm : m mod (Z.of_nat n) <> 0.








Lemma neq_a_a1 : forall a, ~Loc.eq a (a - 1).
Proof.
generalize n_sup_1.
intros.
unfold Loc.eq, Loc.add, def.n, Loc.unit.
rewrite <- Zdiv.Zminus_mod_idemp_l; try omega.
destruct (a mod Z.of_nat n ?= Z.of_nat n) eqn : Hn;
try rewrite Z.compare_lt_iff in *;
try rewrite Z.compare_eq_iff in *;
try rewrite Z.compare_gt_iff in *.
+ rewrite Hn, Zdiv.Zmod_small; omega.
+ destruct (a mod Z.of_nat n) eqn : Hp.
  - rewrite <- Zdiv.Z_mod_same_full with (a:= Z.of_nat n) at 2.
    rewrite Zdiv.Zminus_mod_idemp_l, Zdiv.Zmod_small; omega.
  - rewrite Zdiv.Zmod_small; try omega.
    generalize (Pos2Z.is_pos p); omega.
  - assert (Hn0: 0 < Z.of_nat n) by omega.
    generalize (Z.mod_pos_bound a (Z.of_nat n) Hn0); intros.
    rewrite Hp in H0.
    generalize (Pos2Z.neg_is_neg p).
    omega.
+ assert (Hn0: 0 < Z.of_nat n) by omega.
  generalize (Z.mod_pos_bound a (Z.of_nat n) Hn0); intros.
  omega.
Qed.


Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").

(* This function moves every robots of [k] nodes. *)
Definition f_conf conf k : Config.t :=
  fun id =>
      match id with
      | Good g => {| Config.loc := Loc.add k (Config.loc (conf (Good g)));
                     Config.robot_info := Config.robot_info (conf (Good g)) |}
      | Byz b => conf (Byz b)
      end.

Instance f_conf_compat : Proper (Config.eq ==> Z.eq ==> Config.eq) f_conf.
Proof.
  intros c1 c2 Hc k1 k2 Hk.
  unfold f_conf.
  unfold Config.eq.
  intros [g|b]; try ImpByz b.
  split; simpl in *.
  rewrite Hk.
  destruct (Hc (Good g)) as (Hc',_). 
  rewrite Hc'.
  reflexivity.
  now destruct (Hc (Good g)) as (_,Hc'); rewrite Hc'.
Qed.


(* Two configuration are equivalent if all robots of the first are moved of the same [k] numbur to have the second. *)
Definition equiv_conf conf1 conf2: Prop := exists k, Config.eq conf2 (f_conf conf1 k).


(* the same than [count_occ_map], but with the abstraction. *)

Lemma countA_occ_map : forall (A B: Type) (f : A -> B) (eqA : A -> A -> Prop)
                     (eqB : B -> B -> Prop)
                     (decA : forall x x' : A, {eqA x x'} + {~eqA x x'})
                     (decB : forall y y' : B, {eqB y y'} + {~eqB y y'}),
                     (forall x1 x2 : A, eqB (f x1) (f x2) <-> eqA x1 x2) ->
                     forall (l : list A), Equivalence eqA -> Equivalence eqB ->
                                        forall x, countA_occ eqA decA x l =
                                                  countA_occ eqB decB (f x) (map f l).
Proof.
  intros. 
  unfold countA_occ.
  induction l.
  + simpl in *.
    reflexivity.
  + destruct (decA a x) eqn : HdecA;
      rewrite map_cons.
    - destruct (decB (f a) (f x)) eqn : HdecB.
      * f_equiv.
        apply IHl.
      * destruct n0.
        now rewrite H.
    - destruct (decB (f a) (f x)) eqn : HdecB.
      destruct n0.
      now rewrite <- H.
      apply IHl.
Qed.


(* utiliser le prédicat d'équivalence (equiv_conf) pour prouver le spectre. *)


  
Lemma round1_move_g : forall g0, Loc.eq (Config.loc (round r da1 config1 (Good g0)))
                        (Loc.add (Config.loc (config1 (Good g0))) (Loc.opp m)).
Proof.
  intros g0.
  unfold move in Hmove.
  simpl in *.
  unfold Loc.add, Loc.opp, Loc.unit.
  generalize spect_rotation; intro.
  assert (Hpgm := pgm_compat r (H g0)).
  rewrite <- Zdiv.Zminus_mod_idemp_r.
  rewrite <- Hpgm, Hmove.
  rewrite Zdiv.Zminus_mod_idemp_r.
  reflexivity.
Qed.

Lemma moving_no_stop : ~Stopped (execute r bad_demon1 config1).
Proof.
  intros Hs.
  generalize n_sup_1; intros Hn1.
  destruct Hs as (Hs, _).
  unfold stop_now in Hs.
  simpl in *.
  specialize (Hs (Good g)).
  unfold Config.eq_RobotConf in Hs.
  destruct Hs as (Hs, _).
  rewrite round1_move_g in Hs.
  unfold Loc.add, Loc.opp, Loc.unit, def.n in *.
  rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same in Hs.
  simpl in *.
  rewrite Zdiv.Zplus_mod_idemp_r in Hs.
  rewrite Z.add_opp_r in Hs.
  unfold Loc.eq in *.
  rewrite Z.mod_mod in Hs.
  assert (0 < (m mod Z.of_nat def.n) < Z.of_nat def.n).
  split.
  assert (Z.of_nat def.n > 0) by (generalize n_sup_1; unfold def.n ; omega).
  generalize (Zdiv.Z_mod_lt m (Z.of_nat def.n) H).
  unfold def.n.
  omega.
  apply Zdiv.Z_mod_lt.
  generalize n_sup_1; unfold def.n; omega.
  rewrite Zdiv.Zminus_mod in Hs.
  destruct ((create_conf1 g) mod Z.of_nat def.n ?= (m mod Z.of_nat def.n)) eqn : Hcompare_conf1_m;
    try rewrite Z.compare_eq_iff in *;
    try rewrite Z.compare_gt_iff in *;
    try rewrite Z.compare_lt_iff in *.
  + (* rewrite <- Hcompare_conf1_m in Hm_mod. *)
    rewrite <- Hcompare_conf1_m, Z.sub_diag, Z.mod_0_l in Hs.
    omega.
    unfold def.n; generalize n_sup_1; omega.
  + rewrite <- Z.lt_sub_0 in Hcompare_conf1_m.
    rewrite Z.add_lt_mono_l with (p := Z.of_nat def.n) in Hcompare_conf1_m.
    simpl in *.
    replace (create_conf1 g mod Z.of_nat def.n - m mod Z.of_nat def.n) with
    (0 + (create_conf1 g mod Z.of_nat def.n - m mod Z.of_nat def.n)) in Hs by omega.
    rewrite <- Z.mod_same with (a := Z.of_nat def.n) in Hs.
    assert (- Z.of_nat def.n < create_conf1 g mod Z.of_nat def.n - m mod Z.of_nat def.n).
    assert (0 <= create_conf1 g mod Z.of_nat def.n).
    apply Zdiv.Z_mod_lt.
    unfold def.n; generalize n_sup_1; omega.
    omega.
    rewrite Zdiv.Zplus_mod_idemp_l in Hs.
    rewrite Z.mod_small with (a :=  (Z.of_nat def.n + (create_conf1 g mod Z.of_nat def.n - m mod Z.of_nat def.n))) in Hs.
    omega.
    split; try omega.
    omega.
  + rewrite Z.mod_small with (a := (create_conf1 g mod Z.of_nat def.n - m mod Z.of_nat def.n)) in Hs.
    omega.
    split.
    rewrite <- Z.lt_0_sub in Hcompare_conf1_m.
    omega.
    assert (Hconf := Zdiv.Z_mod_lt (create_conf1 g) (Z.of_nat def.n)).
    assert (Hm' := Zdiv.Z_mod_lt m (Z.of_nat def.n)).
    omega.
  + unfold def.n; omega.
  + unfold def.n; lia.   
Qed.  


(* the spectre of any configuration during the computation [round] of the new 
   positions of its robots is equal the the spectre of the initial configuration 
   during the same computation [round] *)
Lemma config1_Spectre_Equiv : forall conf g0,
    equiv_conf config1 conf->
    Spect.eq (!! (Config.map (apply_sim
                                (trans (Config.loc (conf (Good g0)))))
                             conf))
             (!! (Config.map (apply_sim
                                (trans (Config.loc (config1 (Good g0)))))
                             config1)).
Proof.
  intros conf g0 Hconf_equiv x.
  unfold Spect.from_config in *.
  (* unfold Spect.multiset. *)
  simpl in *.
  unfold Config.map in *.
  repeat rewrite Spect.multiset_spec in *.
  unfold apply_sim, trans; simpl.
  unfold equiv_conf, f_conf in *.
  destruct Hconf_equiv.
  destruct (H (Good g0)) as (Hl, Hri).
  simpl in *.
  assert (SetoidList.NoDupA Loc.eq
                            (map (fun x : Names.ident =>
                           Config.loc (apply_sim (trans (Config.loc (conf (Good g0))))
                                                          (conf x)))
                                 Names.names)).
  {
    apply (map_injective_NoDupA eq_equivalence Loc.eq_equiv).
    + intros a b Hab.
      rewrite Hab.
      reflexivity.
    + intros id1 id2 Hloc.
      destruct id1 as [g1|b1], id2 as [g2|b2]; try ImpByz b1; try ImpByz b2.
      unfold apply_sim,trans in *; simpl in *.
      rewrite (H (Good g0)), (H (Good g1)), (H (Good g2)) in Hloc.
      simpl in Hloc.
      destruct (Names.eq_dec (Good g1) (Good g2)).
      assumption.
      generalize unique_g_2.
      intros Hu.
      exfalso.
      apply (Hu g0 g1 g2).
      intros Hn; rewrite Hn in n0.
      apply n0.
      reflexivity.
      apply Loc.add_reg_l with (w := x0).
      do 2 rewrite Loc.add_assoc.
      rewrite Loc.add_comm.
      rewrite Loc.add_comm with (v := (Loc.opp (create_conf1 g2))).
      apply Loc.add_reg_l with (w := Loc.opp x0).
      do 2 rewrite Loc.add_assoc with (u := Loc.opp x0).
      do 2 rewrite <- Loc.opp_distr_add.
      do 2 rewrite Loc.add_comm with (v := Loc.add x0 (create_conf1 g0)).
      apply Hloc.
    + assert (Hnames := Names.names_NoDup).
      apply NoDupA_Leibniz in Hnames.
      assumption.
  }
  assert (forall elt, Spect.In elt (!! (Config.map (apply_sim
                                (trans (Config.loc (conf (Good g0)))))
                                                   conf)) ->
                      countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
        (Config.list
           (fun id : Names.ident =>
            apply_sim (trans (Config.loc (conf (Good g0)))) (conf id)))) = 1%nat).
  {
    intros elt Hspe.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
        (Config.list
           (fun id : Names.ident =>
              apply_sim (trans (Config.loc (conf (Good g0)))) (conf id)))) > 1)%nat
                                              -> False).
    {
      intros Hgt.
      rewrite Config.list_spec, map_map in *.
     
      rewrite (NoDupA_countA_occ' Loc.eq_dec) in H0.
      rewrite <- Spect.support_In in Hspe.
      unfold Spect.from_config in Hspe.
      unfold Config.map in Hspe.
      rewrite Config.list_spec in Hspe.
      rewrite map_map in Hspe.
      rewrite Spect.multiset_support in Hspe.
      specialize (H0 elt Hspe).
      rewrite H0 in Hgt.
      omega.
      apply Loc.eq_equiv.
    }
    rewrite <- Spect.support_In in Hspe.
    unfold Spect.from_config in Hspe.
    rewrite Spect.multiset_support in Hspe.
    unfold Config.map in Hspe.
    rewrite <- (countA_occ_pos Loc.eq_equiv Loc.eq_dec) in Hspe.
    destruct ( (countA_occ Loc.eq Loc.eq_dec elt
          (map Config.loc
             (Config.list
                (fun id : Names.ident =>
                   apply_sim (trans (Config.loc (conf (Good g0)))) (conf id))))
          ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
           (map Config.loc
              (Config.list
                 (fun id : Names.ident =>
                  apply_sim (trans (Config.loc (conf (Good g0)))) (conf id)))) <= 0)%nat by omega.
      apply le_not_gt in H2.
      contradiction.
    - exfalso; apply H1; apply Heq.
  }
  assert (forall elt,
             Spect.In elt (!! (Config.map (apply_sim (trans (Config.loc (conf (Good g0))))) conf)) <-> Spect.In elt (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g0))))) config1))).
  {  unfold apply_sim, trans; simpl in *.
     intros elt.
     do 2 rewrite Spect.from_config_In.
     split.
     + intros (gc1,Hc1).
       destruct gc1 as [g1| b] eqn : Hg.
     - generalize (conf1_1 g1 g0); intros Hc11.
       destruct Hc11.
       exists (Good g1).
       simpl in *.
       rewrite <- Hc1.
       rewrite Hl, (H (Good g1)).
       simpl.
       rewrite <- Loc.add_assoc.
       rewrite Loc.add_comm with (v := Loc.opp (Loc.add x0 (create_conf1 g1))).
       rewrite Loc.opp_distr_add.
       do 2 rewrite Loc.add_assoc.
       rewrite Loc.add_opp.
       rewrite Loc.add_comm with (u := Loc.origin).
       now rewrite Loc.add_origin, Loc.add_comm.
     - ImpByz b.
   + intros (gc1,Hc1).
     destruct gc1 as [g1| b] eqn : Hg.
     - generalize (conf1_1 g1 g0); intros Hc11.
       destruct Hc11.
       exists (Good g1).
       simpl in *.
       rewrite <- Hc1.
       rewrite Hl, (H (Good g1)).
       simpl.
       rewrite <- Loc.add_assoc.
       rewrite Loc.add_comm with (v := Loc.opp (Loc.add x0 (create_conf1 g1))).
       rewrite Loc.opp_distr_add.
       do 2 rewrite Loc.add_assoc.
       rewrite Loc.add_opp.
       rewrite Loc.add_comm with (u := Loc.origin).
       now rewrite Loc.add_origin, Loc.add_comm.
     - ImpByz b.
  }
  assert (Ht_map : forall x : Spect.elt, 
             Spect.In x (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g0))))) config1))
       <-> (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g0))))) config1))[x] = 1%nat).
  { intros elt; split.
    intros Hsp_In.
    assert (Hsp_In' := Hsp_In).
    (* rewrite HSfcI in Hsp. *)
    (* destruct Hsp. *)
    unfold Spect.from_config.
    (* unfold Spect.multiset. *)
    generalize unique_g_2.
    intros.
    simpl in *.
    rewrite Spect.multiset_spec. 
    rewrite Config.list_spec.
    rewrite map_map.
    assert (HNoDup_map : SetoidList.NoDupA Loc.eq (map (fun x0 : Names.ident => Config.loc (Config.map (apply_sim (trans (create_conf1 g0))) config1 x0)) Names.names)).
    { apply (map_injective_NoDupA) with (eqA := Logic.eq).
      + intuition.
      + apply Loc.eq_equiv.
      + intros a b Hab.
        rewrite Hab.
        reflexivity.
      + intros id1 id2 Heq.
        destruct (Names.eq_dec id1 id2).
        assumption.
        exfalso.
        destruct id1 eqn : Hid1,
                         id2 eqn : Hid2.
        assert (H_aux2 := conf1_1 g2 g0);
          assert (H_aux1 := conf1_1 g1 g0).
        destruct H_aux1, H_aux2.
        apply (H3 g0 g1 g2).
        intuition.
        rewrite H6 in n0.
        auto.
        simpl in *.
        rewrite Heq.
        reflexivity.
        ImpByz b.
        ImpByz b. 
        ImpByz b. 
      + assert (Hnames := Names.names_NoDup).
        apply NoDupA_Leibniz in Hnames.
        assumption.
    }
    apply NoDupA_countA_occ'.
    apply Loc.eq_equiv.
    apply HNoDup_map.
    unfold Spect.from_config in Hsp_In.
    unfold Config.map in Hsp_In.
    rewrite Config.list_spec in Hsp_In.
    rewrite map_map in Hsp_In.
    rewrite <- Spect.support_In in Hsp_In.
    rewrite Spect.multiset_support in Hsp_In.
    assumption.
    intros.
    unfold Spect.from_config in *.
    unfold Spect.In.
    omega.
  }
  specialize (Ht_map x).
  destruct (Spect.In_dec x (!! (Config.map (apply_sim
                                (trans (Config.loc (conf (Good g0)))))
                             conf))).
  + assert (i' : Spect.In x (!!
                             (Config.map (apply_sim (trans (Config.loc (config1 (Good g0))))) config1))) by now rewrite <- H2.
    unfold Spect.from_config, Config.map in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    destruct Ht_map as (Ht1, Ht2).
    rewrite H1, Ht1.
    reflexivity.
    apply i'.
    apply i.
  + assert (n0' : ~ Spect.In x (!!
                                  (Config.map (apply_sim (trans (Config.loc (config1 (Good g0))))) config1))) by now rewrite <- H2.
    rewrite Spect.not_In in n0.
    rewrite Spect.not_In in n0'.
    unfold Spect.from_config, Config.map in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.
Qed.


(* any configuration equivalent to the starting one will not stop if executed with 
   [r] and [bad_demon1] *)
Lemma moving_never_stop : forall conf,
    equiv_conf config1 conf ->
    ~Stopped (execute r bad_demon1 conf).
Proof.
  intros conf Hconf_equiv Hstop.
  destruct Hstop as (Hstop, _).
  unfold stop_now in *.
  simpl in *.
  unfold Config.eq, round in Hstop.
  simpl in Hstop.
  specialize (Hstop (Good g)).
  simpl in Hstop.
  destruct Hstop as (Hstop,_).
  simpl in Hstop.
  rewrite (config1_Spectre_Equiv) in Hstop.
  unfold config1 in Hstop; simpl in Hstop.
  rewrite <- spect_rotation in Hstop.
  unfold move in Hmove.
  rewrite Hmove in Hstop.
  set (X := Config.loc (conf (Good g))) in *.
  unfold Loc.add, Loc.opp, Loc.eq in *.
  rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same, Z.mod_mod, 
  Zdiv.Zplus_mod_idemp_r in Hstop;
    try (unfold def.n; generalize n_sup_1; omega).
  simpl in Hstop.
  replace (X + -m) with (X - m) in * by omega.
  assert (0 < (m mod Z.of_nat def.n) < Z.of_nat def.n).
  split.
  assert (Z.of_nat def.n > 0) by (generalize n_sup_1; unfold def.n ; omega).
  generalize (Zdiv.Z_mod_lt m (Z.of_nat def.n) H).
  unfold def.n.
  omega.
  apply Zdiv.Z_mod_lt.
  generalize n_sup_1; unfold def.n; omega.
  rewrite Zdiv.Zminus_mod in Hstop.
  destruct (X mod Z.of_nat def.n ?= (m mod Z.of_nat def.n)) eqn : Hcompare_X_m;
    try rewrite Z.compare_eq_iff in *;
    try rewrite Z.compare_gt_iff in *;
    try rewrite Z.compare_lt_iff in *.
  + rewrite Hcompare_X_m, Z.sub_diag, Zdiv.Zmod_0_l in Hstop.
    omega.
  + rewrite <- Z.lt_sub_0 in Hcompare_X_m.
    rewrite Z.add_lt_mono_l with (p := Z.of_nat def.n) in Hcompare_X_m.
    simpl in *.
    replace (X mod Z.of_nat def.n - m mod Z.of_nat def.n) with
    (0 + (X mod Z.of_nat def.n - m mod Z.of_nat def.n)) in Hstop by omega.
    rewrite <- Z.mod_same with (a := Z.of_nat def.n) in Hstop.
    assert (- Z.of_nat def.n < X mod Z.of_nat def.n - m mod Z.of_nat def.n).
    assert (0 <= X mod Z.of_nat def.n).
    apply Zdiv.Z_mod_lt.
    unfold def.n; generalize n_sup_1; omega.
    omega.
    rewrite Zdiv.Zplus_mod_idemp_l in Hstop.
    rewrite Z.mod_small with (a :=  (Z.of_nat def.n + (X mod Z.of_nat def.n - m mod Z.of_nat def.n))) in Hstop.
    omega.
    split; try omega.
    omega.
  + rewrite Z.mod_small with (a := (X mod Z.of_nat def.n - m mod Z.of_nat def.n)) in Hstop.
    omega.
    split.
    rewrite <- Z.lt_0_sub in Hcompare_X_m.
    omega.
    assert (Hconf := Zdiv.Z_mod_lt (X) (Z.of_nat def.n)).
    assert (Hm' := Zdiv.Z_mod_lt m (Z.of_nat def.n)).
    omega. 
  + assumption.
Qed.


 (* A configuration where the robots are moved of [k] nodes compared to the 
    starting configuration is moved of [((k-1) mod n) mod n] nodes after a round. *)
Lemma rec_conf_equiv : forall conf k, Config.eq conf (f_conf config1 k)
                                      -> Config.eq (round r da1 conf) (f_conf config1 (Loc.add k (Loc.opp m))).
Proof.
  intros conf k Heq [g|b]; try ImpByz b.
  split.
  + assert (Hequiv : equiv_conf config1 conf) by (now exists k).
    unfold f_conf in *.
    simpl in *.
    specialize (Heq (Good g)).
    destruct Heq as (Heq, _).
    simpl in *.
    rewrite config1_Spectre_Equiv .
    unfold config1 at 1.
    simpl.
    rewrite <- spect_rotation; try assumption.
    unfold move in *.
    rewrite Hmove.
    rewrite Heq.
    rewrite Loc.add_comm, Loc.add_assoc.
    rewrite Loc.add_comm with (v := k).
    reflexivity.
    assumption.
  + unfold round; simpl.
    destruct (Heq (Good g)) as (_,Hif).
    rewrite Hif.
    unfold f_conf.
    simpl.
    reflexivity.
Qed.

CoInductive AlwaysEquiv (e : execution) : Prop :=
  CAE : equiv_conf config1 (execution_head e) ->
        AlwaysEquiv (execution_tail e) -> AlwaysEquiv e.

CoInductive AlwaysMoving (e : execution) : Prop :=
  CAM : (~ Stopped e) -> AlwaysMoving (execution_tail e) -> AlwaysMoving e.

(* An execution that is satisfing the predicate [AlwaysEquiv]
   satisfy the [AlwaysMoving] one too. *)

Lemma AlwaysEquiv_impl_AlwaysMoving : forall e,
    e = execute r bad_demon1 (execution_head e)
    -> AlwaysEquiv e -> AlwaysMoving e.
Proof.
  cofix.
  intros e Heq_e HAequiv.
  constructor.
  - destruct HAequiv.
    unfold equiv_conf in H.
    destruct H.
    assert (Hcomp := execute_compat (reflexivity r) (reflexivity bad_demon1) H). 
    rewrite Heq_e.
    rewrite Hcomp.
    apply moving_never_stop.
    exists x.
    reflexivity.
  -  destruct HAequiv.
     apply AlwaysEquiv_impl_AlwaysMoving.
     + rewrite Heq_e at 1.
       rewrite execute_tail.
       simpl in *.
       rewrite Heq_e at 2.
       simpl in *.
       reflexivity.
     + assumption.
Qed.



(*  if a configuration is equivalent to the starting one, it respect the predicate 
    [AlwaysEquiv] *)

Lemma AlwaysEquiv_conf1 : forall conf, equiv_conf config1 conf
                                       -> AlwaysEquiv (execute r bad_demon1 conf).
Proof.
  cofix.
  intros.
  constructor.
  + now simpl in *.
  + apply AlwaysEquiv_conf1.
    simpl in *.
    unfold equiv_conf.
    destruct H.
    exists (Loc.add x (Loc.opp m)).
    now apply rec_conf_equiv.
Qed.

(* the starting configuration respect the [AlwaysMoving] predicate *)

Lemma config1_AlwaysMoving : AlwaysMoving (execute r bad_demon1 config1).
Proof.
  apply AlwaysEquiv_impl_AlwaysMoving.
  now simpl.
  apply AlwaysEquiv_conf1.
  exists 0.
  unfold f_conf.
  intros [g|b]; try ImpByz b.
  fold Loc.origin.
  rewrite Loc.add_comm, Loc.add_origin.
  try repeat split; now simpl in *.
Qed.

(* If an execution use [r] as its robogram, and [bad_demon1] as its demon, *
   and if the execution respect the [AlwaysMoving] predicate, it can't respect 
   the [Will_Stop] one *)

Lemma AlwaysMoving_impl_not_WillStop : forall e,
    e = execute r bad_demon1 (execution_head e)
    -> AlwaysMoving e -> ~ Will_stop e.
Proof.
intros e Heq_e Hmo Hst.
destruct Hmo.
induction Hst.
contradiction.
apply IHHst.
rewrite Heq_e.
cbn.
reflexivity.
now destruct Hmo.
now destruct Hmo.
Qed.



(* The starting configuration will not stop *)
Lemma never_stop : ~ Will_stop (execute r bad_demon1 config1).
Proof.
  apply AlwaysMoving_impl_not_WillStop.
  cbn.
  reflexivity.
  apply config1_AlwaysMoving.
Qed.

  (* final theorem first part: if we move, In the asynchronous model, and if k 
     divide n, then the exploration with stop of a n-node ring is not possible. *)

Theorem no_exploration_moving : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
Proof.
intros Hmod Habs.
specialize (Habs bad_demon1).
unfold FullSolExplorationStop in *.
destruct (Habs config1) as (_, Hstop).
now apply never_stop.
Save.

End Move1.

Section Stop.

  Hypothesis Hm : m mod Z.of_nat n = 0.

  
  Lemma config1_eq_round_config1 :
    Config.eq config1 (round r da1 config1).
    Proof.
      intros [g|b]; try ImpByz b.
      unfold round.
      split; simpl; try reflexivity.
      rewrite <- spect_rotation.
      unfold move in Hmove.
      rewrite Hmove.
      unfold Loc.opp.
      rewrite Zdiv.Zminus_mod, Z.mod_same.
      unfold def.n.
      rewrite Hm.
      simpl.
      rewrite Z.mod_0_l.
      fold Loc.origin.
      now rewrite Loc.add_origin.
      generalize n_sup_1; omega.
      generalize n_sup_1; unfold def.n; omega.
    Qed.

   Lemma NeverVisited_conf1 : forall e,
       eeq e (execute r bad_demon1 config1) ->
       exists l, ~ Will_be_visited l e.
  Proof.
    intros e Heq_e.
    exists Loc.unit.
    intros Hl.
    induction Hl.
    + destruct H as ((g0, Hvis), Hvis_later).
      rewrite Heq_e in Hvis.
      simpl in Hvis.
      assert (Z.of_nat (n mod kG) = 0) by (generalize kdn; omega).
      now apply (config1_ne_unit H g0).
    + apply IHHl.
      rewrite Heq_e.
      cbn.
      symmetry.
      apply (execute_compat (reflexivity r) (reflexivity bad_demon1)
                            config1_eq_round_config1).
  Qed.


  Lemma never_visited :
      ~ (forall l : Loc.t, Will_be_visited l (execute r bad_demon1 config1)).
  Proof.
    intros Hw.
    generalize (NeverVisited_conf1 (reflexivity (execute r bad_demon1 config1))).
    intros Hfalse.
    destruct Hfalse as (g0, Hfalse).
    specialize (Hw g0).
    contradiction.
Qed.
    
  Theorem no_exploration_idle : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    destruct (Habs config1) as (Hexpl, _).
    now apply never_visited.
  Save.

End Stop.

Theorem no_exploration : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
Proof.
  generalize no_exploration_idle, no_exploration_moving.
  intros.
  destruct (Loc.eq_dec m 0); unfold Loc.eq, def.n in *;
  rewrite Z.mod_0_l in *.
  apply H; try assumption.
  generalize n_sup_1; omega.
  apply H0; try assumption.
  generalize n_sup_1; omega.
Save.

End Exploration.