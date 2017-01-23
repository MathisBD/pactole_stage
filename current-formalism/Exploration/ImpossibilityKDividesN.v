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
(* Require Import Morphisms. *)
Require Import Arith.Div2.
Require Import Omega.
(* Require Import List SetoidList. *)
Require Import List Setoid Compare_dec Morphisms FinFun.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.Definitions.
Require Import Pactole.Exploration.test_modulo.

Set Implicit Arguments.
(* taille de l'anneau*)
Parameter n : nat.
Axiom n_sup_1 : 1 < n.

Parameter kG : nat.
Axiom kdn : n mod kG = 0.
Axiom k_inf_n : kG < n.
Axiom k_sup_1 : 1 < kG.


Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.
Module def : RingDef with Definition n := Top.n.
 Definition n:= Top.n.
 Lemma n_pos : n <> 0. Proof. unfold n. generalize Top.n_sup_1. omega. Qed.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
End def.


(** The setting is a ring. *)
Module Loc := Ring(def).
Print Loc.dist.

(** There are KG good robots and no byzantine ones. *)


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(Loc)(K).
Export DefsE.

Coercion Sim.sim_f : Sim.t >-> DiscreteSimilarity.bijection.
Coercion DiscreteSimilarity.section : DiscreteSimilarity.bijection >-> Funclass.

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
  unfold Loc.unit, Loc.mul, def.n.
  rewrite Z.mul_1_r.
  generalize kdn, k_inf_n; intros Hdkn Hk_inf_n.
  rewrite Z.mod_eq with (b := Z.of_nat n); try omega.
  rewrite Zdiv.Zminus_mod, Nat2Z.inj_mul, Z.mod_mul; try omega.
  assert (Hn0 : kG <> 0%nat) by (generalize k_sup_1; omega).
  assert (Hneq := Nat.div_mod n kG Hn0).
  rewrite Hdkn, <-plus_n_O in Hneq.
  rewrite Hneq at 1; rewrite Nat2Z.inj_mul.
  rewrite Z.mul_comm.
  rewrite Z.mul_mod.
  rewrite Zdiv.Z_mod_mult.
  rewrite Zmult_0_r.
  rewrite Zdiv.Zmod_0_l.
  reflexivity.
  assert (H0n : (0 < n/ kG)%nat).
  apply Nat.div_str_pos.
  omega.
  omega.
  assert (H0n : (0 < n/ kG)%nat).
  apply Nat.div_str_pos.
  generalize k_sup_1.
  omega.
  omega.
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
  generalize kdn.
  intros Hkdn.
  unfold Names.G, Names.Gnames, Names.Internals.Gnames, Names.Internals.G, K.nG in *.
  destruct kG eqn : Hkg.
  + generalize k_sup_1; intros; omega. 
  + unfold create_conf1.
    unfold Loc.eq, Loc.mul, Loc.unit, def.n.
    assert (Hkn : forall x, x mod Z.of_nat n = 0
                              -> x mod Z.of_nat (n / S n0) = 0).
    { intros.
      rewrite Nat.mod_divides in Hkdn; try omega.
      destruct Hkdn.
      rewrite Nat.mul_comm in H0.
      rewrite H0 in *.
      rewrite Nat.div_mul in *.
      destruct x0.
      now rewrite Zdiv.Zmod_0_r.
      rewrite Nat2Z.inj_mul, Z.rem_mul_r in H.
      generalize Z_of_nat_complete; intros Haux.
      assert (Ha1 := Haux (x mod Z.of_nat (S x0))).
      assert (Ha2 := Haux ((x / Z.of_nat (S x0)) mod Z.of_nat (S n0))).
      destruct Ha1.
      { now apply Zdiv.Z_mod_lt. }
      destruct Ha2.
      { now apply Zdiv.Z_mod_lt. }
      rewrite H1, H2 in H.
      assert (forall x y, 0 <= x -> 0 <= y -> x + y = 0 -> x = 0 /\ y = 0).
      { intros r s Hr Hs Hrs.
        omega. }
      apply H3 in H.
      destruct H; rewrite H1 in *; assumption.
      omega.
      rewrite <- Nat2Z.inj_mul.
      omega.
      assert ( (0 < S x0)%nat ) by omega.
      assert ( 0<Z.of_nat (S x0)).
      rewrite <- Nat2Z.inj_0.
      now apply inj_lt.
      omega.
      assert ( (0 < S n0)%nat ) by omega.
      assert ( 0<Z.of_nat (S n0)).
      rewrite <- Nat2Z.inj_0.
      now apply inj_lt.
      assert ( (0 < S n0)%nat ) by omega.
      assert ( 0<Z.of_nat (S n0)).
      rewrite <- Nat2Z.inj_0.
      now apply inj_lt.
      omega.
      omega.
      omega.
      omega. }
    assert (Hmod1 :  Z.of_nat (n / kG) <> 0).
      generalize k_inf_n, k_sup_1; intros.
      rewrite Nat.mod_divides, <-Hkg in Hkdn.
      destruct Hkdn.      
      rewrite H1, Nat.mul_comm.
      rewrite Nat.div_mul.
      destruct x.
      omega.
      rewrite <- Nat2Z.inj_0.
      intuition.
      apply Nat2Z.inj in H2.
      omega.
      omega.
      omega.
    assert (Haux' : exists x:nat, (x < kG)%nat /\ 
               ((Z.of_nat x) * Z.of_nat (n/kG)) mod Z.of_nat n = loc mod Z.of_nat n).
    { exists (Z.to_nat (((loc mod Z.of_nat n)/Z.of_nat (n/kG)))). 
      rewrite Z2Nat.id.
      set (n' := Z.of_nat n) in *.
      (* rewrite Zdiv.Zmult_mod_idemp_l.  *)
      rewrite <- Hkg, <- Z.div_exact in Hmod.
      split.
      + assert (Hlocm : exists loc' : nat, loc mod n' = Z.of_nat loc'). 
        apply Z_of_nat_complete.
        apply Zdiv.Z_mod_lt.
        generalize n_sup_1; intros.
        apply inj_lt in H.
        fold n' in H.
        omega.
        destruct Hlocm as (loc', Hlocm).
        rewrite Hlocm.
        rewrite <- Zdiv.div_Zdiv, Nat2Z.id.
        assert (loc' < n)%nat.
        apply Nat2Z.inj_lt.
        rewrite <- Hlocm.
        unfold n'.
        apply Zdiv.Z_mod_lt.
        generalize n_sup_1; omega.
        (* replace n with (kG * (n/kG))%nat in H. *)
        apply Nat.div_lt_upper_bound with (b := (n/kG)%nat) (q := kG).
        omega.
        rewrite Nat.mul_comm.
        rewrite <- Nat.div_exact in Hkdn.
        rewrite Hkg, <- Hkdn.
        assumption.
        omega.
        omega.
      + assert (forall a, a mod Z.of_nat (n/kG) = 0 -> (a mod n') mod Z.of_nat (n/kG) = 0).
        intros.
        rewrite <- Nat.div_exact, <- Hkg in Hkdn.
        unfold n'.
        rewrite Hkdn at 1.
        rewrite Nat.mul_comm, Nat2Z.inj_mul, Z.rem_mul_r.
        rewrite <- Zdiv.Zplus_mod_idemp_r.
        rewrite Z.mul_comm, Zdiv.Z_mod_mult.
        rewrite H.
        simpl in *.
        apply Z.mod_0_l.
        omega.
        omega.
        omega.
        omega.
        rewrite Z.div_exact in Hmod.
        specialize (H loc Hmod).
        rewrite <- Z.div_exact in H.
        rewrite Z.mul_comm, <- H.
        apply Z.mod_mod.
        generalize n_sup_1; intros.
        unfold n'.
        omega.
        omega.
        omega.
      + omega.
      + apply Zdiv.Z_div_pos.
        omega.
        apply Zdiv.Z_mod_lt.
        generalize n_sup_1; intros; omega.
    }
    destruct Haux' as (fg', (Haux, Haux')).
    generalize (conf_aux); intros Ha.
    specialize (Ha fg' kG k_sup_1 Haux).
    destruct Ha.
    rewrite <- Hkg in *.
    exists x; rewrite H.
    rewrite <- Nat2Z.inj_mul in Haux'.
    rewrite Z.mul_1_r, Z.mod_mod.
    apply Haux'.
    generalize n_sup_1; omega.
Qed.



Lemma conf1_inf_n : forall g:Names.G,
    (Z.of_nat ((proj1_sig (Fin.to_nat g)) * (n / kG)) * 1) < Z.of_nat n.
Proof.
  intros.
  unfold Names.G, Names.Internals.G in *.
  assert (Hf := Fin.to_nat g).
  destruct Hf.
  generalize kdn; intros  Hkdn.
  rewrite <- Nat.div_exact in Hkdn.
  unfold K.nG in *.
  rewrite Hkdn at 2.
  generalize ((Fin.to_nat g)).
  intros.
  destruct s.
  simpl.
  rewrite Z.mul_1_r.
  rewrite <- Nat2Z.inj_lt.
  apply mult_lt_compat_r.
  assumption.
  generalize k_sup_1, k_inf_n; intros.
  apply Nat.div_str_pos.
  omega.
  generalize k_sup_1; omega.
Qed.


(* an Injection theorem about config1 *)
Lemma unique_g : forall g1 g2,
               g1 <> g2 -> Loc.eq (Config.loc (config1 (Good g1)))
                                  (Config.loc (config1 (Good g2))) -> False.
Proof.
  intros.
  generalize k_sup_1, k_inf_n.
  intros Hks1 Hkin.
  unfold config1, Loc.eq in H0.
  simpl in *.
  unfold create_conf1 in H0.
  unfold Loc.mul, Loc.unit, def.n in H0.
  generalize (Fin.to_nat_inj g1 g2).
  intros Heq.
  apply H.
  apply Heq.
  assert (Hsol1 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g2) * (n / kG)) * 1 < Z.of_nat n).
  { generalize (Fin.to_nat g2).
    intros.
    unfold K.nG in *.
    destruct s.
    simpl.
    generalize kdn.
    intros.
    rewrite <- Nat.div_exact in H1.
    split.
    omega.
    rewrite H1 at 2.
    rewrite Z.mul_1_r.
    apply inj_lt.
    apply mult_lt_compat_r.
    assumption.
    apply Nat.div_str_pos_iff;
      omega.
    omega.
  }
   assert (Hsol2 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g1) * (n / kG)) * 1 < Z.of_nat n).
  { generalize (Fin.to_nat g1).
    intros.
    unfold K.nG in *.
    destruct s.
    simpl.
    generalize kdn.
    intros.
    rewrite <- Nat.div_exact in H1.
    split.
    omega.
    rewrite H1 at 2.
    rewrite Z.mul_1_r.
    apply inj_lt.
    apply mult_lt_compat_r.
    assumption.
    apply Nat.div_str_pos_iff;
      omega.
    omega.
  }
  do 4 rewrite Z.mod_small in H0;
    try do 2 rewrite Z.mul_1_r in H0;
    try (apply Hsol1);
    try (apply Hsol2);
    try (apply Zdiv.Z_mod_lt;
    omega).
  apply Nat2Z.inj in H0.
  rewrite Nat.mul_cancel_r in H0.
  assumption.
  assert ((0 < (n/kG))%nat).
  apply Nat.div_str_pos.
  omega.
  omega.
Qed.


(* The same that [NoDup_count_occ'] but with the abstraction. *)
Lemma NoDupA_countA_occ' :
              forall (A : Type) (eqA : A -> A -> Prop)
                     (decA : forall x y : A, {eqA x y} + {~eqA x y})
                     (l : list A), Equivalence eqA -> 
                SetoidList.NoDupA eqA l <->
                (forall x : A, SetoidList.InA eqA x l ->
                               countA_occ eqA decA x l = 1%nat).
Proof.
  intros A eqA decA l HeqA.
  split.
  + intros HndA x HinA.
    induction l.
  - now rewrite SetoidList.InA_nil in HinA.
  - assert (HndA' := SetoidList.NoDupA_cons).
    simpl in *.
    destruct (decA a x).
    * assert ((a :: l) = (List.cons a nil) ++ l).
      simpl in *.
      reflexivity.
      rewrite H in *.
      rewrite NoDupA_app_iff in *; try assumption.
      simpl in *.
      destruct HndA as (Hnda, (Hndl, HIn_f)).
      specialize (HIn_f a).
      assert (~ SetoidList.InA eqA a l) by intuition.
      rewrite e in H0.
      rewrite <- (countA_occ_pos HeqA decA) in H0.
      omega.
    * apply IHl.
      ++ assert (Hadd_nil : (a :: l) = (List.cons a nil) ++ l) by now simpl. 
         rewrite Hadd_nil in *.
         rewrite NoDupA_app_iff in *; try assumption.
         destruct HndA as (Hnda, (Hndl, HIn_f)); try assumption.
      ++ assert (Hadd_nil : (a :: l) = (List.cons a nil) ++ l) by now simpl.
         rewrite Hadd_nil in *.
         rewrite SetoidList.InA_app_iff in *.
         destruct HinA; try assumption.
         rewrite SetoidList.InA_singleton in *.
         now destruct n0.
  + intros HinA.
    induction l; try intuition.
    simpl in *.
    induction l as [|b l0].
    - apply SetoidList.NoDupA_singleton.
    - destruct (decA a b) eqn : Hdec.
      * specialize (HinA a).
        assert (SetoidList.InA eqA a (a :: b :: l0)) by
            now apply SetoidList.InA_cons_hd.
        specialize (HinA H).
        destruct (decA a a); try assumption.
        assert ((countA_occ eqA decA a (b :: l0) > 0)%nat).
        rewrite countA_occ_pos; try assumption.
        rewrite e; intuition.
        apply lt_n_S in H0.
        omega.
        exfalso.
        apply f.
        reflexivity.
      * apply SetoidList.NoDupA_cons.
        ++ intros Hf.
           assert (SetoidList.InA eqA a (a :: b :: l0)) by intuition.
           specialize (HinA a H).
           destruct (decA a a); try intuition.
           rewrite <- countA_occ_pos in Hf.
           assert (countA_occ eqA decA a (b :: l0) = 0)%nat by omega.
           rewrite H0 in Hf.
           omega.
           assumption.
        ++ apply IHl.
           intros c Hc.
           assert (HinA_aux := HinA a).
           specialize (HinA c).
           simpl in *.
           destruct (decA b c).
           assert (SetoidList.InA eqA c (a :: b :: l0)) by intuition.
           specialize (HinA H).
           destruct (decA a c).
           rewrite <- e in e0.
           contradiction.
           assumption.
           destruct (decA a c).
           assert (SetoidList.InA eqA c (a :: b :: l0)) by intuition.
           specialize (HinA H).
           assert (SetoidList.InA eqA a (a :: b :: l0)) by intuition.
           specialize (HinA_aux H0).
           destruct (decA a a); try (now destruct f1).
           destruct (decA b a); try discriminate.
           assert ((countA_occ eqA decA a l0 = 0)%nat) by omega.
           assert ((countA_occ eqA decA c (b :: l0) > 0)%nat).
           rewrite countA_occ_pos.
           assumption.
           assumption.
           simpl in *.
           destruct (decA b c); simpl in *.
           contradiction.
           omega.
           rewrite SetoidList.InA_cons in Hc.
           destruct Hc.
           destruct f0.
           rewrite H.
           reflexivity.
           apply HinA.
           intuition.
Qed.      

Parameter g : Names.G.


Variable r : robogram.
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
  intros.
  generalize conf1_new_1, k_sup_1, k_inf_n; intros Hc1n Hks1 Hkin.
  unfold Loc.eq.
  assert (Hc_idg := Hc1n idg).
  assert (Hc_g := Hc1n g0).
  assert (Hnkg0 : Z.of_nat (n / kG) <> 0).
  assert (H0n : (0 < n/kG)%nat).
  apply Nat.div_str_pos.
  omega.
  omega.
  generalize conf1_new_2; intros Hc1n2.
  unfold Loc.add, Loc.opp, def.n.
  set (n0 := Z.of_nat n).
  specialize (Hc1n2 (create_conf1 g0 - create_conf1 idg)).
  destruct Hc1n2.
  rewrite Zdiv.Zminus_mod.
  rewrite Hc_idg, Hc_g.
  simpl in *.
  apply Z.mod_0_l.
  omega.
  exists x.
  unfold Loc.eq, def.n in H.
  rewrite <- Zdiv.Zminus_mod_idemp_r.
  fold n0 in H.
  rewrite H.
  rewrite <- Zdiv.Zminus_mod_idemp_l with (a := n0).
  rewrite Z.mod_same.
  rewrite Zdiv.Zplus_mod_idemp_r.
  rewrite Z.mod_mod.
  simpl in *.
  rewrite Z.add_opp_r, Zdiv.Zminus_mod_idemp_r.
  rewrite Z.sub_sub_distr.
  rewrite Z.add_comm, Z.sub_diag.
  now rewrite Z.add_0_r.
  unfold n0. omega.
  unfold n0. omega.
Qed.

Lemma mod_min_eq : forall a b c, (a-b)mod Z.of_nat n = (a-c) mod Z.of_nat n ->
                                 - Z.of_nat n < a - c < Z.of_nat n ->
                                 - Z.of_nat n < a - b < Z.of_nat n ->
                                 c mod Z.of_nat n = b mod Z.of_nat n.
Proof.
  intros a b c Heq Hlac Hlab.
  generalize n_sup_1; intros Hns1.
  destruct (a ?= b) eqn : Hab, (a ?= c) eqn : Hac, (b ?= c) eqn : Hbc;
    try rewrite Z.compare_lt_iff in *;
    try rewrite Z.compare_gt_iff in *;
    try rewrite Z.compare_eq_iff in *;
    try (now rewrite Hbc in *);
         try omega.
  + rewrite <- Hab, Z.sub_diag, Zdiv.Zmod_0_l in Heq.
    replace (a - c) with (- (c - a)) in Heq by omega.
    symmetry in Heq.
    apply Zdiv.Z_mod_zero_opp_full in Heq.
    rewrite <- Z.add_0_l with (n := - - (c - a) mod Z.of_nat n) in Heq.
    rewrite Z.mod_small in Heq; try omega.
  + rewrite <- Hab, Z.sub_diag, Zdiv.Zmod_0_l in Heq.
    symmetry in Heq.
    rewrite Z.mod_small in Heq; try omega.
  + rewrite <- Hac, Z.sub_diag, Zdiv.Zmod_0_l in Heq.
    replace (a - b) with (- (b - a)) in Heq by omega.
    apply Zdiv.Z_mod_zero_opp_full in Heq.
    rewrite <- Z.add_0_l with (n := - - (b - a) mod Z.of_nat n) in Heq.
    rewrite Z.mod_small in Heq; try omega.
  + replace (a - b) with (- (b - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    replace (a - c) with (- (c - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    do 2 rewrite Z.mod_small in Heq; try omega.
    rewrite Z.mod_small; try omega.
    rewrite Z.mod_small; try omega.
  + replace (a - b) with (- (b - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    replace (a - c) with (- (c - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    do 2 rewrite Z.mod_small in Heq; try omega.
    rewrite Z.mod_small; try omega.
    rewrite Z.mod_small; try omega.   
  + replace (a - b) with (- (b - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    do 2 rewrite Z.mod_small in Heq; try omega.
    rewrite Z.sub_sub_distr in Heq.
    assert (Ha : c = b - Z.of_nat n) by omega.
    rewrite Ha, <- Zdiv.Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r; try omega.
    rewrite Z.mod_small; try omega.
  + rewrite <- Hac, Z.sub_diag, Zdiv.Zmod_0_l in Heq.
    rewrite Z.mod_small in Heq; try omega.
  + replace (a - c) with (- (c - a)) in * by omega.
    rewrite Zdiv.Z_mod_nz_opp_full in Heq; try omega.
    do 2 rewrite Z.mod_small in Heq; try omega.
    rewrite Z.sub_sub_distr in Heq.
    assert (Ha : b = c - Z.of_nat n) by omega.
    rewrite Ha, <- Zdiv.Zminus_mod_idemp_r, Z.mod_same, Z.sub_0_r; try omega.
    rewrite Z.mod_small; try omega.
  + do 2 rewrite Z.mod_small in Heq; try omega.
  + do 2 rewrite Z.mod_small in Heq; try omega.
Qed.

Lemma unique_g_2 : forall g0 g1 g2 : Names.G,
    g1 <> g2 -> Loc.eq (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g1)))
                       (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g2)))
    -> False.
Proof.
  intros g0 g1 g2 Hg Heq.
  generalize k_sup_1, k_inf_n, conf1_inf_n.
  intros Hks1 Hkin Hcif.
  unfold config1, Loc.eq in Heq.
  generalize unique_g; intros Hunique.
  specialize (Hunique g1 g2 Hg).
  simpl in *.
  unfold Loc.mul, Loc.add, Loc.opp, Loc.unit, def.n in Heq.
  apply Hunique.
  do 2 rewrite Z.mod_mod in Heq; try omega.
  do 2 rewrite Zdiv.Zplus_mod_idemp_r in Heq; try omega.
  do 2 rewrite Z.add_sub_assoc in Heq.
  rewrite Z.add_comm in Heq.
  do 2 rewrite <- Z.add_sub_assoc in Heq.
  do 2 (rewrite <- Zdiv.Zplus_mod_idemp_l, Z.mod_same in Heq; try omega;
        simpl in * ) .
  unfold Loc.eq, def.n.
  apply mod_min_eq with (a := create_conf1 g0).
  symmetry.
  assumption.
  rewrite Zdiv.Zminus_mod in Heq.
  rewrite Zdiv.Zminus_mod with (b := create_conf1 g2) in Heq.
  assert (- Z.of_nat n < create_conf1 g0 mod Z.of_nat n - create_conf1 g1 mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (create_conf1 g0) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (create_conf1 g1) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  assert (- Z.of_nat n < create_conf1 g0 mod Z.of_nat n - create_conf1 g2 mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (create_conf1 g0) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (create_conf1 g2) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
Qed.


(* The spectre of the initial configuration is the same that the one during 
   its computaion [round]. *)

Lemma spect_rotation : forall g0 : Names.G, Spect.eq (!! config1) (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)).
Proof.
(* unfold Spect.multiset. *)
(* unfold Spect.eq. *)
  (* intros X. *)
  intros g0.
  unfold apply_sim, trans; simpl in *.
  generalize Spect.from_config_In, conf1_1, Spect.pos_in_config.
  intros HSfcI Hconf1_1 HSpic.
  assert (Htrue : forall x:Spect.elt, Spect.In x (!!config1)
              <-> Spect.In x (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))).
  { unfold apply_sim, trans; simpl in *.
    intros x. do 2 rewrite HSfcI.
    split.
    + intros (gc1,Hc1).
      destruct gc1 as [g1| b] eqn : Hg.
      - specialize (Hconf1_1 g1 g0).
        destruct Hconf1_1.
        exists (Good x0).
        simpl in *.
        rewrite <- Hc1, H.
        reflexivity.
      - ImpByz b. 
    + intros (gc1,Hc1).
      destruct gc1 as [g1| b] eqn : Hg.
      - simpl in *.
        assert (H':= Hconf1_1 g1 g0).
        destruct H'.
        rewrite H in Hc1.
        unfold Loc.add, Loc.opp, def.n in Hc1.
        set (cc1 := create_conf1 g0) in Hc1.
        set (n0 := Z.of_nat n) in Hc1.
        generalize n_sup_1; intros Hn.
        repeat rewrite Zdiv.Zminus_mod_idemp_r, Zdiv.Zplus_mod_idemp_r in Hc1;
          try omega.
        replace (cc1 + (n0 - (cc1 + (n0 - create_conf1 x0) mod n0)))
        with (n0 - (n0 - create_conf1 x0) mod n0) in Hc1 by omega.
        do 2 rewrite <- Zdiv.Zminus_mod_idemp_l with (a:= n0) in Hc1.
        rewrite Z.mod_same in Hc1.
        rewrite Z.sub_0_l with (n := create_conf1 x0) in Hc1.
        rewrite Zdiv.Zminus_mod_idemp_r in Hc1.
        simpl in *.
        exists (Good x0).
        simpl in *.
        rewrite <- Hc1.
        unfold Loc.eq, def.n.
        rewrite Z.mod_mod; try omega.
        rewrite <- Z.sub_0_l.
        rewrite Z.sub_opp_r.
        now simpl in *.
        unfold n0.
        omega.
      - ImpByz b. 
  }
  unfold Spect.eq.
  assert (Ht : forall x : Spect.elt, 
             Spect.In x (!! config1) <-> (!! config1)[x] = 1%nat).
  { intros x; split.
    intros Hsp_In.
    assert (Hsp_In' := Hsp_In).
    (* rewrite HSfcI in Hsp. *)
    (* destruct Hsp. *)
    unfold Spect.from_config.
    (* unfold Spect.multiset. *)
    generalize unique_g.
    intros.
    rewrite Spect.multiset_spec. 
    rewrite Config.list_spec.
    rewrite map_map.
    assert (HNoDup_map : SetoidList.NoDupA Loc.eq (map (fun x0 : Names.ident => Config.loc (config1 x0)) Names.names)).
    { apply (map_injective_NoDupA) with (eqA := Logic.eq).
      intuition.
      apply Loc.eq_equiv.
      intros a b Hab.
      rewrite Hab.
      reflexivity.
      intros id1 id2 Heq.
      destruct (Names.eq_dec id1 id2).
      assumption.
      exfalso.
      destruct id1 eqn : Hid1,
      id2 eqn : Hid2.
      apply (H g1 g2).
      intuition.
      rewrite H0 in n0.
      auto.
      now rewrite Heq.
      ImpByz b.
      ImpByz b.
      ImpByz b.
      assert (Hnames := Names.names_NoDup).
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
  } assert (Ht_map : forall x : Spect.elt, 
             Spect.In x (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
       <-> (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))[x] = 1%nat).
  { intros x; split.
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
        assert (H_aux2 := Hconf1_1 g2 g0);
          assert (H_aux1 := Hconf1_1 g1 g0).
        destruct H_aux1, H_aux2.
        apply (H g0 g1 g2).
        intuition.
        rewrite H2 in n0.
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
  intros x.
  specialize (Htrue x).
  rewrite Ht, Ht_map in Htrue.
  cut (Config.eq (Config.map
         (fun infoR : Config.RobotConf =>
          {|
          Config.loc := Loc.add (create_conf1 g0) (Loc.opp (Config.loc infoR));
          Config.robot_info := Config.robot_info infoR |}) config1)
                 (Config.map (apply_sim (trans (create_conf1 g0))) config1)).
  intros Heq_conf; rewrite Heq_conf.
  destruct (Spect.In_dec x (!! config1)).
  rewrite (Ht x) in i.
  rewrite i.
  rewrite Htrue in i; now rewrite i.
  assert (n0' : ~ Spect.In x (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))).
  { intros Hn.
    apply n0.
    rewrite <- Ht, <- Ht_map in Htrue.
    now rewrite Htrue.
    }
  unfold Spect.In in n0;
    unfold Spect.In in n0'.
  omega.
  unfold apply_sim, trans;
  simpl in *.
  reflexivity.
Qed.


Lemma da1_compat : Proper (Logic.eq ==> opt_eq (Loc.eq ==> Sim.eq))
  (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => trans c))).
Proof.
intros ? [g | b] ?; subst; simpl.
+ intros c1 c2 Hc. rewrite <- Hc; reflexivity.
+ apply Fin.case0. exact b.
Qed.

Definition da1 : demonic_action.

refine {|
  relocate_byz := fun b => Loc.origin;
  step := (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => trans c))) |}.
Proof.
- exact da1_compat.
- intros id sim c Heq. destruct id; simpl in Heq.
  + inversion Heq. now simpl.
  + apply Fin.case0. exact b .
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

Section Move1.
  
Hypothesis Hm : m mod (Z.of_nat n) <> 0.





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