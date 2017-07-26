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


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid Compare_dec Morphisms FinFun.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
Require Import Pactole.Exploration.Graph.DefinitionsSSync.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.

Set Implicit Arguments.


Module Gra := MakeRing.

Export Gra.
Export MakeRing.

(** Taille de l'anneau*)

Definition n := n.
Parameter kG : nat.
Axiom kdn : (n mod kG)%nat = 0%nat.
Axiom k_inf_n : (kG < n)%nat.
Axiom k_sup_1 : (1 < kG)%nat.


Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

Module def : RingDef with Definition n := n.
 Definition n:= n.
 Lemma n_sup_1 : (n > 1)%nat. Proof. unfold n; apply n_sup_1. Qed.
 Lemma n_pos : (n <> 0)%nat. Proof. generalize n_sup_1. omega. Qed.
End def.

(** The setting is a ring. *)

  (** There are KG good robots and no byzantine ones. *)


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := DefinitionsSSync.ExplorationDefs(K).
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

Section DiscreteExploration.
Open Scope Z_scope.

  
Definition create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (Z2V (((Z_of_nat ((proj1_sig (Fin.to_nat f))*(n / kG)))))) Loc.unit.


(* the starting configuration where a robots is on the origin, 
   and every other robot is at a distance of [x*(kG/n)] where x is between 1 and kG *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc :=  pos;
                             Config.info :=
                               {| Info.source := pos;
                                  Info.target := pos  |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.info := {| Info.source := pos; Info.target := pos |} |}
            end.

Unset Printing Dependent Evars Line.

Lemma conf1_new_aux:
  forall gg: nat,  
    V2Z (Loc.mul (Z2V (((Z_of_nat (gg*(n / kG)))))) Loc.unit) mod Z.of_nat (n/kG) = 0.
Proof.
  intros.
  assert (H0n : (0 < n/ kG)%nat).
  apply Nat.div_str_pos.
  generalize k_sup_1, k_inf_n;
  omega.
  unfold Loc.unit, Loc.mul.
  rewrite <- 3 loc_fin.
  assert (Hns1 := n_sup_1).
  repeat rewrite Z.mod_1_l; try lia.
  fold n in *.
  rewrite Z.mul_1_r.
  repeat rewrite Z.mod_mod; try lia.
  assert (Hkdn := kdn).
  rewrite <- Nat.div_exact in Hkdn.
  rewrite Hkdn at 2.
  rewrite (Nat.mul_comm kG _).
  rewrite 2 Nat2Z.inj_mul.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r, (Zdiv.Zmult_mod (Z.of_nat (n/kG))).
  rewrite <-Zdiv.Zmult_mod_idemp_r, Z.mod_same.
  rewrite Zmult_0_r,Zmult_0_l.
  rewrite Zdiv.Zmod_0_l.
  reflexivity.
  omega.
  omega.
  generalize k_sup_1; lia.
  generalize k_sup_1; lia.
Qed.



(* A position where a robot is in config1 divied [k/n] *)
Lemma conf1_new_1 : forall g0: Names.G, V2Z (create_conf1 g0) mod Z.of_nat (n/kG) = 0.
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
                                exists g:Names.G,
                                  Loc.eq (create_conf1 g) (Z2V loc).
Proof.
  intros loc Hmod.
  intros.
  generalize kdn n_sup_1.
  fold n in *.
  intros Hkdn Hns1.
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
      rewrite Nat.div_mul in *; try lia.
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
      lia.
    }
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
        apply inj_lt in Hns1.
        fold n' in Hns1.
        omega.
        destruct Hlocm as (loc', Hlocm).
        rewrite Hlocm.
        rewrite <- Zdiv.div_Zdiv, Nat2Z.id.
        assert (loc' < n)%nat.
        apply Nat2Z.inj_lt.
        rewrite <- Hlocm.
        unfold n'.
        apply Zdiv.Z_mod_lt.
        lia.
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
    repeat rewrite <- loc_fin.
    repeat rewrite Z.mod_1_l; try (fold n; lia).
    rewrite Z.mul_1_r, Z.mod_mod;
    fold n in *; try lia.
    rewrite Haux'.
    unfold Veq.
    repeat rewrite <- loc_fin.
    fold n.
    rewrite Z.mod_mod; lia.
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
  unfold Veq in H0.
  repeat rewrite <- loc_fin in H0.
  rewrite 2 Z.mod_1_l in H0; try (fold n; lia).
  fold n in *.
  rewrite 2 Z.mul_1_r in H0.
  rewrite 6 Z.mod_mod in H0; try (fold n; lia).
  rewrite Z.mul_1_r in *.
  do 2 rewrite Z.mod_small in H0;
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

Parameter g : Names.G.


Variable r : DGF.robogram.


(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)
(* changer conf1 pour que loc et tgt soient égales *)

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
  specialize (Hc1n2 (V2Z (create_conf1 g0) - V2Z (create_conf1 idg))).
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
  unfold Veq; repeat rewrite <- loc_fin; repeat rewrite Z.mod_mod; try (fold n; lia).
  rewrite Zdiv.Zplus_mod_idemp_r.
  simpl in *.
  rewrite Z.add_opp_r, Zdiv.Zminus_mod_idemp_r.
  rewrite Z.sub_sub_distr.
  rewrite Z.add_comm, Z.sub_diag.
  now rewrite Z.add_0_r.
  unfold n0. fold n; omega.
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
  unfold Veq in *; repeat rewrite <- loc_fin in *.
  do 6 rewrite Z.mod_mod in Heq; try (fold n; omega).
  do 2 rewrite Zdiv.Zplus_mod_idemp_r in Heq; try omega.
  do 2 rewrite Z.add_sub_assoc in Heq.
  rewrite Z.add_comm in Heq.
  do 2 rewrite <- Z.add_sub_assoc in Heq.
  do 2 (rewrite <- Zdiv.Zplus_mod_idemp_l, Z.mod_same in Heq; try omega;
        simpl in * ) .
  unfold Loc.eq, def.n.
  apply mod_min_eq with (a := V2Z (create_conf1 g0)).
  symmetry.
  assumption.
  rewrite Zdiv.Zminus_mod in Heq.
  rewrite Zdiv.Zminus_mod with (b := V2Z (create_conf1 g2)) in Heq.  assert (- Z.of_nat n < (V2Z (create_conf1 g0)) mod Z.of_nat n - V2Z (create_conf1 g1) mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (V2Z (create_conf1 g0)) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (V2Z (create_conf1 g1)) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
    assert (- Z.of_nat n < (V2Z (create_conf1 g0)) mod Z.of_nat n - V2Z (create_conf1 g2) mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (V2Z (create_conf1 g0)) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (V2Z (create_conf1 g2)) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold create_conf1, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  fold n; omega.
  fold n; omega.
  fold n; omega.
Qed.


(* The spectre of the initial configuration is the same that the one during 
   its computaion [round]. *)

Import DGF.
(* probleme, si je veux faire un demon synchrone, j'ai besoin de savoir quand tous
les robots sont arrivé à leur cible, donc j'ai besoin d'information sur la 
configuration.  Si j'ai des info sur la configuration dans l'action démoniaque, 
je dois avoir des information sur l'execution pour le demon.
et l'execution depend du démon. donc double dépendance, donc problème.

possibilité d'avoir une variable globale comptant le nombre de robots arrivé?
et de mettre a jour cette variable dans round via une fonction ? et de regarder
cette variable dans l'action démoniaque au moment de dire si on bouge ou non?

 *)

Definition da1 : demonic_action.
  refine
    {|
      relocate_byz := fun b => Fin.case0 _ b;
      step :=  (lift_conf (fun (g : Names.G) Rconf =>
                             Some (trans (Config.loc (Rconf)))))
                 
    |}.
  Proof.
    - intros [g1|b1] [g2|b2] Hg rc1 rc2 Hrc; try discriminate; simpl in *.
      unfold Names.G.
      destruct Hrc as (Hl_rc, (Hs_rc, Ht_rc)).
      destruct 
        (Loc.eq_dec (Config.loc rc1)
                    (Info.target (Config.info rc1))),
      (Loc.eq_dec (Config.loc rc2)
                  (Info.target (Config.info rc2)));
        try (now auto);
        try now rewrite Hl_rc, Ht_rc in *.
      apply Fin.case0.
      exact b1.    
  Defined.
  
    
CoFixpoint bad_demon1 : demon := Stream.cons da1 bad_demon1.

Lemma bad_demon1_tail : 
    Stream.tl bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.
  
Lemma bad_demon1_head :
    Stream.hd bad_demon1 = da1.
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
    unfold Loc.mul, Loc.eq, Loc.unit, def.n, Veq.
    repeat rewrite <- loc_fin.
    repeat rewrite Z.mod_mod; try (generalize n_sup_1; lia).
    simpl in *.
    rewrite Z.mod_0_l, Z.mod_1_l.
    omega.
    generalize n_sup_1; omega.
    generalize n_sup_1; omega.
  +  simpl in *.
     generalize k_sup_1, k_inf_n, n_sup_1.
     intros.
     unfold Loc.mul, Loc.unit in *;
       repeat rewrite <- loc_fin in *.
     unfold create_conf1.
     unfold Loc.eq, Loc.mul, Loc.unit, def.n, Veq. 
     rewrite Zdiv.mod_Zmod in Hmod; try omega.
     apply Zdiv.Z_div_exact_full_2 in Hmod; try omega.
     repeat rewrite <- loc_fin.
     repeat rewrite Z.mod_mod; try (generalize n_sup_1; lia).
     repeat rewrite Z.mod_1_l; try lia.
     rewrite Z.mul_1_r.
     fold n in *.
     rewrite Z.mod_mod; try lia.
     rewrite Nat2Z.inj_mul, Zdiv.div_Zdiv; try omega.
     fold n.
     rewrite Hmod in *.
     set (x := Z.of_nat n/Z.of_nat kG) in *. 
     replace (Z.of_nat kG * x ) with (x * Z.of_nat kG) by intuition.
     rewrite Zdiv.Z_div_mult_full; try lia.
     replace (x * Z.of_nat kG) with (Z.of_nat kG * x) by intuition.
     rewrite Zdiv.Zmult_mod_distr_r.
     assert (1 < x).
     assert (Z.of_nat kG < Z.of_nat n) by omega.
     apply Zmult_lt_reg_r with (p := Z.of_nat kG); try omega.
     rewrite Z.mul_comm with (n:= x).
     rewrite <- Hmod.
     omega.
     intuition.
     rewrite Zdiv.Zmod_eq in H3.
     rewrite Z.mul_comm in H3.
     apply Z.eq_mul_1 in H3.
     destruct H3; omega.
     omega.
Qed.

 
(** **  First case: the robots moves **)
Lemma neq_a_1a : forall a, ~Loc.eq a (Loc.add Loc.unit a).
Proof.
  generalize n_sup_1.
  intros.
  unfold Loc.eq, Loc.add, def.n, Veq, Loc.unit.
  repeat rewrite <- loc_fin.
  repeat rewrite Z.mod_mod; try omega.
  destruct (V2Z a mod Z.of_nat n ?= Z.of_nat n) eqn : Hn;
    try rewrite Z.compare_lt_iff in *;
    try rewrite Z.compare_eq_iff in *;
    try rewrite Z.compare_gt_iff in *;
    fold n in *;
    try rewrite Z.mod_1_l; try lia.
  + rewrite <- Zdiv.Zplus_mod_idemp_r, Hn,
    <- Zdiv.Zplus_mod_idemp_r, Zdiv.Z_mod_same_full.
    do 2 (simpl in *; rewrite Z.mod_1_l; try lia). 
  + apply Zlt_le_succ in Hn.
    unfold Z.succ in Hn.
    apply Zle_lt_or_eq in Hn.
    destruct Hn.
    rewrite <- Zdiv.Zplus_mod_idemp_r.
    rewrite (Zdiv.Zmod_small (1+_) _); try split; try omega.
    apply Z.add_nonneg_nonneg.
    lia.
    apply Zdiv.Z_mod_lt.
    lia.
    rewrite <- Zdiv.Zplus_mod_idemp_r, Z.add_comm, H0, Z.mod_same; try lia.
  + assert (Hn0: 0 < Z.of_nat n) by omega.
    generalize (Z.mod_pos_bound (V2Z a) (Z.of_nat n) Hn0); intros.
    omega.
Qed.


Parameter m : Z.
Hypothesis Hmove : forall g,
    V2Z (r.(pgm)
        (!! (Config.map
               (apply_sim (trans (Config.loc (config1 (Good g)))))
               (config1))) Loc.origin) = m.

Definition f_conf conf k : Config.t :=
  fun id =>
      match id with
      | Good g => {| Config.loc := Loc.add k (Config.loc (conf (Good g)));
                     Config.info :=
                       {| Info.source := Loc.add k (Info.source (Config.info (conf (Good g))));
                          Info.target := Loc.add k (Info.target (Config.info (conf (Good g))))
                       |}
                  |}
      | Byz b => conf (Byz b)
      end.

Instance f_conf_compat : Proper (Config.eq ==> Loc.eq ==> Config.eq) f_conf.
Proof.
  intros c1 c2 Hc k1 k2 Hk.
  unfold f_conf.
  unfold Config.eq.
  intros [g|b]; try ImpByz b.
  split; simpl in *.
  unfold Loc.add.
  rewrite Zdiv.Zplus_mod, Hk.
  destruct (Hc (Good g)) as (Hc',_). 
  rewrite Hc'.
  rewrite <- Zdiv.Zplus_mod.
  reflexivity.
  unfold Loc.add.
  rewrite 2 (Zdiv.Zplus_mod (V2Z k1)) , Hk.
  split; simpl;
    destruct (Hc (Good g)) as (_,(Hcs', Hct')); try rewrite Hcs'; try rewrite Hct';
      try rewrite <- Zdiv.Zplus_mod;
  reflexivity.
Qed.


(* Two configuration are equivalent if all robots of the first are moved of the same [k] numbur to have the second. *)
Definition equiv_conf conf1 conf2: Prop := exists k, Config.eq conf2 (f_conf conf1 k).


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


Definition rconfig1 := round r da1 config1.


Section Move1.
  
  Hypothesis Hm : Loc.eq (Z2V m) (Z2V 1).


(* This function moves every robots of [k] nodes. *)


(* the same than [count_occ_map], but with the abstraction. *)

Lemma rconfig1_simpl :
  let n_pos g := Loc.add (Z2V 1) (create_conf1 g) in  
  Config.eq rconfig1 (fun id =>
                        match id with
                        | Good g =>
                          {| Config.loc := n_pos g;
                             Config.info := {| Info.source := create_conf1 g;
                                               Info.target := n_pos g |}
                          |}
                        | Byz b => (config1 (Byz b))
                     end).
Proof.
  intros n_pos [g|b]; try ImpByz b.  
  unfold rconfig1, n_pos, round;
    repeat split; simpl in *;
  rewrite Loc.add_opp;
  unfold Loc.add;
  rewrite (Hmove g);
  unfold Loc.eq, LocationA.eq, Veq in *;
  repeat rewrite <- loc_fin in *; repeat rewrite Z.mod_mod;
    try (generalize n_sup_1; fold n in *; lia);
  fold n in *;
  rewrite 2 Z.mod_mod in Hm;
    try (generalize n_sup_1; fold n in *; lia);
  rewrite <- Zdiv.Zplus_mod_idemp_l, Hm;
  reflexivity.
Qed.


Definition AlwaysEquiv (e : execution) : Prop :=
  Stream.forever (fun e1 => equiv_conf rconfig1
                                        (Stream.hd e1)) e.
                                                                    
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.forever (fun e1 => ~Stopped e1) e.

    
(* An execution that is satisfing the predicate [AlwaysEquiv]
   satisfy the [AlwaysMoving] one too. *)


Lemma AlwaysMoving_impl_not_WillStop : forall e,
    e = execute r bad_demon1 (Stream.hd e)
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

Lemma config1_Spectre_Equiv : forall conf g0,
      (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id)))
            /\
            Location.eq (Info.target (Config.info (conf id)))
                        (Loc.add k (Info.target (Config.info (config1 id)))))
            ->
    Spect.eq (!! (Config.map (apply_sim
                                (trans (Config.loc (conf (Good g0)))))
                             (conf)))
             (!! (Config.map (apply_sim
                                (trans (Config.loc (config1 (Good g0)))))
                             ( config1))).
Proof.
  clear Hmove.
  intros conf g0 Hconf_equiv x.
  unfold Spect.from_config in *.
  (* unfold Spect.multiset. *)
  simpl in *.
  unfold Config.map in *.
  repeat rewrite Spect.multiset_spec in *.
  unfold apply_sim, trans; simpl.
  unfold equiv_conf, f_conf in *.
  destruct Hconf_equiv.
  destruct (H (Good g0)) as (Hl, Ht).
  simpl in *.
  
  assert (Hconf_eq_lt : forall glt,
             Loc.eq (Config.loc (conf (Good glt)))
                    (Info.target (Config.info (conf (Good glt))))).
  { intros glt.
    specialize (H (Good glt)).
    simpl in *.
    destruct H as (Hfalse_l, Hfalse_t).
    simpl in *.
    rewrite Hfalse_l, Hfalse_t.
    reflexivity.
  } 
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
      assert (Hg0 := H (Good g0));
        assert (Hg1 := H (Good g1));
        assert (Hg2 := H (Good g2));
        simpl in *.
       destruct (Names.eq_dec (Good g1) (Good g2)).
       assumption.
       generalize unique_g_2.
       intros Hu.
       exfalso.
       apply (Hu g0 g1 g2).
       intros Hn; rewrite Hn in n0.
       apply n0.
       reflexivity.
        simpl in *;
        rewrite 2 Loc.add_comm with (y := (Loc.opp (Config.loc (conf (Good g0)))))
          in Hloc;
        apply Loc.add_reg_l in Hloc;
        destruct Hg1 as (Hg1,_), Hg2 as (Hg2,_);
        rewrite Hg1, Hg2 in Hloc;
        simpl in *;
        apply Loc.add_reg_l in Hloc.
        unfold Loc.opp.
        now rewrite <- Zdiv.Zminus_mod_idemp_r, Hloc, Zdiv.Zminus_mod_idemp_r.
        + assert (Hnames := Names.names_NoDup).
      apply NoDupA_Leibniz in Hnames.
      assumption.
  }
  simpl in *.
  assert (forall elt, Spect.In elt (!! (Config.map (apply_sim
                                                      (trans (Config.loc
                                                                   (conf (Good g0)))))
                             conf)) ->
                      countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
        (Config.list
           (fun id : Names.ident =>
              apply_sim (trans (Config.loc
                                  (conf (Good g0)))) (conf id)))) = 1%nat).
  {
    intros elt Hspe.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
        (Config.list
           (fun id : Names.ident =>
              apply_sim (trans (Config.loc
                                     (conf (Good g0)))) (conf id)))) > 1)%nat
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
      unfold apply_sim, trans in *; simpl in *.
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
                   apply_sim (trans (Config.loc
                                          (conf (Good g0)))) (conf id))))
          ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
           (map Config.loc
              (Config.list
                 (fun id : Names.ident =>
                    apply_sim (trans (Config.loc
                                           (conf (Good g0))))
                              (conf id)))) <= 0)%nat by omega.
      apply le_not_gt in H2.
      contradiction.
    - exfalso; apply H1; apply Heq.
  }
  assert (forall elt,
             Spect.In elt (!! (Config.map (apply_sim (trans (Config.loc
                                                               (conf (Good g0)))))
                                          conf))
             <->
             Spect.In elt (!! (Config.map (apply_sim (trans (Config.loc
                                                               (config1 (Good g0)))))
                                          config1))).
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
       destruct (H (Good g1)) as (Hl_g1, Ht_g1).
       simpl in *.
       unfold Location.eq in *.
       rewrite Hl, Hl_g1.
       rewrite Loc.opp_distr_add.
       rewrite Loc.add_assoc.
       rewrite (Loc.add_comm _ (Loc.opp x0)).
       rewrite Loc.add_assoc, Loc.add_opp', (Loc.add_comm Loc.origin), Loc.add_origin.
       reflexivity.
     - ImpByz b.
   + intros (gc1,Hc1).
     destruct gc1 as [g1| b] eqn : Hg; try ImpByz b.
     generalize (conf1_1 g1 g0); intros Hc11.
     destruct Hc11.
     exists (Good g1).
     simpl in *.
     rewrite <- Hc1.
     destruct (H (Good g1)) as (Hl_g1, Ht_g1).
     unfold round.
     simpl in *.
     rewrite Hl_g1, Hl;
       rewrite <- Loc.add_assoc;
       rewrite (Loc.opp_distr_add x0);
       rewrite (Loc.add_comm (create_conf1 g1));
       rewrite Loc.add_assoc;
       rewrite Loc.add_assoc;
       rewrite Loc.add_opp, (Loc.add_comm Loc.origin), Loc.add_origin;
       now rewrite Loc.add_comm.
  }
  assert (Ht_map : forall x : Spect.elt, 
             Spect.In x (!! (Config.map (apply_sim (trans (Config.loc
                                                                (config1 (Good g0)))))
                                        config1))
             <-> (!! (Config.map (apply_sim (trans (Config.loc
                                                         (config1 (Good g0)))))
                                 config1))[x] = 1%nat).
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
    assert (HNoDup_map :
              SetoidList.NoDupA Loc.eq
                                (map (fun x0 : Names.ident =>
                                        Config.loc (Config.map
                                                      (apply_sim (trans ( (create_conf1 g0))))
                                                      config1 x0)) Names.names)).
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
                         id2 eqn : Hid2; try ImpByz b.
        assert (H_aux2 := conf1_1 g2 g0);
          assert (H_aux1 := conf1_1 g1 g0).
        destruct H_aux1, H_aux2.
        apply (H3 g0 g1 g2).
        intuition.
        rewrite H6 in n0.
        auto.
        simpl in *;
        do 2 rewrite Loc.add_comm with (y := Loc.opp _) in Heq;
        apply Loc.add_reg_l in Heq;
        rewrite Heq;
        reflexivity.
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
                                              (trans (Config.loc
                                                           (conf (Good g0)))))
                             conf))).
  + assert (i' : Spect.In x (!!
                               (Config.map (apply_sim (trans (Config.loc
                                                                   (config1 (Good g0)))))
                                           config1))) by now rewrite <- H2.
    unfold Spect.from_config, Config.map in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    destruct Ht_map as (Ht1, Ht2).
    rewrite H1, Ht1.
    reflexivity.
    apply i'.
    apply i.
  + assert (n0' : ~ Spect.In x (!!
                                  (Config.map (apply_sim (trans
                                                            (Config.loc
                                                               (config1 (Good g0)))))
                                              config1))) by now rewrite <- H2.
    rewrite Spect.not_In in n0.
    rewrite Spect.not_In in n0'.
    unfold Spect.from_config, Config.map in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.
Qed.

  

Lemma round_2_simplify_1 :
  forall conf,
         equiv_conf rconfig1 conf
    -> Config.eq
         (round r da1 conf)
         (fun id =>
            match id with
            | Byz b => Fin.case0 _ b
            | Good g =>
              let local_config := Config.map
                                    (apply_sim
                                       (trans 
                                          (Config.loc
                                                (conf (Good g)))))
                                    conf in
                let local_target : Loc.t := (r (Spect.from_config local_config)
                                       (Config.loc (local_config (Good g)))) in
                let new_target :=
                    ((trans
                        (Config.loc
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Bijection.section)
                                                                  local_target in
                {| Config.loc := new_target;
                   Config.info :=
                     {| Info.source := Config.loc (conf (Good g));
                        Info.target := new_target
                     |}
                |}
              end).
Proof.
  intros conf Hconf_eq [g|b]; unfold round at 1; simpl in *; try ImpByz b.
  assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id)))
            /\
            Location.eq (Info.target (Config.info (conf id)))
                        (Loc.add k (Info.target (Config.info (config1 id)))))
            ).
  { destruct Hconf_eq.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, (_, Ht));
      unfold f_conf in *.
    assert (Hrs := rconfig1_simpl).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, (_,Hts)).
    rewrite Hls in Hl.
    simpl in *.
    rewrite Hts in *.
    rewrite Hl, Ht.
    now split; rewrite Loc.add_assoc, (Loc.add_comm x).
  }
  repeat split; simpl.
Qed.

Unset Printing Implicit.
Lemma round1_move_g_1 : forall g0,
    ~ Loc.eq (Config.loc (round r da1 rconfig1 (Good g0)))
      (Config.loc (rconfig1 (Good g0))).
Proof.
  intros g0.
  simpl in *.
  rewrite Loc.add_opp.
  generalize (config1_Spectre_Equiv rconfig1 g0).
  intros.
  assert ((exists k : Loc.t,
         forall id : Names.ident,
         Location.eq (Config.loc (rconfig1 id))
           (Loc.add k (Config.loc (config1 id))) /\
         Location.eq (Info.target (Config.info (rconfig1 id)))
           (Loc.add k (Info.target (Config.info (config1 id)))))).
  { unfold rconfig1.
    unfold round.
    simpl in *.
    exists (Z2V m).
    intros[ g|b]; try ImpByz b.
    simpl.
    rewrite Loc.add_opp.
    unfold Loc.add.
    rewrite Hmove.
    split; rewrite <- loc_fin;
      now repeat rewrite Zdiv.Zplus_mod_idemp_l.
  }
  specialize (H H0).
  simpl in *.
  rewrite Loc.add_opp in *.
  rewrite H.
  assert (Hmg : Loc.eq
            (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
               Loc.origin) (Z2V m)).
  { now rewrite <- (Hmove g0), <- fin_loc. }
  rewrite 2 (Loc.add_compat (Hmg) (reflexivity _)).
  rewrite Hm.
  assert (Hneq :=  @neq_a_1a (Loc.add (Z2V 1) (create_conf1 g0))).
  unfold Loc.unit in Hneq.
  rewrite Z.mod_1_l in Hneq; try (generalize n_sup_1; lia).
  intro Hf; destruct Hneq; now symmetry.
Qed.


(* utiliser le prédicat d'équivalence (equiv_conf) pour prouver le spectre. *)



Lemma moving_no_stop : ~Stopped (((execute r bad_demon1 rconfig1))).
Proof.
  intros Hs.
  generalize n_sup_1; intros Hn1.
  destruct Hs as (Hs,_).
  unfold stop_now in Hs.
  generalize (round1_move_g_1).
  intros Hrmg1.
  simpl in Hs.
  specialize (Hs (Good g)).
  destruct Hs as (Hl, (Hs, Ht)).
  specialize (Hrmg1 g).
  destruct Hrmg1.
  apply (symmetry Hl).
Qed.  


Lemma round1_move_g_equiv : forall g0 conf,
    equiv_conf rconfig1 conf ->
    ~ Loc.eq (Config.loc (round r da1 conf (Good g0)))
                        (Config.loc (conf (Good g0))).
Proof.
  intros g0 conf Hequiv.
  assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id)))
            /\
            Location.eq (Info.target (Config.info (conf id)))
                        (Loc.add k (Info.target (Config.info (config1 id)))))
            ).
  { destruct Hequiv.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, (_, Ht));
      unfold f_conf in *.
    assert (Hrs := rconfig1_simpl).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, (_,Hts)).
    rewrite Hls in Hl.
    simpl in *.
    rewrite Hts in *.
    rewrite Hl, Ht.
    now split; rewrite Loc.add_assoc, (Loc.add_comm x).
  }
  rewrite (round_2_simplify_1 Hequiv (Good g0)) in *.
  assert (HSequiv := config1_Spectre_Equiv conf g0 Hequiv').
  unfold equiv_conf, f_conf in Hequiv.
  destruct Hequiv as (k, Hequiv).
  destruct (Hequiv (Good g0)) as (Hl0, (Hs0, Ht0)).
  simpl in *.
  intros Hf.
  rewrite HSequiv in Hf.
  specialize (Hmove g0).
  simpl in *.
  rewrite Loc.add_opp in Hf; fold Loc.origin in Hf.
  assert (Hmg : Loc.eq
                  (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
                     Loc.origin) (Z2V m)).
  { now rewrite <- Hmove, <- fin_loc. }
  rewrite (Loc.add_compat (Hmg) (reflexivity _)) in Hf.
  rewrite Hm in *.
  assert (Hn := @neq_a_1a (conf (Good g0))).
  unfold Loc.unit in Hn.
  rewrite Z.mod_1_l in Hn;
    try (generalize n_sup_1; lia).
  now destruct Hn.
Qed.

(* any configuration equivalent to the starting one will not stop if executed with 
   [r] and [bad_demon1] *)
Lemma moving_never_stop : forall conf,
    equiv_conf rconfig1 conf ->
    ~Stopped (execute r bad_demon1 conf).
Proof.
  intros conf Hconf_equiv Hstop.
  destruct Hstop as (Hstop, (Hsl, _)).
  unfold stop_now in *.
  simpl in *.
  apply (round1_move_g_equiv g Hconf_equiv).
  specialize (Hstop (Good g)).
  symmetry.
  now destruct Hstop.
Qed.

Lemma AlwaysEquiv_impl_AlwaysMoving : forall e,
    e = execute r bad_demon1 (Stream.hd e)
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
    rewrite rconfig1_simpl in *.
    simpl in *.
    now exists (x).
  - apply AlwaysEquiv_impl_AlwaysMoving.
    + rewrite Heq_e at 1.
      rewrite execute_tail.
      simpl in *.
      rewrite Heq_e at 2.
      simpl in *.
      reflexivity.
    + simpl in *.
      destruct HAequiv.
      apply HAequiv.
Qed.


Lemma AlwaysEquiv_conf1 : forall conf,
    equiv_conf rconfig1 conf
    -> AlwaysEquiv (execute r bad_demon1 conf).
Proof.
  cofix.
  intros.
  constructor.
  + destruct H.
    unfold f_conf in H.
    exists (x).
    intros [g0|b]; try ImpByz b.
    specialize (H (Good g0)).
    simpl in *.
    rewrite H.
    simpl in *.
    repeat split; simpl;
      try rewrite Loc.add_opp.
  + apply AlwaysEquiv_conf1.
    simpl in *.
    assert (Hequiv' :
              (exists k, forall id,
                    Location.eq (Config.loc (conf id))
                                (Loc.add k (Config.loc (config1 id)))
                    /\
                    Location.eq (Info.target (Config.info (conf id)))
                                (Loc.add k (Info.target
                                              (Config.info (config1 id)))))).
    { destruct H.
      exists (Loc.add (Z2V 1) x).
      intros [g0|b]; try ImpByz b.
      destruct (H (Good g0)) as (Hl, (_, Ht)).
      destruct (rconfig1_simpl (Good g0)) as (Hrl, (_,Hrt)).
      simpl in Ht.
      rewrite Hrt in Ht.
      simpl in Hl.
      rewrite Hrl in Hl.
      simpl in *.
      rewrite Ht,Hl.
      now rewrite Loc.add_assoc, (Loc.add_comm x).
    }
    unfold equiv_conf.
    destruct H.
    exists (Loc.add x (Z2V 1)).
    rewrite round_2_simplify_1.
    intros id.
    simpl.
    destruct id; try ImpByz b.
    assert (Haux := config1_Spectre_Equiv).
    assert (Hmove_eq :=
              pgm_compat
                r
                (!!
                   (Config.map (apply_sim (trans (Config.loc (conf (Good g0)))))
                               (conf)))
                (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g0)))))
                                (config1)))
           (Haux conf g0 Hequiv') Loc.origin _ (reflexivity _)).
    assert (Hmove' := Hmove).
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
                       Loc.origin) (Z2V m)).
    { now rewrite <- (Hmove g0), <- fin_loc. }
    specialize (Hmove' g0).
    simpl in *.
    repeat split; simpl; try repeat rewrite Loc.add_opp.
    rewrite (Loc.add_compat Hmg (reflexivity _)).
    rewrite Hmove_eq, Hmg.
    repeat rewrite Zdiv.Zplus_mod_idemp_l;
      repeat rewrite Zdiv.Zplus_mod_idemp_r;
    destruct (H (Good g0)) as (Hl,( _ , Ht));
    try rewrite Zdiv.Zplus_mod, Hl, <- Zdiv.Zplus_mod;
    try rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod;
    unfold f_conf;
    destruct (rconfig1_simpl (Good g0)) as (Hl0,(_, Ht0));
    simpl in *;
    rewrite Hl, Loc.add_opp, (Loc.add_compat Hmg (reflexivity _));
    rewrite Hm;
    now rewrite Loc.add_assoc, (Loc.add_comm _ x).
    destruct (H (Good g0)) as (Hl,( _ , Ht)).
    rewrite Hl.
    simpl.
    rewrite Loc.add_opp.
    rewrite (Loc.add_compat Hmg (reflexivity _)).
    rewrite Hm.
    now rewrite Loc.add_assoc.
    rewrite (Loc.add_compat Hmove_eq (reflexivity _)).
    rewrite 2 (Loc.add_compat Hmg (reflexivity _)).
    rewrite Hm.
    destruct (H (Good g0)) as (Hl,( _ , Ht)).
    rewrite Hl.
    simpl.
    rewrite Loc.add_opp.
    rewrite (Loc.add_compat Hmg (reflexivity _)).
    rewrite Hm.
    now rewrite Loc.add_assoc, (Loc.add_comm _ x).
    now exists x.
Qed.

(* the starting configuration respect the [AlwaysMoving] predicate *)

Lemma config1_AlwaysMoving : AlwaysMoving (execute r bad_demon1 rconfig1).
Proof.
  apply AlwaysEquiv_impl_AlwaysMoving.
  now simpl.
  apply AlwaysEquiv_conf1.
  exists Loc.origin.
  unfold f_conf.
  intros [g|b]; try ImpByz b.
  now repeat split;simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
Qed.

(* If an execution use [r] as its robogram, and [bad_demon1] as its demon, *
   and if the execution respect the [AlwaysMoving] predicate, it can't respect 
   the [Will_Stop] one *)



(* The starting configuration will not stop *)
Lemma never_stop : ~ Will_stop ((execute r bad_demon1 rconfig1)).
Proof.
  apply AlwaysMoving_impl_not_WillStop.
  cbn.
  reflexivity.
  apply config1_AlwaysMoving.
Qed.

  (* final theorem first part: if we move, In the asynchronous model, and if k 
     divide n, then the exploration with stop of a n-node ring is not possible. *)

Theorem no_exploration_moving : Z_of_nat (n mod kG) = 0 -> ~ (FullSolExplorationStop r).
Proof.
  intros Hmod Habs.
  specialize (Habs bad_demon1).
  unfold FullSolExplorationStop in *.
  destruct (Habs config1) as (_, Hstop).
  destruct Hstop;
    try now apply never_stop.
  destruct H.
  unfold stop_now in H.
  simpl in *.
  fold rconfig1 in H.
  rewrite rconfig1_simpl in H.
  destruct (H (Good g)) as (Hl, _);
    simpl in *.
  symmetry in Hl.
  assert (Hn := @neq_a_1a (create_conf1 g)).
  unfold Loc.unit in *; rewrite Z.mod_1_l in Hn; try (generalize n_sup_1; lia).
  now destruct Hn.
Save.

End Move1.

Section Stop.

  Hypothesis Hm : Loc.eq (Z2V m) (Z2V 0).

  Lemma round_simplify_0 : forall conf,
      equiv_conf config1 conf -> 
      Config.eq (round r da1 conf) conf.
  Proof.
    intros.
    unfold round.
    simpl in *.
    unfold lift_conf; simpl.
    intros [g|b]; try ImpByz b.
    simpl in *.    
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))
                       Loc.origin) (Z2V m)).
    { now rewrite <- (Hmove g), <- fin_loc. }
    repeat split; simpl; try rewrite Loc.add_opp, (config1_Spectre_Equiv conf g);
      try rewrite (Loc.add_compat Hmg (reflexivity _));
      try rewrite Hm;
    assert (Loc.eq (Z2V 0) Loc.origin)
      by (unfold Loc.origin, Loc.eq, Veq; rewrite <- 2 loc_fin;
          repeat rewrite Z.mod_mod; generalize n_sup_1; fold n; try lia);
    try (now rewrite H0, Loc.add_comm, Loc.add_origin); destruct H.
    exists x.
    intros [g0|b]; try ImpByz b.
    destruct (H (Good g0)) as (Hl,( _,Ht)).
    rewrite Hl, Ht.
    now unfold f_conf; simpl.
    destruct (H (Good g)) as (Hl,(Hs,_)).
    rewrite Hl, Hs.
    now simpl.
    destruct (H (Good g)) as (Hl,(_, Ht)).
    rewrite H0, Hl ,Ht, Loc.add_comm, Loc.add_origin; now simpl.
    exists x.
    intros [g0|b]; try ImpByz b.
    destruct (H (Good g0)) as (Hl,( _,Ht)).
    rewrite Hl, Ht.
    now unfold f_conf; simpl.
  Qed.
  
  Lemma NeverVisited_conf1 : forall e,
       eeq e (execute r bad_demon1 config1) ->
       exists l, ~ Will_be_visited l e.
  Proof.
    intros e Heq_e.
    exists Loc.unit.
    intros Hl.
    induction Hl.
    + destruct H as (g0, Hvis).
      rewrite Heq_e in Hvis.
      simpl in Hvis.
      assert (Z.of_nat (n mod kG) = 0) by (generalize kdn; fold n in *; lia).
      now apply (config1_ne_unit H g0).
    + apply IHHl.
      rewrite Heq_e.
      cbn.
      symmetry.
      assert (Hequiv : equiv_conf config1 config1).
      { exists Loc.origin.
        unfold f_conf.
        intros id.
        simpl in *.
        destruct id as [g|b]; try ImpByz b.
        repeat split; simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin;
          reflexivity.
      }
      rewrite (execute_compat (reflexivity r) (reflexivity bad_demon1)
                            (symmetry (round_simplify_0 Hequiv))).
      constructor.
      simpl.
      now rewrite round_simplify_0.
      now rewrite round_simplify_0.
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
    
  Theorem no_exploration_idle : Z_of_nat (n mod kG) = 0 -> ~ (FullSolExplorationStop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    destruct (Habs config1) as (Hexpl, _).
    now apply never_visited.
  Save.

End Stop.

Section Move_minus1.

  Hypothesis Hm : Loc.eq (Z2V m) (Loc.opp (Z2V 1)).

  Lemma round_2_config1 :
    Config.eq (round r da1 config1)
              (fun id =>
                 match id with
                 | Good g =>
                   {| Config.loc := Loc.add (Loc.opp (Z2V 1)) (create_conf1 g);
                      Config.info :=
                        {| Info.source := create_conf1 g;
                           Info.target := Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)
                        |} |}
                 | Byz b => (config1 (Byz b))
                 end).
  Proof.
    intros [g|b]; try ImpByz b.
    unfold round.
    simpl in *.
    destruct (Loc.eq_dec (create_conf1 g) (create_conf1 g)) as [?|nfalse];
      try (now destruct nfalse).
    simpl in *.
    specialize (Hmove g).
    simpl in *.
    destruct (Location.eq_dec
                  (Loc.add
                     (r
                        (!!
                           (Config.map (apply_sim (trans (create_conf1 g))) config1))
                        (Loc.add (create_conf1 g) (Loc.opp (create_conf1 g))))
                     (create_conf1 g)) (create_conf1 g)).
    - exfalso.
      rewrite Loc.add_opp in e0; fold Loc.origin in e0.
      assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g))) config1))
                         Loc.origin) (Z2V m)).
      { now rewrite <- (Hmove), <- fin_loc. }
      rewrite Hmg in e0.
      rewrite Hm in e0.
      assert (Loc.eq (Loc.add (Z2V 1) (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))
                     (Loc.add (Z2V 1) (create_conf1 g))).
      { apply (Loc.add_reg_l (Loc.opp (Z2V 1))). 
        now rewrite 3 Loc.add_assoc, Loc.add_opp',
        2(Loc.add_comm Loc.origin), 2 Loc.add_origin.
      }
      rewrite Loc.add_assoc, Loc.add_opp, Loc.add_comm, Loc.add_origin in H.
      assert (Hn : Loc.eq (Loc.unit) (Z2V 1)).
      unfold Loc.eq, Veq, Loc.unit; rewrite <- 2 loc_fin, 2 Z.mod_mod;
        try (generalize n_sup_1; lia).
      now rewrite <- Hn in H; apply neq_a_1a in H.
    - simpl in *.
      destruct (Loc.eq_dec (create_conf1 g)
           (Loc.add
              (r (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))
                 (Loc.add (create_conf1 g) (Loc.opp (create_conf1 g))))
              (create_conf1 g)))
        as [?|n0'];
        try (now destruct n0); try now destruct n0'.
      simpl in *.
      now repeat split; simpl;
      rewrite Loc.add_opp;
      fold Loc.origin;
      assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g))) config1))
                         Loc.origin) (Z2V m))
        by (now rewrite <- (Hmove), <- fin_loc);
      rewrite (Loc.add_compat Hmg (reflexivity _));
      rewrite Hm.
  Qed.

  Lemma round_2_2_simplify : Config.eq (f_conf (round r da1 (config1))
                                               (Loc.opp (Z2V 1)))
                                       (round r da1
                                              (round r da1 config1)).
  Proof.
    intros [g|b]; try ImpByz b.
    rewrite round_2_config1.
    unfold round.
    simpl in *; unfold lift_conf; simpl.
    assert (Location.eq (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans
                                       (Loc.add (Loc.opp (Z2V 1))
                                                (create_conf1 g))))
                                 (* (trans (Config.loc ((round r da1 (round r da1 config1)) (Good g)))))*) 
                                 (fun id : Names.ident =>
                                    match id with
                                    | Good g0 =>
                                       {|
                     Config.loc := Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0);
                     Config.info := {|
                                    Info.source := create_conf1 g0;
                                    Info.target := Loc.add 
                                                     (Loc.opp (Z2V 1))
                                                     (create_conf1 g0) |} |}
                 | Byz _ =>
                     {|
                     Config.loc := Loc.origin;
                     Config.info := {|
                                    Info.source := Loc.origin;
                                    Info.target := Loc.origin |} |}
                                    end)))
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (create_conf1 g)))))
                        (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans (Config.loc (config1 (Good g)))))
                                 config1))
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (create_conf1 g)))))
           ).
    { apply pgm_compat; try reflexivity.
      rewrite <- round_2_config1.
      assert (Hc_eq :
                Config.eq
                  (Config.map
                     (apply_sim (trans (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))))
                     (round r da1 config1))
                  (Config.map
                     (apply_sim
                        (trans (Config.loc ((round r da1 config1)
                                              (Good g)))))
                     (round r da1 (config1)))).
      { apply Config.map_compat; try easy.
        apply apply_sim_compat.
        assert (Location.eq (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                            (Config.loc
                               ((round r da1 config1) (Good g))))
          by now rewrite (round_2_config1 (Good g)).
        now rewrite H.
      }
      rewrite Hc_eq.
      rewrite (config1_Spectre_Equiv ((round r da1 config1)) g).
      reflexivity.
      exists (Loc.opp (Z2V 1)).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_config1).
      specialize (Hr (Good g')).
      destruct Hr as (Hl, (_, Ht)).
      simpl in *.
      repeat split;simpl.
      now rewrite Hl.
      now rewrite Ht.
    }
    specialize (Hmove g).
    destruct (Location.eq_dec
                (Loc.add
                   (r
                      (!!
                         (Config.map
                            (apply_sim
                               (trans (Loc.add (Loc.opp (Z2V 1))
                                               (create_conf1 g))))
                            (fun id : Names.ident =>
                               match id with
                               | Good g0 =>
                                 {|
                                   Config.loc := Loc.add 
                                                   (Loc.opp (Z2V 1)) 
                                                   (create_conf1 g0);
                                   Config.info :=
                                     {|
                                       Info.source := create_conf1 g0;
                                       Info.target := Loc.add (Loc.opp (Z2V 1))
                                                                (create_conf1 g0)
                                     |} |}| Byz _ =>
                                 {|
                                   Config.loc := Loc.origin;
                                   Config.info := {|
                                                         Info.source := Loc.origin;
                                                         Info.target := Loc.origin |} |}
                               end)))
                      (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                               (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))))
                   (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))
                (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))
      as [e0|nmove].
    - exfalso.
      rewrite H in e0.
      rewrite Loc.add_opp in e0; fold Loc.origin in e0;
        simpl in *.
      assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g))) config1))
                         Loc.origin) (Z2V m))
        by (now rewrite <- (Hmove), <- fin_loc);
        rewrite (Loc.add_compat Hmg (reflexivity _)), Hm in e0.
      apply Loc.add_reg_l in e0.
      assert (Hfalse : Location.eq
                         ((Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))
                         (Loc.add (Z2V 1) (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))).
      { rewrite Loc.add_assoc, Loc.add_opp, (Loc.add_comm Loc.origin), Loc.add_origin.
        assumption.
      }
      assert (Loc.eq (Z2V 1) Loc.unit).
      { unfold Loc.unit,Loc.eq, Veq; rewrite <- 2 loc_fin, 2 Z.mod_mod;
          try generalize n_sup_1; unfold n in *; try lia.
      }
      rewrite H0 in Hfalse.
      now apply neq_a_1a in Hfalse.
    - simpl in *.
      destruct (Loc.eq_dec
                  (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                  (Loc.add
                     (r
                        (!!
                           (Config.map
                              (apply_sim (trans (Loc.add (Loc.opp (Z2V 1))
                                                         (create_conf1 g))))
                              (fun id : Names.ident =>
                                 match id with
                                 | Good g0 =>
                                   {|
                                     Config.loc := Loc.add (Loc.opp (Z2V 1))
                                                           (create_conf1 g0);
                                     Config.info :=
                                       {|

                                         Info.source := create_conf1 g0;
                                         Info.target := Loc.add
                                                            (Loc.opp (Z2V 1))
                                                            (create_conf1 g0) |} |}
                                 | Byz _ =>
                                   {|
                                     Config.loc := Loc.origin;
                                     Config.info :=
                                       {|
                                         Info.source := Loc.origin;
                                         Info.target := Loc.origin |} |}
                                 end)))
                        (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))
                                 (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g)))))
                     (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))))
      ; try now destruct nmove.
      simpl in *.
      repeat split; simpl; 
        try rewrite H;
        assert (Hmg : Loc.eq
                        (r (!! (Config.map (apply_sim
                                              (trans (create_conf1 g))) config1))
                           Loc.origin) (Z2V m))
          by (now rewrite <- (Hmove), <- fin_loc);
        try rewrite Loc.add_opp, (Loc.add_compat Hmg (reflexivity _)), Hm;
        try easy.
  Qed.
    
  Lemma round1_move_g_1_m : forall g0,
      ~ Loc.eq (Config.loc (round r da1 (round r da1 config1) (Good g0)))
        (Config.loc ((round r da1 config1) (Good g0))).
  Proof.
    intros g0.
    rewrite <- (round_2_2_simplify (Good g0)).
    unfold f_conf.
    assert (Hr2c := round_2_config1 (Good g0)). 
    destruct Hr2c as (Hl2c, (Hs2c, Ht2c)).
    simpl in *.
    intros Hf.
    apply (@neq_a_1a (Loc.add
               (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
                  (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g0))))
               (create_conf1 g0))).
    rewrite <- Hf.
    unfold Loc.unit.
    rewrite Z.mod_1_l.
    rewrite (Loc.add_assoc (Z2V 1)), 2 Loc.add_opp, (Loc.add_comm (Loc.origin)),
    Loc.add_origin.
    now rewrite Loc.add_opp in *.
    generalize n_sup_1; lia.
  Qed.


  (* utiliser le prédicat d'équivalence (equiv_conf) pour prouver le spectre. *)



  Lemma moving_no_stop_m : ~Stopped ((execute r bad_demon1 (round r da1 config1))).
  Proof.
    intros Hs.
    generalize n_sup_1; intros Hn1.
    destruct Hs as (Hs, _).
    unfold stop_now in Hs.
    simpl in *.
    specialize (Hs (Good g)).
    destruct Hs as (Hl, (Hs, Ht)).
    simpl in *.
    now apply (round1_move_g_1_m g).
  Qed.  

(* Lemma round_2_simplify_m1 :
  forall conf,
         equiv_conf (round r da1 (config1)) conf
    -> Config.eq
         (round r da1 conf)
         (fun id =>
            match id with
            | Byz b => Fin.case0 _ b
            | Good g =>
              let local_config := Config.map
                                    (apply_sim
                                       (trans 
                                          (Config.loc
                                                (conf (Good g)))))
                                    conf in
                let local_target : Loc.t := (r (Spect.from_config local_config)
                                       (Config.loc (local_config (Good g)))) in
                let new_target :=
                    ((trans
                        (Config.loc
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Bijection.section)
                                                                  local_target in
                {| Config.loc := new_target;
                   Config.info :=
                     {| Info.source := Config.loc (conf (Good g));
                        Info.target := new_target
                     |}
                |}
              end).
Proof.
  intros conf Hconf_eq [g|b]; unfold round at 1; try ImpByz b.
 now split. (* 
 assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id)))
            /\
            Location.eq (Info.target (Config.info (conf id)))
                        (Loc.add k (Info.target (Config.info (config1 id)))))
            ).
  { destruct Hconf_eq.
    exists (Loc.add (Loc.opp (Z2V 1)) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, (_, Ht));
      unfold f_conf in *.
    assert (Hrs := round_2_config1).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, (_,Hts)).
    simpl in *.
    rewrite Hls in Hl.
    simpl in *.
    rewrite Hts in *.
    rewrite Hl, Ht.
    now split; rewrite Loc.add_assoc, (Loc.add_comm x).
  }
  simpl.
  now split
  destruct Hconf_eq.
  destruct (H (Good g)) as (Hl, (Hs, Ht)).
  split; simpl in *;
  try rewrite Hl in *;
  try rewrite Hs in *;
  try rewrite Ht in *.
  assert (Hequiv_g := config1_Spectre_Equiv conf g Hequiv').
  rewrite Hl in Hequiv_g.
  rewrite Hequiv_g.
  repeat rewrite Loc.add_opp.
  unfold Loc.add;
    simpl;
  repeat rewrite Hmove.
  repeat rewrite <- loc_fin.
  repeat rewrite Z.mod_mod.
  assert (Location.eq (Graph.Z2V
                               (ImpossibilityKDividesN.Loc.add m
                                  (ImpossibilityKDividesN.Loc.add 
                                     (Graph.Loc x)
                                     (ImpossibilityKDividesN.Loc.add m
                                        (Graph.Loc (create_conf1 g)) mod 
                                      Z.of_nat n) mod Z.of_nat n)
                                  mod Z.of_nat Graph.n))
                      (Config.loc ((round r da1 conf) (Good g)))).
  { unfold round.
    simpl.
    rewrite Loc.add_opp.
    rewrite Hl.
    rewrite Hequiv_g.
    unfold Location.eq, Veq.
    simpl in *.
    rewrite Loc.add_opp.
    unfold Loc.add.
    rewrite Hmove.
    repeat rewrite <- loc_fin.
    now repeat rewrite Z.mod_mod;
      try (generalize n_sup_1; unfold n; lia).
  }
  assert (Hrp : Location.eq
                   ((r
                       (!!
                          (Config.map
                             (apply_sim
                                (trans
                                   (Graph.Z2V
                                      (ImpossibilityKDividesN.Loc.add
                                         m
                                         (ImpossibilityKDividesN.Loc.add 
                                            (Graph.Loc x)
                                            (ImpossibilityKDividesN.Loc.add
                                               m
                                               (Graph.Loc (create_conf1 g)) mod 
                                               Z.of_nat n) mod Z.of_nat n)
                                         mod Z.of_nat Graph.n)))) 
                             (round r da1 conf))) Loc.origin))
                   (r
                      (!!
                         (Config.map
                            (apply_sim
                               (trans (Config.loc (round r da1 conf (Good g)))))
                            (round r da1 conf))) Loc.origin)).
  { apply (pgm_compat r).
    apply Spect.from_config_compat.
    apply Config.map_compat.
    apply apply_sim_compat.
    apply trans_compat.
    apply H0.
    reflexivity.
    reflexivity.
  }
  simpl.
  unfold Location.eq, Veq in H0.
  rewrite <- loc_fin in H0.
  unfold ImpossibilityKDividesN.Loc.add in *.
  unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq, ImpossibilityKDividesN.def.n, n in *.
  rewrite 3 Zdiv.Zplus_mod.
  rewrite H0.
  rewrite Hrp.
  repeat rewrite Zdiv.Zplus_mod_idemp_l;
    repeat rewrite Zdiv.Zplus_mod_idemp_r.
  assert ((exists k : Loc.t,
     forall id : Names.ident,
     Location.eq (Config.loc (round r da1 conf id)) (Loc.add k (Config.loc (config1 id))) /\
     Location.eq (Info.target (Config.info (round r da1 conf id)))
       (Loc.add k (Info.target (Config.info (config1 id)))))).
  { exists (Loc.add (Z2V m) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hlr, (_, Htr));
      unfold f_conf in *.
    assert (Hrs := round_2_config1).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, (_,Hts)).
    simpl in *.
    rewrite Hls in Hlr.
    simpl in *.
    rewrite Hts in *.
    rewrite config1_Spectre_Equiv.
    rewrite Loc.add_opp.
    unfold Loc.add; simpl;
      rewrite Hmove.
    repeat rewrite <- loc_fin.
    unfold ImpossibilityKDividesN.Loc.add;
      rewrite (Zdiv.Zplus_mod _ (Loc (Config.loc (conf (Good g'))))). 
    rewrite Hlr.
    unfold Loc.add, ImpossibilityKDividesN.Loc.add.
    rewrite (Zdiv.Zplus_mod (Loc (Loc.opp _))), <- Hm.
    repeat rewrite <- loc_fin.
    unfold ImpossibilityKDividesN.def.n, n.
    repeat rewrite Zdiv.Zplus_mod_idemp_l;
      repeat rewrite Zdiv.Zplus_mod_idemp_r.
    replace ((m mod Z.of_nat ImpossibilityKDividesN.n +
          (((m + Graph.Loc x) mod Z.of_nat ImpossibilityKDividesN.n)
           mod Z.of_nat ImpossibilityKDividesN.n) mod Z.of_nat ImpossibilityKDividesN.n +
          Graph.Loc (create_conf1 g')))
            with (m mod Z.of_nat ImpossibilityKDividesN.n +
          ((((m + Graph.Loc x) mod Z.of_nat ImpossibilityKDividesN.n)
           mod Z.of_nat ImpossibilityKDividesN.n) mod Z.of_nat ImpossibilityKDividesN.n +
          Graph.Loc (create_conf1 g'))) by lia.
    rewrite Zdiv.Zplus_mod_idemp_l, <- (Zdiv.Zplus_mod_idemp_r (((((m + (Loc _)) mod _)mod _) mod _)+_) m).
    repeat rewrite Z.mod_mod;try (generalize n_sup_1; unfold n; lia).
    repeat rewrite Zdiv.Zplus_mod_idemp_l.
    repeat rewrite Zdiv.Zplus_mod_idemp_r.
    rewrite <- (Zdiv.Zplus_mod_idemp_r (Loc x + _) m).
    rewrite (Zdiv.Zplus_mod_idemp_r _ (Loc x)).
    rewrite Zdiv.Zplus_mod_idemp_r.
    now replace (m + (Loc x + (m + Graph.Loc (create_conf1 g')))) with
        (m + (m + Loc x + Graph.Loc (create_conf1 g'))) by lia.
    apply Hequiv'.
  }
  rewrite (Zdiv.Zplus_mod (Loc (r _ _))).
  fold ImpossibilityKDividesN.def.n.
  rewrite (pgm_compat r _ _ (config1_Spectre_Equiv (round r da1 conf) g H1)
                      _ _ (reflexivity Loc.origin)).
  simpl.
  rewrite Hmove.
  unfold Loc.add, ImpossibilityKDividesN.Loc.add;
    fold ImpossibilityKDividesN.def.n;
  rewrite (Zdiv.Zplus_mod (Loc (r _ _ ))).
  rewrite (pgm_compat r _ _ (reflexivity _) _ _ (Loc.add_opp (Config.loc (conf (Good g))))).
  rewrite (pgm_compat r _ _ (config1_Spectre_Equiv conf g Hequiv') _ _ (reflexivity _)).
  simpl.
  rewrite Hmove.
  repeat rewrite <- loc_fin.
  unfold ImpossibilityKDividesN.def.n in *.
  rewrite Hl.
  unfold Loc.add, ImpossibilityKDividesN.Loc.add;
    fold ImpossibilityKDividesN.def.n;
  rewrite (Zdiv.Zplus_mod (Loc (r _ _ ))).
  rewrite (pgm_compat r _ _ (reflexivity _) _ _ (Loc.add_opp (create_conf1 g))).
  rewrite Hmove.
  rewrite <- loc_fin.


  
  unfold round; simpl.
  destruct (Loc.eq_dec (Config.loc (conf (Good g)))
                         (Info.target (Config.info (conf (Good g)))))
      as [e_lt|nfalse] eqn : Hlt_eqdec; try now destruct nfalse; rewrite Hlg0, Htg0.
  simpl in *.
  destruct ( Location.eq_dec
                  (Loc.add
                     (r
                        (!!
                           (Config.map
                              (apply_sim (trans (Config.loc (conf (Good g))))) conf))
                        (Loc.add (Config.loc (conf (Good g)))
                           (Loc.opp (Config.loc (conf (Good g))))))
                     (Config.loc (conf (Good g)))) (Config.loc (conf (Good g)))).
  rewrite Hequiv_g in e.
  specialize (Hmove g);
    simpl in *.
  rewrite Loc.add_opp in e; fold Loc.origin in e.
  assert (Hmove' : Loc.eq
                     (r (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))
                        Loc.origin)
                     (Z2V m)) by now rewrite <- Hmove, <- fin_loc.
  unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq in e.
  rewrite Hm in *.
  rewrite (Loc.add_compat Hmove' (reflexivity _)) in e.
  exfalso.
  apply (@neq_a_1a (Config.loc (conf (Good g)))).
  unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq.
  rewrite <- e at 1.
  unfold Loc.add, Loc.opp, ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp, n, ZnZ.ImpossibilityKDividesN.def.n.
  rewrite Zdiv.Zminus_mod, Z.mod_same;
  repeat rewrite <- loc_fin;
    repeat rewrite Z.mod_mod;
    repeat rewrite Zdiv.Zminus_mod_idemp_r;
    repeat rewrite Zdiv.Zplus_mod_idemp_l;
    repeat rewrite Zdiv.Zplus_mod_idemp_r;
    try (generalize n_sup_1; unfold n; lia);
  now replace (1 + (0 - 1 + Graph.Loc (Config.loc (conf (Good g))))) with
  (Graph.Loc (Config.loc (conf (Good g)))) by lia.
  simpl in *.
  destruct (Loc.eq_dec (Config.loc (conf (Good g)))
           (Loc.add
              (r
                 (!!
                    (Config.map (apply_sim (trans (Config.loc (conf (Good g)))))
                       conf))
                 (Loc.add (Config.loc (conf (Good g)))
                    (Loc.opp (Config.loc (conf (Good g))))))
              (Config.loc (conf (Good g))))).
  Show 2. try now destruct n0.
  simpl in *.
  reflexivity.
  destruct nfalse; rewrite Hlg0, Htg0.
  assert (Hr := round_2_config1 (Good g)).
  simpl in *.
  destruct Hr as (Hl, (_, Ht)).
  simpl in *.
  now rewrite Hl, Ht. *) 
Qed.*)

  
  Lemma round1_move_g_equiv_m : forall g0 conf,
      equiv_conf (round r da1 (config1)) conf ->
      ~ Loc.eq (Config.loc ((round r da1 conf) (Good g0)))
        (Config.loc (conf (Good g0))).
  Proof.
    intros g0 conf Hequiv.
    assert (Hequiv' :
              (exists k, forall id,
                    Location.eq (Config.loc (conf id))
                                (Loc.add k (Config.loc (config1 id)))
                    /\
                    Location.eq (Info.target (Config.info (conf id)))
                                (Loc.add k (Info.target
                                              (Config.info (config1 id)))))).
    { destruct Hequiv.
      exists (Loc.add (Loc.opp (Z2V 1)) x).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_config1).
      specialize (Hr (Good g')).
      destruct Hr as (Hl, (_, Ht)).
      simpl in *.
      destruct (H (Good g')) as (Hl', (_,Ht')).
      rewrite Hl', Ht' in *.
      unfold f_conf in *.
      simpl in *.
      rewrite Hl in *.
      repeat split;simpl; 
        rewrite Loc.add_assoc, (Loc.add_comm x); easy.
    }
    assert (HSequiv := config1_Spectre_Equiv conf g0 Hequiv').
    simpl.
    rewrite Loc.add_opp.
    rewrite (config1_Spectre_Equiv conf g0 Hequiv').
    assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g0))) config1))
                         Loc.origin) (Z2V m))
        by (now rewrite <- (Hmove g0), <- fin_loc);
      simpl;
      rewrite (Loc.add_compat Hmg (reflexivity _));
      rewrite Hm.
    intro Hf.
    apply (@neq_a_1a (conf (Good g0))).
    rewrite <- Hf.
    unfold Loc.unit.
    rewrite Z.mod_1_l.
    now rewrite (Loc.add_assoc (Z2V 1)), Loc.add_opp, (Loc.add_comm (Loc.origin)),
    Loc.add_origin.
    generalize n_sup_1; lia.
  Qed.

  (* any configuration equivalent to the starting one will not stop if executed with 
   [r] and [bad_demon1] *)
  Lemma moving_never_stop_m : forall conf,
      equiv_conf (round r da1 (config1)) conf ->
      ~Stopped (execute r bad_demon1 conf).
  Proof.
    intros conf Hconf_equiv Hstop.
    destruct Hstop as (Hstop, _).
    unfold stop_now in *.
    simpl in *.
    apply (round1_move_g_equiv_m g Hconf_equiv).
    specialize (Hstop (Good g)).
    symmetry.
    apply Hstop.
  Qed.


  CoInductive AlwaysEquiv_m (e : execution) : Prop :=
    CAE_m : equiv_conf (round r da1 (config1)) (Stream.hd e) ->
            AlwaysEquiv_m ((Stream.tl e)) -> AlwaysEquiv_m e.


  
  Lemma AlwaysEquiv_impl_AlwaysMoving_m : forall e,
      e = execute r bad_demon1 (Stream.hd e)
      -> AlwaysEquiv_m e -> AlwaysMoving e.
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
      apply moving_never_stop_m.
      unfold round.
      exists x.
      reflexivity.
    -  destruct HAequiv.
       apply AlwaysEquiv_impl_AlwaysMoving_m.
       + rewrite Heq_e at 1.
         rewrite execute_tail.
         simpl in *.
         rewrite Heq_e at 2.
         simpl in *.
         reflexivity.
       + assumption.
  Qed.


  Lemma AlwaysEquiv_conf1_m : forall conf,
      equiv_conf (round r da1 (config1)) conf
      -> AlwaysEquiv_m (execute r bad_demon1 conf).
  Proof.
    cofix.
    intros.
    constructor.
    + now simpl in *.
    + assert (Hequiv' :
                (exists k, forall id,
                      Location.eq (Config.loc (conf id))
                                  (Loc.add k (Config.loc (config1 id)))
                      /\
                      Location.eq (Info.target (Config.info (conf id)))
                                  (Loc.add k (Info.target
                                                (Config.info (config1 id)))))).
      { destruct H.
        exists (Loc.add (Loc.opp (Z2V 1)) x).
        intros [g'|b]; try ImpByz b.
        assert (Hr :=  round_2_config1).
        specialize (Hr (Good g')).
        destruct Hr as (Hl, (_, Ht)).
        simpl in *.
        destruct (H (Good g')) as (Hl', (_,Ht')).
        rewrite Hl', Ht' in *.
        unfold f_conf in *.
        simpl in *.
        rewrite Hl in *.
        repeat split;simpl; 
          rewrite Loc.add_assoc, (Loc.add_comm x); easy.
      }
      apply AlwaysEquiv_conf1_m.
      assert (Hr := round_2_config1).
      simpl.
      destruct H.
      exists (Loc.add x (Z2V m)).
      simpl.
      intros id.
      simpl.
      destruct id; try ImpByz b.
      simpl.
      specialize (Hr (Good g0));
      destruct Hr as (Hl, (_, Ht)).
      assert (Haux := config1_Spectre_Equiv).
      repeat split; simpl;
        try (
            rewrite (Haux conf g0 Hequiv'), 2 Loc.add_opp;
            try (destruct (H (Good g0)) as (Hlf, (_ , Htf));
                 rewrite Hlf;
                 simpl in *;
                 rewrite Hl;
                 rewrite Hm;
                 rewrite (Loc.add_assoc x);
                 rewrite Loc.add_comm;
                 rewrite <- Loc.add_assoc;
                 now rewrite (Loc.add_comm (create_conf1 g0)))).
      destruct (H (Good g0)) as (Hlf, (_ , Htf));
        rewrite Hlf.
      simpl.
      rewrite <- (Hmove g0).
      rewrite Loc.add_opp.
      simpl.
      rewrite <- fin_loc.
      now rewrite Loc.add_assoc.
  Qed.

  (* the starting configuration respect the [AlwaysMoving] predicate *)

  Lemma config1_AlwaysMoving_m : AlwaysMoving (execute r bad_demon1
                                                       (round r da1 (config1))).
  Proof.
    apply AlwaysEquiv_impl_AlwaysMoving_m.
    now simpl.
    apply AlwaysEquiv_conf1_m.
    exists Loc.origin.
    unfold f_conf.
    intros [g|b]; try ImpByz b.
    now repeat split;simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
  Qed.
  
  Lemma never_stop_m : ~ Will_stop (execute r bad_demon1 (round r da1 ((config1)))).
  Proof.
    apply AlwaysMoving_impl_not_WillStop.
    cbn.
    reflexivity.
    apply config1_AlwaysMoving_m.
  Qed.

  
  Theorem no_exploration_moving_m : Z_of_nat (n mod kG) = 0 -> ~ (FullSolExplorationStop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    unfold FullSolExplorationStop in *.
    destruct (Habs (round r da1 ((config1)))) as (_, Hstop).
    now apply never_stop_m.
  Save.

End Move_minus1.


Lemma range_r :  forall g,
    let s := (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g))))) config1)) in
    Loc.eq (r s Loc.origin) (Z2V 1)
    \/ Loc.eq (r s Loc.origin) (Z2V 0)
    \/ Loc.eq (r s Loc.origin) (Loc.opp (Z2V 1)).
Proof.
  intros Rconf s.
  assert (Hrange := pgm_range r s Loc.origin).
  destruct Hrange as (lp, (ep, (Hl, He))).
  unfold Graph.find_edge, Graph.Eeq in *.
  destruct (Loc.eq_dec (Loc.origin)
                        (Loc.add (lp) (Z2V 1))).
  do 2 right.
  rewrite Hl.
  rewrite <- (Loc.add_origin (Loc.opp (Z2V 1))).
  rewrite Loc.add_comm.
  now rewrite e, <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
  destruct (Nat.eq_dec Graph.n 2).
  generalize k_sup_1, k_inf_n; fold n in *; lia.
  destruct (Graph.Loc.eq_dec (Graph.Loc.add Loc.origin (Graph.Z2V 1)) lp); try easy.
  left.
  rewrite Hl, <- e.
  now rewrite Loc.add_comm, Loc.add_origin.
  right; left.
  destruct (Graph.Loc.eq_dec Loc.origin lp); try easy.
  now rewrite Hl,e.
Qed.


Theorem no_exploration : Z_of_nat (n mod kG) = 0 -> ~ (FullSolExplorationStop r).
Proof.
  generalize no_exploration_idle, no_exploration_moving, no_exploration_moving_m,
  range_r.
  intros.
  specialize (Hmove g);
    specialize (H2 g).
  destruct H2.
  unfold Loc.eq, LocationA.eq, Veq in *.
  apply H0; try assumption;
  rewrite Hmove in H2. rewrite <- loc_fin, H2, Z.mod_mod; try generalize n_sup_1; lia.
  destruct H2; unfold Loc.eq, LocationA.eq, Veq in *.
  apply H; rewrite Hmove in H2; try rewrite <- loc_fin, H2, Z.mod_mod;
    try generalize n_sup_1; lia.
  now apply H1; rewrite Hmove in H2; try rewrite <- loc_fin, H2, Z.mod_mod;
    try generalize n_sup_1; lia.
Save.

End DiscreteExploration.
(*
Section ContinuousExploration.

  Theorem no_explorationC :
    forall r,
    let r' := Equiv.rbgD2C r in
      Z_of_nat (n mod kG) = 0%Z  ->
      (forall g : Names.Internals.G,
          Loc
            (Equiv.DGF.pgm (Equiv.rbgC2D r')
                           (!!
                              (Equiv.DGF.Config.map
                                 (Equiv.DGF.apply_sim
                                    (trans
                                       (Equiv.DGF.Config.loc
                                          (config1
                                             (@Good Names.Internals.G
                                                    Names.Internals.B g)))))
                                 config1)) Loc.origin) = m)
      -> ~ (forall (d : Equiv.CGF.demon) c,
               FullSolExplorationStop (Equiv.rbgC2D r')
                                      (Equiv.demonC2D d (Equiv.CGF.execute r' d c))).
  Proof.
    intros r r' H.
    generalize no_exploration_idle, no_exploration_moving, no_exploration_moving_m,
    range_r.
    intros Hnei Hnem Hnemm Hrange.
    generalize Equiv.graph_equivD2C.
    intros HgeD2C Hm.
    generalize (no_exploration Hm H).
    intros Hf HfC.
    apply Hf.
    unfold r' in *.
    intros d c.
    specialize (HfC (Equiv.demonD2C d (Equiv.DGF.execute r d c)) (Equiv.ConfigD2C c) (c)). 
    assert (Equiv.DGF.deq (Equiv.demonC2D (Equiv.demonD2C d (Equiv.DGF.execute r d c))
                                          (Equiv.CGF.execute r' (Equiv.demonD2C d (Equiv.DGF.execute r d c))
                    (Equiv.ConfigD2C c))) d).
    {
      admit.
    }
    unfold r' in *.
    rewrite H0 in HfC.
    split; destruct HfC as (Hvis, Hst); intros.
    specialize (Hvis l).
    now rewrite <- H0.
    assumption.
Qed. *)