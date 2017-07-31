(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms
      R. Pelle                 
      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
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

(** Ring Size *)

Definition n := MakeRing.n.

(** Number of Robots *)
Parameter k : nat.
Axiom k_div_n : (n mod k)%nat = 0%nat.
Axiom k_inf_n : (k < n)%nat.
Axiom k_sup_1 : (1 < k)%nat.


Module K : Size with Definition nG := k with Definition nB := 0%nat.
  Definition nG := k.
  Definition nB := 0%nat.
End K.

Module def : RingDef with Definition n := n.
 Definition n:= n.
 Lemma n_sup_1 : (n > 1)%nat. Proof. unfold n; apply n_sup_1. Qed.
 Lemma n_pos : (n <> 0)%nat. Proof. generalize n_sup_1. omega. Qed.
End def.

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
Import DGF.

Definition spect_equi config id := (!! (Config.map
               (apply_sim (trans (Config.loc (config id))))
               (config)) Loc.origin). 

(** Defintion of the Configuration *)
Definition loc_equi (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (Z2V (((Z_of_nat ((proj1_sig (Fin.to_nat f))*(n / k)))))) Loc.unit.


(** The starting configuration where a robot is on the origin, 
   and every other robot is at a distance of [x*(k/n)] where x is between 1 and k-1 *)
Definition conf_equi : Config.t :=
  fun id => match id with
              | Good g => let pos := loc_equi g in
                          {| Config.loc :=  pos;
                             Config.state := tt |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.state := tt |}
            end.

Unset Printing Dependent Evars Line.


Lemma conf1_new_aux:
  forall gg: nat,  
    V2Z (Loc.mul (Z2V (((Z_of_nat (gg*(n / k)))))) Loc.unit) mod Z.of_nat (n/k) = 0.
Proof.
  intros.
  assert (H0n : (0 < n/ k)%nat).
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
  assert (Hk_div_n := k_div_n).
  rewrite <- Nat.div_exact in Hk_div_n.
  rewrite Hk_div_n at 2.
  rewrite (Nat.mul_comm k _).
  rewrite 2 Nat2Z.inj_mul.
  rewrite Z.rem_mul_r.
  rewrite <- Zdiv.Zplus_mod_idemp_r, (Zdiv.Zmult_mod (Z.of_nat (n/k))).
  rewrite <-Zdiv.Zmult_mod_idemp_r, Z.mod_same.
  rewrite Zmult_0_r,Zmult_0_l.
  rewrite Zdiv.Zmod_0_l.
  reflexivity.
  omega.
  omega.
  generalize k_sup_1; lia.
  generalize k_sup_1; lia.
Qed.



(** A position where a robot is in conf_equi is divisible by [k/n] *)
Lemma conf1_new_1 : forall g0: Names.G, V2Z (loc_equi g0) mod Z.of_nat (n/k) = 0.
Proof.
  intros g0.
  unfold loc_equi.
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


(** If a position divides [n/k] then a robot is at this position in conf_equi *)
Lemma conf1_new_2 : forall loc, loc mod Z.of_nat (n / k) = 0 ->
                                exists g:Names.G,
                                  Loc.eq (loc_equi g) (Z2V loc).
Proof.
  intros loc Hmod.
  intros.
  generalize k_div_n n_sup_1.
  fold n in *.
  intros Hk_div_n Hns1.
  unfold Names.G, Names.Gnames, Names.Internals.Gnames, Names.Internals.G, K.nG in *.
  destruct k eqn : Hkg.
  + generalize k_sup_1; intros; omega. 
  + unfold loc_equi.
    unfold Loc.eq, Loc.mul, Loc.unit, def.n.
    assert (Hkn : forall x, x mod Z.of_nat n = 0
                              -> x mod Z.of_nat (n / S n0) = 0).
    { intros.
      rewrite Nat.mod_divides in Hk_div_n; try omega.
      destruct Hk_div_n.
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
    assert (Hmod1 :  Z.of_nat (n / k) <> 0).
      generalize k_inf_n, k_sup_1; intros.
      rewrite Nat.mod_divides, <-Hkg in Hk_div_n.
      destruct Hk_div_n.      
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
    assert (Haux' : exists x:nat, (x < k)%nat /\ 
               ((Z.of_nat x) * Z.of_nat (n/k)) mod Z.of_nat n = loc mod Z.of_nat n).
    { exists (Z.to_nat (((loc mod Z.of_nat n)/Z.of_nat (n/k)))). 
      rewrite Z2Nat.id.
      set (n' := Z.of_nat n) in *.
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
        apply Nat.div_lt_upper_bound with (b := (n/k)%nat) (q := k).
        omega.
        rewrite Nat.mul_comm.
        rewrite <- Nat.div_exact in Hk_div_n.
        rewrite Hkg, <- Hk_div_n.
        assumption.
        omega.
        omega.
      + assert (forall a, a mod Z.of_nat (n/k) = 0 -> (a mod n') mod Z.of_nat (n/k) = 0).
        intros.
        rewrite <- Nat.div_exact, <- Hkg in Hk_div_n.
        unfold n'.
        rewrite Hk_div_n at 1.
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
    specialize (Ha fg' k k_sup_1 Haux).
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
    (Z.of_nat ((proj1_sig (Fin.to_nat g)) * (n / k)) * 1) < Z.of_nat n.
Proof.
    intros.
  unfold Names.G, Names.Internals.G in *.
  assert (Hf := Fin.to_nat g).
  destruct Hf.
  generalize k_div_n; intros  Hk_div_n.
  rewrite <- Nat.div_exact in Hk_div_n.
  unfold K.nG in *.
  rewrite Hk_div_n at 2.
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


(** An injection theorem about conf_equi *)
Lemma unique_g : forall g1 g2,
               g1 <> g2 -> Loc.eq (Config.loc (conf_equi (Good g1)))
                                  (Config.loc (conf_equi (Good g2))) -> False.
Proof.
  intros.
  generalize k_sup_1, k_inf_n.
  intros Hks1 Hkin.
  unfold conf_equi, Loc.eq in H0.
  simpl in *.
  unfold loc_equi in H0.
  unfold Loc.mul, Loc.unit, def.n in H0.
  generalize (Fin.to_nat_inj g1 g2).
  intros Heq.
  apply H.
  apply Heq.
  assert (Hsol1 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g2) * (n / k)) * 1 < Z.of_nat n).
  { generalize (Fin.to_nat g2).
    intros.
    unfold K.nG in *.
    destruct s.
    simpl.
    generalize k_div_n.
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
   assert (Hsol2 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g1) * (n / k)) * 1 < Z.of_nat n).
  { generalize (Fin.to_nat g1).
    intros.
    unfold K.nG in *.
    destruct s.
    simpl.
    generalize k_div_n.
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
  assert ((0 < (n/k))%nat).
  apply Nat.div_str_pos.
  omega.
  unfold K.nG.
  omega.
Qed.




Parameter g : Names.G.


Variable r : DGF.robogram.

Lemma conf1_1 : forall idg g0: Names.G, exists g2:Names.G,
      Loc.eq (loc_equi idg)
             (Loc.add (loc_equi g0) (Loc.opp (loc_equi g2))).
Proof.
  intros.
  generalize conf1_new_1, k_sup_1, k_inf_n; intros Hc1n Hks1 Hkin.
  unfold Loc.eq.
  assert (Hc_idg := Hc1n idg).
  assert (Hc_g := Hc1n g0).
  assert (Hnkg0 : Z.of_nat (n / k) <> 0).
  assert (H0n : (0 < n/k)%nat).
  apply Nat.div_str_pos.
  omega.
  omega.
  generalize conf1_new_2; intros Hc1n2.
  unfold Loc.add, Loc.opp, def.n.
  set (n0 := Z.of_nat n).
  specialize (Hc1n2 (V2Z (loc_equi g0) - V2Z (loc_equi idg))).
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
    g1 <> g2 -> Loc.eq (Loc.add (loc_equi g0) (Loc.opp (loc_equi g1)))
                       (Loc.add (loc_equi g0) (Loc.opp (loc_equi g2)))
    -> False.
Proof.
  intros g0 g1 g2 Hg Heq.
  generalize k_sup_1, k_inf_n, conf1_inf_n.
  intros Hks1 Hkin Hcif.
  unfold conf_equi, Loc.eq in Heq.
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
  apply mod_min_eq with (a := V2Z (loc_equi g0)).
  symmetry.
  assumption.
  rewrite Zdiv.Zminus_mod in Heq.
  rewrite Zdiv.Zminus_mod with (b := V2Z (loc_equi g2)) in Heq.  assert (- Z.of_nat n < (V2Z (loc_equi g0)) mod Z.of_nat n - V2Z (loc_equi g1) mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (V2Z (loc_equi g0)) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (V2Z (loc_equi g1)) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try (fold n;omega).
    assert (- Z.of_nat n < (V2Z (loc_equi g0)) mod Z.of_nat n - V2Z (loc_equi g2) mod Z.of_nat n < Z.of_nat n).
  { assert (Hmod_n := Zdiv.Z_mod_lt).
    assert (Hns : Z.of_nat n > 0) by omega.
    assert (Hma := Hmod_n (V2Z (loc_equi g0)) (Z.of_nat n) Hns).
    assert (Hmb := Hmod_n (V2Z (loc_equi g2)) (Z.of_nat n) Hns).
    split ; try omega.
  }
  do 2 rewrite Z.mod_small in H; try omega.
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  unfold loc_equi, Loc.mul, def.n.
  apply Zdiv.Z_mod_lt; try omega.
  fold n; omega.
  fold n; omega.
  fold n; omega.
Qed.


(** Defintion of the demon *)
Definition da_equi : demonic_action.
  refine
    {|
      relocate_byz := fun b => Fin.case0 _ b;
      step :=  (lift_conf (fun (g : Names.G) =>
                             Some (fun Rconf => trans (Config.loc Rconf))))
   |}.
  Proof.
    - intros [g1|b1] [g2|b2] Hg; try discriminate; simpl in *.
      unfold Names.G.
      intros x y Hxy.
      apply trans_compat.
      apply Hxy.
      apply Fin.case0.
      exact b1.    
  Defined.
  
    
CoFixpoint demon_equi : demon := Stream.cons da_equi demon_equi.

Lemma demon_equi_tail : 
    Stream.tl demon_equi = demon_equi.
Proof. reflexivity. Qed.
  
Lemma demon_equi_head :
    Stream.hd demon_equi = da_equi.
Proof. reflexivity. Qed.
Theorem equi_kFair : kFair 1 demon_equi.
Proof.
cofix.
constructor; [| constructor].
* intros [g1 | b1] id2; try ImpByz b1.  apply kReset. simpl. discriminate.
* intros [g1 | b1] id2; try ImpByz b1. 
  apply kReset. simpl. discriminate. 
* simpl. assumption.
Qed.

(** Fairness properties *)
Lemma equi_fair : Fair demon_equi.
Proof. apply (@kFair_Fair 1%nat). apply equi_kFair. Qed.
                           
Lemma conf_equi_ne_unit : Z_of_nat (n mod k) = 0 ->
      forall g:Names.G, ~ Loc.eq (loc_equi g) Loc.unit.
Proof.
  intros Hmod g.
  generalize k_sup_1, k_inf_n, n_sup_1.
  intros.
  unfold Names.G, Names.Internals.G, K.nG in *.
  induction g.
  + simpl in *.
    unfold loc_equi.
    simpl in *.
    unfold Loc.mul, Loc.eq, Loc.unit, def.n, Veq.
    repeat rewrite <- loc_fin.
    repeat rewrite Z.mod_mod; try (generalize n_sup_1; lia).
    simpl in *.
    rewrite Z.mod_0_l, Z.mod_1_l.
    omega.
    generalize n_sup_1; omega.
    generalize n_sup_1; omega.
  + unfold Loc.mul, Loc.unit in *;
       repeat rewrite <- loc_fin in *.
    unfold loc_equi.
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
    set (x := Z.of_nat n/Z.of_nat (S n0)) in *. 
    replace (Z.of_nat (S n0) * x ) with (x * Z.of_nat (S n0)) by intuition.
    rewrite Zdiv.Z_div_mult_full; try lia.
    replace (x * Z.of_nat (S n0)) with (Z.of_nat (S n0) * x) by intuition.
    rewrite Zdiv.Zmult_mod_distr_r.
    assert (1 < x).
    assert (Z.of_nat (S n0) < Z.of_nat n) by lia.
    apply Zmult_lt_reg_r with (p := Z.of_nat (S n0)); try lia.
    intuition.
    rewrite Zdiv.Zmod_eq in H3.
    rewrite Z.mul_comm in H3.
    apply Z.eq_mul_1 in H3.
    destruct H3; omega.
    lia.
    lia.
Qed.

 
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

(** Conf_equi is a valid initial conf *)
Lemma  equi_valid : Valid_starting_conf conf_equi.
Proof.
  unfold Valid_starting_conf.
  intros l' Hf.
  simpl in *.
  destruct Hf as (l, Hf).
  rewrite Spect.multiset_spec in Hf.
  assert (HndAg : SetoidList.NoDupA Loc.eq
                                    (map (fun x : Names.ident => Config.loc (conf_equi x))
                                    Names.names)).
  {
    apply (map_injective_NoDupA eq_equivalence Loc.eq_equiv).
    + intros a b Hab.
      rewrite Hab.
      reflexivity.
    + intros id1 id2 Hloc.
      destruct id1 as [g1|b1], id2 as [g2|b2]; try ImpByz b1; try ImpByz b2.
      destruct (Names.eq_dec (Good g1) (Good g2)).
      assumption.
      assert (Hg : g1 <> g2).
      { intuition.
        apply n0.
        now rewrite H.
      }
      generalize (unique_g_2 g Hg).
      intros Hu.
      destruct Hu.
      simpl in *;
        now rewrite Hloc.
    + assert (Hnames := Names.names_NoDup).
      apply NoDupA_Leibniz in Hnames.
      assumption.
  }
  assert (Hkn : forall x, x mod Z.of_nat n = 0
                          -> x mod Z.of_nat (n / k) = 0).
  { intros.
    generalize k_sup_1; intros Hk.
    assert (Hk_div_n := k_div_n).
    rewrite Nat.mod_divides in Hk_div_n; try omega.
    destruct Hk_div_n.
    rewrite Nat.mul_comm in H0.
    rewrite H0 in *.
    rewrite Nat.div_mul in *; try lia.
    destruct x0.
    now rewrite Zdiv.Zmod_0_r.
    rewrite Nat2Z.inj_mul, Z.rem_mul_r in H.
    generalize Z_of_nat_complete; intros Haux.
    assert (Ha1 := Haux (x mod Z.of_nat (S x0))).
    assert (Ha2 := Haux ((x / Z.of_nat (S x0)) mod Z.of_nat k)).
    destruct Ha1.
    { now apply Zdiv.Z_mod_lt. }
    destruct Ha2.
    { apply Zdiv.Z_mod_lt. generalize k_sup_1; lia. }
    rewrite H1, H2 in H.
    assert (forall x y, 0 <= x -> 0 <= y -> x + y = 0 -> x = 0 /\ y = 0).
    { intros s t Hr Hs Hrs.
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
    generalize k_sup_1; 
      lia.
  }
  simpl in *.
  assert (forall elt, Spect.M.In elt (snd (!! (conf_equi) l)) ->
                        countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                              (Config.list
                                                                 conf_equi)) = 1%nat).
  {

    intros elt Hspe.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map DefsE.Config.loc
                                                 (DefsE.Config.list
                                                    conf_equi)) > 1)%nat
            -> False).
    {
      intros Hgt.     
      rewrite (NoDupA_countA_occ' Loc.eq_dec) in HndAg.
      rewrite <- Spect.M.support_In in Hspe.
      unfold Spect.from_config in Hspe.
      unfold Config.map in Hspe.
      simpl in *.
      rewrite Config.list_spec, map_map in *.
      rewrite Spect.multiset_support in Hspe.
      specialize (HndAg elt Hspe).
      unfold apply_sim, trans in *; simpl in *.
      lia.
      apply Loc.eq_equiv.
    }
    simpl in *.
    rewrite <- Spect.M.support_In in Hspe.
    unfold Spect.from_config in Hspe.
    rewrite Spect.multiset_support in Hspe.
    unfold Config.map in Hspe.
    rewrite <- (countA_occ_pos Loc.eq_equiv Loc.eq_dec) in Hspe.
    destruct ( (countA_occ Loc.eq Loc.eq_dec elt
                           (map Config.loc
                                (Config.list
                                   (fun id : Names.ident => (conf_equi id))))
                           ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
                         (map Config.loc
                              (Config.list
                                 (fun id : Names.ident => (conf_equi id)))) <= 0)%nat by omega.
      apply le_not_gt in H0.
      contradiction.
    - exfalso; apply H; apply Heq.
  }
  specialize (H l).
  simpl in *.
  rewrite Config.list_spec, map_map in *.
  simpl.
  unfold Loc.eq in H.
  assert (Hdec := Spect.M.In_dec).
  unfold Spect.M.elt in *.
  specialize (Hdec l
                   (Spect.multiset (map
                                      (fun x : Names.ident => Config.loc (conf_equi x))
                                        Names.names))).
  destruct Hdec;
  simpl in *.
  rewrite H in Hf.
  lia.
  apply i.
 assert (n0' : ~ Spect.M.In l (snd (!! (conf_equi) Loc.origin))).
 simpl in *.
 rewrite Config.list_spec, map_map.
 simpl in *.
 apply n0.
 rewrite Spect.M.not_In in n0.
 unfold Spect.from_config, Config.map in *.
 simpl in *.
 rewrite Spect.multiset_spec in *.
 unfold apply_sim, trans in *; simpl in *.
 lia.
Qed.  

 


Definition m := 
    V2Z (r.(pgm) (spect_equi conf_equi (Good g))).

(** For each robot on conf_equi, the vision is the same *) 

Lemma same_Spectrum : forall g0,
    Spect.eq (spect_equi conf_equi (Good g)) (spect_equi conf_equi (Good g0)).
Proof.
  intros.
  split; simpl; try easy.
  unfold spect_equi, Spect.from_config.
  simpl.
  unfold Spect.M.eq.
  intro x.
  rewrite 2 Spect.multiset_spec.
  unfold Spect.from_config in *.
  unfold Config.map in *.
  assert (HndAg : SetoidList.NoDupA Loc.eq
                                    (map (fun x : Names.ident =>
                                            Config.loc (apply_sim (trans (loc_equi g)) (conf_equi x))) Names.names)).
  {
    apply (map_injective_NoDupA eq_equivalence Loc.eq_equiv).
    + intros a b Hab.
      rewrite Hab.
      reflexivity.
    + intros id1 id2 Hloc.
      destruct id1 as [g1|b1], id2 as [g2|b2]; try ImpByz b1; try ImpByz b2.
      unfold apply_sim,trans in *; simpl in *.
      destruct (Names.eq_dec (Good g1) (Good g2)).
      assumption.
      assert (Hg : g1 <> g2).
      { intuition.
        apply n0.
        now rewrite H.
      }
      generalize (unique_g_2 g Hg).
      intros Hu.
      destruct Hu.
      simpl in *;
        rewrite 2 Loc.add_comm with (y := (Loc.opp (loc_equi g)))
        in Hloc;
        apply Loc.add_reg_l in Hloc.
      now rewrite Hloc.
    + assert (Hnames := Names.names_NoDup).
      apply NoDupA_Leibniz in Hnames.
      assumption.
  }
  assert (Hkn : forall x, x mod Z.of_nat n = 0
                          -> x mod Z.of_nat (n / k) = 0).
  { intros.
    generalize k_sup_1; intros Hk.
    assert (Hk_div_n := k_div_n).
    rewrite Nat.mod_divides in Hk_div_n; try omega.
    destruct Hk_div_n.
    rewrite Nat.mul_comm in H0.
    rewrite H0 in *.
    rewrite Nat.div_mul in *; try lia.
    destruct x1.
    now rewrite Zdiv.Zmod_0_r.
    rewrite Nat2Z.inj_mul, Z.rem_mul_r in H.
    generalize Z_of_nat_complete; intros Haux.
    assert (Ha1 := Haux (x0 mod Z.of_nat (S x1))).
    assert (Ha2 := Haux ((x0 / Z.of_nat (S x1)) mod Z.of_nat k)).
    destruct Ha1.
    { now apply Zdiv.Z_mod_lt. }
    destruct Ha2.
    { apply Zdiv.Z_mod_lt. generalize k_sup_1; lia. }
    rewrite H1, H2 in H.
    assert (forall x y, 0 <= x -> 0 <= y -> x + y = 0 -> x = 0 /\ y = 0).
    { intros s t Hr Hs Hrs.
      omega. }
    apply H3 in H.
    destruct H; rewrite H1 in *; assumption.
    omega.
    rewrite <- Nat2Z.inj_mul.
    omega.
    assert ( (0 < S x1)%nat ) by omega.
    assert ( 0<Z.of_nat (S x1)).
    rewrite <- Nat2Z.inj_0.
    now apply inj_lt.
    omega.
    generalize k_sup_1; 
      lia.
  }
  simpl in *.
  assert (forall l elt, Spect.M.In elt (snd (!! (Config.map (apply_sim
                                                               (trans (loc_equi g)))
                                                            conf_equi) l)) ->
                        countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                              (Config.list
                                                                 (fun id : Names.ident =>
                                                                    apply_sim (trans (loc_equi g)) (conf_equi id)))) = 1%nat).
  {
    intros l elt Hspe.
    simpl in *.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                   (Config.list
                                                      (fun id : Names.ident =>
                                                         apply_sim (trans (loc_equi g)) (conf_equi id)))) > 1)%nat
            -> False).
    {
      intros Hgt.
      rewrite Config.list_spec, map_map in *.     
      rewrite (NoDupA_countA_occ' Loc.eq_dec) in HndAg.
      rewrite <- Spect.M.support_In in Hspe.
      unfold Spect.from_config in Hspe.
      unfold Config.map in Hspe.
      rewrite Spect.multiset_support in Hspe.
      specialize (HndAg elt Hspe).
      unfold apply_sim, trans in *; simpl in *.
      rewrite HndAg in Hgt.
      omega.
      apply Loc.eq_equiv.
    }
    rewrite <- Spect.M.support_In in Hspe.
    unfold Spect.from_config in Hspe.
    rewrite Spect.multiset_support in Hspe.
    unfold Config.map in Hspe.
    rewrite <- (countA_occ_pos Loc.eq_equiv Loc.eq_dec) in Hspe.
    destruct ( (countA_occ Loc.eq Loc.eq_dec elt
                           (map Config.loc
                                (Config.list
                                   (fun id : Names.ident =>
                                      apply_sim (trans (loc_equi g)) (conf_equi id))))
                           ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
                         (map Config.loc
                              (Config.list
                                 (fun id : Names.ident =>
                                    apply_sim (trans (loc_equi g))
                                              (conf_equi id)))) <= 0)%nat by omega.
      apply le_not_gt in H0.
      contradiction.
    - exfalso; apply H; apply Heq.
  }
  assert (forall l elt,
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                      (conf_equi (Good g)))))
                                                 conf_equi) l))
             <->
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                      (conf_equi (Good g0)))))
                                                 conf_equi) l))).
  {  intros l elt.
     do 2 rewrite Spect.from_config_In.
     assert (Hcc1 := conf1_1 g g0).
     destruct Hcc1 as (g2', Hcc1).
     assert (Hg_opp : forall g1 : Names.G, exists g': Names.G, Loc.eq (loc_equi g') (Loc.opp (loc_equi g1))).
     { intros.
       generalize conf1_new_2.
       intros.
       unfold Loc.eq, Veq, Loc.opp.
       rewrite <- loc_fin.
       repeat rewrite Z.mod_mod.
       specialize (H0 (((Z.of_nat MakeRing.n - V2Z (loc_equi g1))))).
         assert (((Z.of_nat MakeRing.n - V2Z (loc_equi g1)))
                   mod Z.of_nat (n / k) = 0).
         rewrite Zdiv.Zminus_mod.
         rewrite conf1_new_1.
         rewrite Hkn; try easy.
         rewrite Hkn; try easy.
         apply Z.mod_same.
         generalize n_sup_1; fold n; lia.
         specialize (H0 H1).
         unfold Loc.eq, Veq in H0; rewrite <- loc_fin, Z.mod_mod in H0.
         apply H0.
         generalize n_sup_1; lia.
         generalize n_sup_1; lia.
         generalize n_sup_1; lia.
     }
     
     assert (forall (g1 g2:Names.G), exists (g':Names.G), Loc.eq (loc_equi g') (Loc.add (loc_equi g1)
                                                                      (loc_equi g2))).
       { generalize conf1_new_2.
         intros.
         unfold Loc.eq, Veq, Loc.add.
         rewrite <- loc_fin.
         repeat rewrite Z.mod_mod.
         
         specialize (H0 (((V2Z (loc_equi g1) + V2Z (loc_equi g2))))).
         assert (((V2Z (loc_equi g1) + V2Z (loc_equi g2)))
                   mod Z.of_nat (n / k) = 0).
         rewrite Zdiv.Zplus_mod.
         rewrite 2 conf1_new_1.
         simpl; rewrite Z.mod_0_l.
         reflexivity.
         destruct k eqn : Hkg.
         generalize k_sup_1; lia.
         generalize k_inf_n, k_sup_1, k_div_n; intros ? ? Hk_div_n.
         rewrite Hkg in *.
         rewrite Nat.mod_divides, <-Hkg in Hk_div_n.
         destruct Hk_div_n.      
         rewrite H3, Nat.mul_comm.
         rewrite Hkg in *.
         rewrite Nat.div_mul.
         destruct x0.
         omega.
         rewrite <- Nat2Z.inj_0.
         intuition.
         apply Nat2Z.inj in H4.
         omega.
         omega.
         omega.
         specialize (H0 H1).
         unfold Loc.eq, Veq in H0; rewrite <- loc_fin, Z.mod_mod in H0.
         apply H0.
         generalize n_sup_1; lia.
         generalize n_sup_1; lia.
         generalize n_sup_1; lia.
       }
       split.
     + intros (gc1,Hc1).
       destruct gc1 as [g1| b] eqn : Hg; try ImpByz b.
       unfold Config.map, apply_sim, trans, conf_equi; simpl in *.
       destruct (H0 g1 g2').
       exists (Good x0).
       simpl.
       rewrite <- Hc1, H1.
       rewrite Hcc1.
       rewrite Loc.opp_distr_add, Loc.opp_opp.
       rewrite Loc.add_assoc, (Loc.add_comm (loc_equi g1)), <- Loc.add_assoc.
       now rewrite (Loc.add_comm).
     + assert (Hcc2 : Loc.eq (loc_equi g0)
                             (Loc.add (loc_equi g) (loc_equi g2'))).
       rewrite Hcc1.
       rewrite <- Loc.add_assoc.
       now rewrite Loc.add_opp', Loc.add_origin.
       intros (gc1,Hc1).
       destruct gc1 as [g1| b] eqn : Hg; try ImpByz b.
       unfold Config.map, apply_sim, trans, conf_equi; simpl in *.
       destruct (Hg_opp g2').
       destruct (H0 g1 x0).
       rewrite Hcc2 in Hc1.
       exists (Good x1).
       simpl.
       rewrite <- Hc1.
       rewrite H2, H1.
       now rewrite Loc.opp_distr_add, (Loc.add_comm (Loc.opp _) (Loc.opp _)),
       Loc.add_assoc.
  }
  assert (Ht_map : forall (x : Spect.M.elt) l, 
             Spect.M.In x (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                (conf_equi (Good g0)))))
                                        conf_equi) l))
             <-> (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                         (conf_equi (Good g0)))))
                                 conf_equi) l))[x] = 1%nat).
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
                                                      (apply_sim (trans ( (loc_equi g0))))
                                                      conf_equi x0)) Names.names)).
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
        apply (H1 g0 g1 g2).
        intuition.
        rewrite H4 in n0.
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
    rewrite <- Spect.M.support_In in Hsp_In.
    rewrite Spect.multiset_support in Hsp_In.
    assumption.
    intros.
    unfold Spect.from_config in *.
    unfold Spect.M.In.
    omega.
  }
  specialize (Ht_map x Loc.origin).
  destruct (Spect.M.In_dec x (snd (!! (Config.map (apply_sim
                                                (trans (Config.loc
                                                          (conf_equi (Good g)))))
                             conf_equi) Loc.origin))).
  + assert (i' : Spect.M.In x  (snd (!! (Config.map (apply_sim
                                                (trans (Config.loc
                                                          (conf_equi (Good g0)))))
                             conf_equi) Loc.origin))) by now rewrite <- H0.
    unfold Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    destruct Ht_map as (Ht1, Ht2).
    rewrite H, Ht1.
    reflexivity.
    apply i'.
    apply Loc.origin.
    apply i.
  + assert (n0' : ~ Spect.M.In x (snd (!! (Config.map (apply_sim
                                                (trans (Config.loc
                                                          (conf_equi (Good g0)))))
                             conf_equi) Loc.origin))) by now rewrite <- H0.
    rewrite Spect.M.not_In in n0.
    rewrite Spect.M.not_In in n0'.
    unfold Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.  
Qed.

(** Two configurations are equivalent if one is obtained by translating all the robots from the other configuration by the same number [k] of vertices. *)
Definition f_conf conf k : Config.t :=
  fun id =>
      match id with
      | Good g => {| Config.loc := Loc.add k (Config.loc (conf (Good g)));
                     Config.state := tt |}
                      
      | Byz b => conf (Byz b)
      end.

Instance f_conf_compat : Proper (Config.eq ==> Loc.eq ==> Config.eq) f_conf.
Proof.
  intros c1 c2 Hc k1 k2 Hk.
  unfold f_conf.
  unfold Config.eq.
  intros [g|b]; try ImpByz b.
  split; simpl in *.
  now rewrite Hk, (Hc (Good g)).
  reflexivity.
Qed.


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


Definition rconf_equi := round r da_equi conf_equi.

(** For each configuration [c], if [c] is equivalent to [conf_equi] as described before, 
     then the vision for each robot is the same in the two configurations [c] and [conf_equi].  *)
Lemma equiv_spectrum : forall conf g0,
      (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (conf_equi id))))
            ->
    Spect.eq (spect_equi conf (Good g0)) (spect_equi conf_equi (Good g0)).
Proof.
  intros conf g0 Hconf_equiv.
  split; try reflexivity; intros x.
  simpl in *.
  unfold Config.map in *.
  repeat rewrite Spect.multiset_spec in *.
  unfold apply_sim, trans; simpl.
  unfold equiv_conf, f_conf in *.
  destruct Hconf_equiv.
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
  assert (forall elt, Spect.M.In elt (snd (spect_equi conf (Good g0))) ->
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
      rewrite <- Spect.M.support_In in Hspe.
      unfold Spect.from_config in Hspe.
      unfold Config.map in Hspe.
      simpl in Hspe.
      rewrite Config.list_spec in Hspe.
      rewrite map_map in Hspe.
      simpl in *.
      rewrite Spect.multiset_support in Hspe.
      specialize (H0 elt Hspe).
      unfold apply_sim, trans in *; simpl in *.
      rewrite H0 in Hgt.
      omega.
      apply Loc.eq_equiv.
    }
    rewrite <- Spect.M.support_In in Hspe.
    unfold Spect.from_config in Hspe.
    simpl in Hspe.
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
             Spect.M.In elt (snd (spect_equi conf (Good g0)))
             <->
             Spect.M.In elt (snd (spect_equi conf_equi (Good g0)))).
  {  unfold apply_sim, trans;
       intros elt.
     unfold spect_equi.
     do 2 rewrite Spect.from_config_In.
     simpl in *.
     split.
     + intros (gc1,Hc1).
       destruct gc1 as [g1| b] eqn : Hg.
     - generalize (conf1_1 g1 g0); intros Hc11.
       destruct Hc11.
       exists (Good g1).
       simpl in *.
       rewrite <- Hc1.
       simpl in *.
       unfold Location.eq in *.
       rewrite (H (Good g0)), (H (Good g1)).
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
     unfold round.
     simpl in *.
     rewrite (H (Good g0)), (H (Good g1)).
       rewrite <- Loc.add_assoc;
       rewrite (Loc.opp_distr_add x0);
       rewrite (Loc.add_comm (loc_equi g1));
       rewrite Loc.add_assoc.
       rewrite Loc.add_assoc.
       rewrite (Loc.add_comm x0), <- (Loc.add_assoc _ x0),
       Loc.add_opp, Loc.add_origin.
       simpl.
       now rewrite Loc.add_comm.
  }
  assert (Ht_map : forall x : Spect.M.elt, 
             Spect.M.In x (snd (spect_equi conf_equi (Good g0)))
             <-> (snd (spect_equi conf_equi (Good g0)))[x] = 1%nat).
  { intros elt; split.
    intros Hsp_In.
    assert (Hsp_In' := Hsp_In).
    unfold Spect.from_config.
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
                                                      (apply_sim (trans ( (loc_equi g0))))
                                                      conf_equi x0)) Names.names)).
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
    rewrite <- Spect.M.support_In in Hsp_In.
    rewrite Spect.multiset_support in Hsp_In.
    assumption.
    intros.
    unfold Spect.from_config in *.
    unfold Spect.M.In.
    omega.
  }
  specialize (Ht_map x).
  destruct (Spect.M.In_dec x (snd (spect_equi conf (Good g0)))).
  + assert (i' : Spect.M.In x (snd (spect_equi conf_equi (Good g0)))) by now rewrite <- H2.
    unfold spect_equi, Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    destruct Ht_map as (Ht1, Ht2).
    rewrite H1. rewrite Ht1.
    reflexivity.
    apply i'.
    apply i.
  + assert (n0' : ~ Spect.M.In x (snd (spect_equi conf_equi (Good g0)))) by now rewrite <- H2.
    rewrite Spect.M.not_In in n0.
    rewrite Spect.M.not_In in n0'.
    unfold spect_equi, Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.
Qed.

(** The key idea is to prove that we can always make robots think that there are in the same configuration.

    So, in [conf_equi], if a robot moves, it can be in two direction, [Forward] or [Backward], and for each direction, all robots move in the same direction.
The configuration is then the same that before the movement. *)

(** **  First case: the robots move forward direction  **)

Section Move1.
  
  Hypothesis Hm : Loc.eq (Z2V m) (Z2V 1).

Lemma rconf_equi_simpl :
  let n_pos g := Loc.add (Z2V 1) (loc_equi g) in  
  Config.eq rconf_equi (fun id =>
                        match id with
                        | Good g =>
                          {| Config.loc := n_pos g;
                             Config.state := tt
                          |}
                        | Byz b => (conf_equi (Byz b))
                     end).
Proof.
  intros n_pos [g0|b]; try ImpByz b.  
  unfold rconf_equi, n_pos, round;
    repeat split; simpl in *;
  rewrite Loc.add_opp;
  unfold Loc.add.
  unfold m in Hm.
  rewrite (pgm_compat r _ _ (same_Spectrum g0)) in Hm.
  unfold spect_equi in *.
  simpl in *.
  unfold Loc.eq, Veq in *; rewrite <- loc_fin in *.
  rewrite Z.mod_mod in Hm;
  try rewrite Zdiv.Zplus_mod;
  try rewrite Hm;
  repeat rewrite <- loc_fin; repeat rewrite Z.mod_mod; 
  try rewrite Zdiv.Zplus_mod_idemp_r;
  try (generalize n_sup_1; fold n in *; lia);
  fold n in *.
Qed.


Definition Always_equiv (e : execution) : Prop :=
  Stream.forever (fun e1 => equiv_conf rconf_equi
                                        (Stream.hd e1)) e.
                                                                    
Definition Always_moving (e : execution) : Prop :=
  Stream.forever (fun e1 => ~Stopped e1) e.

    
(** An execution that is satisfying the predicate [Always_equiv]
   also satisfies [Always_moving]. *)


Lemma Always_moving_impl_not_WillStop : forall e,
    e = execute r demon_equi (Stream.hd e)
    -> Always_moving e -> ~ Will_stop e.
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

  

Lemma round_2_simplify_1 :
  forall conf,
         equiv_conf rconf_equi conf
    -> Config.eq
         (round r da_equi conf)
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
                let local_target : Loc.t := (r (Spect.from_config local_config (Config.loc (local_config (Good g))))) in
                let new_target :=
                    ((trans
                        (Config.loc
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Bijection.section)
                                                                  local_target in
                {| Config.loc := new_target;
                   Config.state := tt |}
              end).
Proof.
  intros conf Hconf_eq [g|b]; unfold round at 1; simpl in *; try ImpByz b.
  assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (conf_equi id))))).
  { destruct Hconf_eq.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, _);
      unfold f_conf in *.
    assert (Hrs := rconf_equi_simpl).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, _).
    rewrite Hls in Hl.
    simpl in *.
    rewrite Hl.
    now rewrite Loc.add_assoc, (Loc.add_comm x).
  }
  repeat split; simpl.
  destruct Hconf_eq.
  apply H.
Qed.

Lemma round1_move_g_1 : forall g0,
    ~ Loc.eq (Config.loc (round r da_equi rconf_equi (Good g0)))
      (Config.loc (rconf_equi (Good g0))).
Proof.
  intros g0.
  simpl in *.
  rewrite Loc.add_opp.
  generalize (equiv_spectrum rconf_equi g0).
  intros.
  assert ((exists k : Loc.t,
         forall id : Names.ident,
         Location.eq (Config.loc (rconf_equi id))
           (Loc.add k (Config.loc (conf_equi id))))).
  { unfold rconf_equi.
    unfold round.
    simpl in *.
    exists (Z2V m).
    intros[g'|b]; try ImpByz b.
    simpl.
    unfold m.
    rewrite <- fin_loc.
    rewrite (pgm_compat r _ _ (same_Spectrum g')).
    now rewrite Loc.add_opp.
  }
  specialize (H H0).
  rewrite Loc.add_opp in *.
  assert (Spect.eq (!! (Config.map (apply_sim (trans (Config.loc (rconf_equi (Good g0))))) rconf_equi) Loc.origin)
                   (!!
             (Config.map
                (apply_sim
                   (trans
                      (Graph.Loc.add
                         (r
                            (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
                               Loc.origin)) (loc_equi g0)))) rconf_equi) Loc.origin)).
  { simpl in *.
    split; try easy.
    rewrite Loc.add_opp in *.
    reflexivity.
  }
  rewrite <- H1, H.
  assert (Hmg : Loc.eq
            (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
               Loc.origin)) (Z2V m)).
  { unfold m. now rewrite <- fin_loc, (pgm_compat r _ _ (same_Spectrum g0)); simpl.
  }
  rewrite 2 (Loc.add_compat (Hmg) (reflexivity _)).
  rewrite Hm.
  assert (Hneq :=  @neq_a_1a (Loc.add (Z2V 1) (loc_equi g0))).
  unfold Loc.unit in Hneq.
  rewrite Z.mod_1_l in Hneq; try (generalize n_sup_1; lia).
  intro Hf; destruct Hneq; now symmetry.
Qed.

Lemma moving_no_stop : ~Stopped (((execute r demon_equi rconf_equi))).
Proof.
  intros Hs.
  generalize n_sup_1; intros Hn1.
  destruct Hs as (Hs,_).
  unfold Stall in Hs.
  generalize (round1_move_g_1).
  intros Hrmg1.
  simpl in Hs.
  specialize (Hs (Good g)).
  destruct Hs as (Hl, _).
  specialize (Hrmg1 g).
  destruct Hrmg1.
  apply (symmetry Hl).
Qed.  


Lemma round1_move_g_equiv : forall g0 conf,
    equiv_conf rconf_equi conf ->
    ~ Loc.eq (Config.loc (round r da_equi conf (Good g0)))
                        (Config.loc (conf (Good g0))).
Proof.
  intros g0 conf Hequiv.
  assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (conf_equi id))))).
  { destruct Hequiv.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, _);
    unfold f_conf in *.
    assert (Hrs := rconf_equi_simpl).
    simpl in Hrs.
    specialize (Hrs (Good g')).
    destruct Hrs as (Hls, _).
    rewrite Hls in Hl.
    simpl in *.
    rewrite Hl.
    now rewrite Loc.add_assoc, (Loc.add_comm x).
  }
  rewrite (round_2_simplify_1 Hequiv (Good g0)) in *.
  simpl.
  rewrite Loc.add_opp.
  assert (HSequiv := equiv_spectrum conf g0 Hequiv').
  unfold equiv_conf, f_conf in Hequiv.
  destruct Hequiv as (k, Hequiv).
  destruct (Hequiv (Good g0)) as (Hl0, _).
  intros Hf.
  rewrite HSequiv in Hf.
  simpl in *.
  assert (Hmg : Loc.eq
                  (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
                     Loc.origin)) (Z2V m)).
  { unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0)).
    rewrite <-fin_loc. now simpl. }
  rewrite (Loc.add_compat (Hmg) (reflexivity _)) in Hf.
  rewrite Hm in *.
  assert (Hn := @neq_a_1a (conf (Good g0))).
  unfold Loc.unit in Hn.
  rewrite Z.mod_1_l in Hn;
    try (generalize n_sup_1; lia).
  now destruct Hn.
Qed.

(** The robogram [r] will never stop under the demon [demon_equi] starting from
    a configuration equivalent to the initial configuration [conf_equi]. *)
Lemma moving_never_stop : forall conf,
    equiv_conf rconf_equi conf ->
    ~Stopped (execute r demon_equi conf).
Proof.
  intros conf Hconf_equiv Hstop.
  destruct Hstop as (Hstop, (Hsl, _)).
  unfold Stall in *.
  simpl in *.
  apply (round1_move_g_equiv g Hconf_equiv).
  specialize (Hstop (Good g)).
  symmetry.
  now destruct Hstop.
Qed.

Lemma Always_equiv_impl_Always_moving : forall e,
    e = execute r demon_equi (Stream.hd e)
    -> Always_equiv e -> Always_moving e.
Proof.
  cofix.
  intros e Heq_e HAequiv.
  constructor.
  - destruct HAequiv.
    unfold equiv_conf in H.
    destruct H.
    assert (Hcomp := execute_compat (reflexivity r) (reflexivity demon_equi) H). 
    rewrite Heq_e.
    rewrite Hcomp.
    apply moving_never_stop.
    rewrite rconf_equi_simpl in *.
    simpl in *.
    now exists (x).
  - apply Always_equiv_impl_Always_moving.
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


Lemma Always_equiv_conf1 : forall conf,
    equiv_conf rconf_equi conf
    -> Always_equiv (execute r demon_equi conf).
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
  + apply Always_equiv_conf1.
    simpl in *.
    assert (Hequiv' :
              (exists k, forall id,
                    Location.eq (Config.loc (conf id))
                                (Loc.add k (Config.loc (conf_equi id))))).
    { destruct H.
      exists (Loc.add (Z2V 1) x).
      intros [g0|b]; try ImpByz b.
      destruct (H (Good g0)) as (Hl, _).
      destruct (rconf_equi_simpl (Good g0)) as (Hrl,_).
      simpl in Hl.
      rewrite Hrl in Hl.
      simpl in *.
      rewrite Hl.
      now rewrite Loc.add_assoc, (Loc.add_comm x).
    }
    unfold equiv_conf.
    destruct H.
    exists (Loc.add x (Z2V 1)).
    rewrite round_2_simplify_1.
    intros id.
    simpl.
    destruct id; try ImpByz b.
    assert (Haux := equiv_spectrum).
    assert (Hmove_eq :=
              pgm_compat
                r
                _ (* (!!
                   (Config.map (apply_sim (trans (Config.loc (conf (Good g0)))))
                               (conf)))
                (!! (Config.map (apply_sim (trans (Config.loc (conf_equi (Good g0)))))
                                (conf_equi)))*) _
           (Haux conf g0 Hequiv')).
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
                       Loc.origin)) (Z2V m)).
    {  unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0)).
    rewrite <-fin_loc. now simpl. }
    simpl in *.
    repeat split; simpl; try repeat rewrite Loc.add_opp.
    rewrite (Loc.add_compat Hmg (reflexivity _)).
    rewrite Hmove_eq, Hmg.
    repeat rewrite Zdiv.Zplus_mod_idemp_l;
      repeat rewrite Zdiv.Zplus_mod_idemp_r;
    destruct (H (Good g0)) as (Hl, _);
    try rewrite Zdiv.Zplus_mod, Hl, <- Zdiv.Zplus_mod;
    try rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod;
    unfold f_conf;
    destruct (rconf_equi_simpl (Good g0)) as (Hl0, _);
    simpl in *;
    rewrite Hl, Loc.add_opp, (Loc.add_compat Hmg (reflexivity _));
    rewrite Hm;
    now rewrite Loc.add_assoc, (Loc.add_comm _ x).
    now exists x.
Qed.

(** The starting configuration satisfies the [Always_moving] predicate. *)

Lemma conf_equi_Always_moving : Always_moving (execute r demon_equi rconf_equi).
Proof.
  apply Always_equiv_impl_Always_moving.
  now simpl.
  apply Always_equiv_conf1.
  exists Loc.origin.
  unfold f_conf.
  intros [g|b]; try ImpByz b.
  now repeat split;simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
Qed.




(** The execution from the starting configuration will not stop. *)
Lemma never_stop : ~ Will_stop ((execute r demon_equi rconf_equi)).
Proof.
  apply Always_moving_impl_not_WillStop.
  cbn.
  reflexivity.
  apply conf_equi_Always_moving.
Qed.

(** Final theorem first part: if [k] divides [n], a robogram that decides to
    move in the configuration [conf_equi] cannot solve epxloration with stop. *)

Theorem no_exploration_moving : Z_of_nat (n mod k) = 0 -> ~ (Explores_and_stop r).
Proof.
  intros Hmod Habs.
  specialize (Habs demon_equi).
  unfold FullSolExplorationStop in *.
  destruct (Habs conf_equi) as (_, Hstop).
  apply equi_valid.
  apply equi_fair.
  destruct Hstop;
    try now apply never_stop.
  destruct H.
  unfold Stall in H.
  simpl in *.
  fold rconf_equi in H.
  rewrite rconf_equi_simpl in H.
  destruct (H (Good g)) as (Hl, _);
    simpl in *.
  symmetry in Hl.
  assert (Hn := @neq_a_1a (loc_equi g)).
  unfold Loc.unit in *; rewrite Z.mod_1_l in Hn; try (generalize n_sup_1; lia).
  now destruct Hn.
Save.

End Move1.

(** ** Second part: The robots never move. *)
Section Stop.

  Hypothesis Hm : Loc.eq (Z2V m) (Z2V 0).

  Lemma round_simplify_0 : forall conf,
      equiv_conf conf_equi conf -> 
      Config.eq (round r da_equi conf) conf.
  Proof.
    intros.
    unfold round.
    simpl in *.
    unfold lift_conf; simpl.
    intros [g0|b]; try ImpByz b.
    simpl in *.    
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
                       Loc.origin)) (Z2V m)).
    {  unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0)).
    rewrite <-fin_loc. now simpl. }
    rewrite Loc.add_opp, (equiv_spectrum conf g0);
      try rewrite (Loc.add_compat Hmg (reflexivity _));
      try rewrite Hm;
    assert (Loc.eq (Z2V 0) Loc.origin)
      by (unfold Loc.origin, Loc.eq, Veq; rewrite <- 2 loc_fin;
          repeat rewrite Z.mod_mod; generalize n_sup_1; fold n; try lia);
    try (now rewrite H0, Loc.add_comm, Loc.add_origin); destruct H.
    exists x.
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, _).
    rewrite Hl.
    now unfold f_conf; simpl.
  Qed.

  (** There is a position that will never be visited starting from [conf_equi]. *)
  Lemma NeverVisited_conf1 : forall e,
       eeq e (execute r demon_equi conf_equi) ->
       exists l, ~ Will_be_visited l e.
  Proof.
    intros e Heq_e.
    exists Loc.unit.
    intros Hl.
    induction Hl.
    + destruct H as (g0, Hvis).
      rewrite Heq_e in Hvis.
      simpl in Hvis.
      assert (Z.of_nat (n mod k) = 0) by (generalize k_div_n; fold n in *; lia).
      now apply (conf_equi_ne_unit H g0).
    + apply IHHl.
      rewrite Heq_e.
      cbn.
      symmetry.
      assert (Hequiv : equiv_conf conf_equi conf_equi).
      { exists Loc.origin.
        unfold f_conf.
        intros id.
        simpl in *.
        destruct id as [g|b]; try ImpByz b.
        repeat split; simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin;
          reflexivity.
      }
      rewrite (execute_compat (reflexivity r) (reflexivity demon_equi)
                            (symmetry (round_simplify_0 Hequiv))).
      constructor.
      simpl.
      now rewrite round_simplify_0.
      now rewrite round_simplify_0.
  Qed.

(** It is false that all position will be visited startion from [conf_equi]. *)
  Lemma never_visited :
      ~ (forall l : Loc.t, Will_be_visited l (execute r demon_equi conf_equi)).
  Proof.
    intros Hw.
    generalize (NeverVisited_conf1 (reflexivity (execute r demon_equi conf_equi))).
    intros Hfalse.
    destruct Hfalse as (g0, Hfalse).
    specialize (Hw g0).
    contradiction.
Qed.


 (** If [k] divides [n], a robogram that decides not to move in the
     configuration [conf_equi] cannot solve exploration with stop. *)
  Theorem no_exploration_idle : Z_of_nat (n mod k) = 0 -> ~ (Explores_and_stop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs demon_equi).
    destruct (Habs conf_equi) as (Hexpl, _).
    apply equi_valid.
    apply equi_fair.
    now apply never_visited.
  Save.

End Stop.

(** ** Third part: The robots move int the Backward direction. *)

Section Move_minus1.

  Hypothesis Hm : Loc.eq (Z2V m) (Loc.opp (Z2V 1)).

  Lemma round_2_conf_equi :
    Config.eq (round r da_equi conf_equi)
              (fun id =>
                 match id with
                 | Good g =>
                   {| Config.loc := Loc.add (Loc.opp (Z2V 1)) (loc_equi g);
                      Config.state := tt |}
                 | Byz b => (conf_equi (Byz b))
                 end).
  Proof.
    intros [g0|b]; try ImpByz b.
    unfold round.
    simpl in *.
    split; simpl; try easy. 
    assert (Hr := Loc.add_compat (pgm_compat r _ _ (symmetry (same_Spectrum g0)))
                                 (reflexivity  (loc_equi g0))).
    simpl in *.
    rewrite Loc.add_opp.
    unfold Loc.eq in *.
    rewrite Hr.
    unfold m in Hm.
    rewrite <- fin_loc in Hm.
    now rewrite Hm.
  Qed.

  Lemma round_2_2_simplify : Config.eq (f_conf (round r da_equi (conf_equi))
                                               (Loc.opp (Z2V 1)))
                                       (round r da_equi
                                              (round r da_equi conf_equi)).
  Proof.
    intros [g0|b]; try ImpByz b.
    rewrite round_2_conf_equi.
    unfold round.
    simpl in *; unfold lift_conf; simpl.
    assert (Location.eq (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans
                                       (Loc.add (Loc.opp (Z2V 1))
                                                (loc_equi g0))))
                                 (fun id : Names.ident =>
                                    match id with
                                    | Good g1 =>
                                       {|
                     Config.loc := Loc.add (Loc.opp (Z2V 1)) (loc_equi g1);
                     Config.state := tt |}
                 | Byz _ =>
                     {|
                     Config.loc := Loc.origin;
                     Config.state := tt |}
                                    end))
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (loc_equi g0))))))
                        (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans (Config.loc (conf_equi (Good g0)))))
                                 conf_equi)
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (loc_equi g0))))))
           ).
    { apply pgm_compat; try reflexivity.
      rewrite <- round_2_conf_equi.
      assert (Hc_eq :
                Config.eq
                  (Config.map
                     (apply_sim (trans (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))))
                     (round r da_equi conf_equi))
                  (Config.map
                     (apply_sim
                        (trans (Config.loc ((round r da_equi conf_equi)
                                              (Good g0)))))
                     (round r da_equi (conf_equi)))).
      { apply Config.map_compat; try easy.
        apply apply_sim_compat.
        assert (Location.eq (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                            (Config.loc
                               ((round r da_equi conf_equi) (Good g0))))
          by now rewrite (round_2_conf_equi (Good g0)).
        now rewrite H.
      }
      rewrite Hc_eq.
      rewrite Loc.add_opp.
      rewrite (equiv_spectrum ((round r da_equi conf_equi)) g0).
      reflexivity.
      exists (Loc.opp (Z2V 1)).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_conf_equi).
      specialize (Hr (Good g')).
      destruct Hr as (Hl, _).
      simpl in *.
      repeat split;simpl.
      now rewrite Hl.
    }
    destruct (Location.eq_dec
                (Loc.add
                   (r
                      (!!
                         (Config.map
                            (apply_sim
                               (trans (Loc.add (Loc.opp (Z2V 1))
                                               (loc_equi g0))))
                            (fun id : Names.ident =>
                               match id with
                               | Good g1 =>
                                 {|
                                   Config.loc := Loc.add 
                                                   (Loc.opp (Z2V 1)) 
                                                   (loc_equi g1);
                                   Config.state := tt |}
                               | Byz _ =>
                                 {|
                                   Config.loc := Loc.origin;
                                   Config.state := tt |}
                               end))
                      (Loc.add (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                               (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))))))
                   (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0)))
                (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0)))
      as [e0|nmove].
    - exfalso.
      rewrite H in e0.
      rewrite Loc.add_opp in e0; fold Loc.origin in e0;
        simpl in *.
      assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (loc_equi g0))) conf_equi)
                         Loc.origin)) (Z2V m)) by
      (unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0));
    rewrite <-fin_loc; now simpl).
      rewrite (Loc.add_compat Hmg (reflexivity _)), Hm in e0.
      apply Loc.add_reg_l in e0.
      assert (Hfalse : Location.eq
                         ((Loc.add (Loc.opp (Z2V 1)) (loc_equi g0)))
                         (Loc.add (Z2V 1) (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0)))).
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
                  (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                  (Loc.add
                     (r
                        (!!
                           (Config.map
                              (apply_sim (trans (Loc.add (Loc.opp (Z2V 1))
                                                         (loc_equi g0))))
                              (fun id : Names.ident =>
                                 match id with
                                 | Good g1 =>
                                   {|
                                     Config.loc := Loc.add (Loc.opp (Z2V 1))
                                                           (loc_equi g1);
                                     Config.state := tt |}
                                 | Byz _ =>
                                   {|
                                     Config.loc := Loc.origin;
                                     Config.state := tt |}
                                 end))
                        (Loc.add (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))
                                 (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))))))
                     (Loc.add (Loc.opp (Z2V 1)) (loc_equi g0))))
      ; try now destruct nmove.
      simpl in *.
      repeat split; simpl; 
        try rewrite H;
        assert (Hmg : Loc.eq
                        (r (!! (Config.map (apply_sim
                                              (trans (loc_equi g0))) conf_equi)
                           Loc.origin)) (Z2V m))
          by  (unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0));
    rewrite <-fin_loc; now simpl);
        try rewrite Loc.add_opp, (Loc.add_compat Hmg (reflexivity _)), Hm;
        try easy.
  Qed.
    
  Lemma round1_move_g_1_m : forall g0,
      ~ Loc.eq (Config.loc (round r da_equi (round r da_equi conf_equi) (Good g0)))
        (Config.loc ((round r da_equi conf_equi) (Good g0))).
  Proof.
    intros g0.
    rewrite <- (round_2_2_simplify (Good g0)).
    unfold f_conf.
    assert (Hr2c := round_2_conf_equi (Good g0)). 
    destruct Hr2c as (Hl2c, _).
    simpl in *.
    intros Hf.
    apply (@neq_a_1a (Loc.add
               (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi)
                  (Loc.add (loc_equi g0) (Loc.opp (loc_equi g0)))))
               (loc_equi g0))).
    rewrite <- Hf.
    unfold Loc.unit.
    rewrite Z.mod_1_l.
    rewrite (Loc.add_assoc (Z2V 1)), 2 Loc.add_opp, (Loc.add_comm (Loc.origin)),
    Loc.add_origin.
    now rewrite Loc.add_opp in *.
    generalize n_sup_1; lia.
  Qed.


  (* When starting from [conf_equi], the execution move at leat at the begining *)
  Lemma moving_no_stop_m : ~Stopped ((execute r demon_equi (round r da_equi conf_equi))).
  Proof.
    intros Hs.
    generalize n_sup_1; intros Hn1.
    destruct Hs as (Hs, _).
    unfold Stall in Hs.
    simpl in *.
    specialize (Hs (Good g)).
    destruct Hs as (Hl, _).
    simpl in *.
    now apply (round1_move_g_1_m g).
  Qed.
  
  Lemma round1_move_g_equiv_m : forall g0 conf,
      equiv_conf (round r da_equi (conf_equi)) conf ->
      ~ Loc.eq (Config.loc ((round r da_equi conf) (Good g0)))
        (Config.loc (conf (Good g0))).
  Proof.
    intros g0 conf Hequiv.
    assert (Hequiv' :
              (exists k, forall id,
                    Location.eq (Config.loc (conf id))
                                (Loc.add k (Config.loc (conf_equi id))))).
    { destruct Hequiv.
      exists (Loc.add (Loc.opp (Z2V 1)) x).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_conf_equi).
      specialize (Hr (Good g')).
      destruct Hr as (Hl, _).
      simpl in *.
      destruct (H (Good g')) as (Hl', _).
      rewrite Hl' in *.
      unfold f_conf in *.
      simpl in *.
      rewrite Hl in *.
      repeat split;simpl; 
        rewrite Loc.add_assoc, (Loc.add_comm x); easy.
    }
    assert (HSequiv := equiv_spectrum conf g0 Hequiv').
    simpl.
    rewrite Loc.add_opp.
    rewrite (equiv_spectrum conf g0 Hequiv').
    assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (loc_equi g0))) conf_equi)
                         Loc.origin)) (Z2V m))
        by (unfold m; rewrite (pgm_compat r _ _ (same_Spectrum g0));
    rewrite <-fin_loc; now simpl);
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

  (** On any configuration equivalent to the initial configuration [conf_equi],
      the robogram [r] is not stopped. *)
  Lemma moving_never_stop_m : forall conf,
      equiv_conf (round r da_equi (conf_equi)) conf ->
      ~Stopped (execute r demon_equi conf).
  Proof.
    intros conf Hconf_equiv Hstop.
    destruct Hstop as (Hstop, _).
    unfold Stall in *.
    simpl in *.
    apply (round1_move_g_equiv_m g Hconf_equiv).
    specialize (Hstop (Good g)).
    symmetry.
    apply Hstop.
  Qed.


  CoInductive Always_equiv_m (e : execution) : Prop :=
    CAE_m : equiv_conf (round r da_equi (conf_equi)) (Stream.hd e) ->
            Always_equiv_m ((Stream.tl e)) -> Always_equiv_m e.


  
  Lemma Always_equiv_impl_Always_moving_m : forall e,
      e = execute r demon_equi (Stream.hd e)
      -> Always_equiv_m e -> Always_moving e.
  Proof.
    cofix.
    intros e Heq_e HAequiv.
    constructor.
    - destruct HAequiv.
      unfold equiv_conf in H.
      destruct H.
      assert (Hcomp := execute_compat (reflexivity r) (reflexivity demon_equi) H). 
      rewrite Heq_e.
      rewrite Hcomp.
      apply moving_never_stop_m.
      unfold round.
      exists x.
      reflexivity.
    -  destruct HAequiv.
       apply Always_equiv_impl_Always_moving_m.
       + rewrite Heq_e at 1.
         rewrite execute_tail.
         simpl in *.
         rewrite Heq_e at 2.
         simpl in *.
         reflexivity.
       + assumption.
  Qed.


  Lemma Always_equiv_conf1_m : forall conf,
      equiv_conf (round r da_equi (conf_equi)) conf
      -> Always_equiv_m (execute r demon_equi conf).
  Proof.
    cofix.
    intros.
    constructor.
    + now simpl in *.
    + assert (Hequiv' :
                (exists k, forall id,
                      Location.eq (Config.loc (conf id))
                                  (Loc.add k (Config.loc (conf_equi id))))).
      { destruct H.
        exists (Loc.add (Loc.opp (Z2V 1)) x).
        intros [g'|b]; try ImpByz b.
        assert (Hr :=  round_2_conf_equi).
        specialize (Hr (Good g')).
        destruct Hr as (Hl, _).
        simpl in *.
        destruct (H (Good g')) as (Hl', _).
        rewrite Hl' in *.
        unfold f_conf in *.
        simpl in *.
        rewrite Hl in *.
        repeat split;simpl; 
          rewrite Loc.add_assoc, (Loc.add_comm x); easy.
      }
      apply Always_equiv_conf1_m.
      assert (Hr := round_2_conf_equi).
      simpl.
      destruct H.
      exists (Loc.add x (Z2V m)).
      simpl.
      intros id.
      simpl.
      destruct id; try ImpByz b.
      simpl.
      specialize (Hr (Good g0));
      destruct Hr as (Hl, _).
      assert (Haux := equiv_spectrum).
      split; simpl;try apply H.
      rewrite 2 Loc.add_opp, (Haux conf g0 Hequiv').
      simpl.
      apply (Loc.add_reg_l (Loc.opp (r (!! (Config.map (apply_sim (trans (loc_equi g0))) conf_equi) Loc.origin)))).
      rewrite Loc.add_assoc, Loc.add_opp'.
      rewrite (Loc.add_comm (Loc.add x _)), 3 Loc.add_assoc, Loc.add_opp'.
      do 2 rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
      destruct (H (Good g0)) as (Hlf, _);
        rewrite Hlf.
      simpl in *.
      unfold m; rewrite <-fin_loc.
      rewrite Loc.add_opp.
      simpl.
      rewrite (Loc.add_comm (loc_equi g0)).
      rewrite <- Loc.add_assoc.
      rewrite (Loc.add_comm (loc_equi g0)).
      now rewrite (pgm_compat r _ _ (same_Spectrum g0)).
  Qed.

  (** The starting configuration satisfies the [Always_moving] predicate. *)

  Lemma conf_equi_Always_moving_m : Always_moving (execute r demon_equi
                                                       (round r da_equi (conf_equi))).
  Proof.
    apply Always_equiv_impl_Always_moving_m.
    now simpl.
    apply Always_equiv_conf1_m.
    exists Loc.origin.
    unfold f_conf.
    intros [g|b]; try ImpByz b.
    now repeat split;simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
  Qed.

  (** The execution will never stop. *)
  Lemma never_stop_m : ~ Will_stop (execute r demon_equi (round r da_equi ((conf_equi)))).
  Proof.
    apply Always_moving_impl_not_WillStop.
    cbn.
    reflexivity.
    apply conf_equi_Always_moving_m.
  Qed.

  (** The exploration with stop is not possible if the robots moves backward. *)  
  Theorem no_exploration_moving_m : Z_of_nat (n mod k) = 0 -> ~ (Explores_and_stop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs demon_equi).
    destruct (Habs conf_equi) as (_, Hstop).
    apply equi_valid.
    apply equi_fair.
    destruct Hstop;
      try now apply never_stop_m.
    destruct H.
    unfold Stall in H.
    simpl in *.
    destruct (H (Good g)) as (Hl, _);
      unfold m in Hm; rewrite <- fin_loc in Hm.
    simpl in *.
    rewrite Loc.add_opp, Hm in Hl.
    assert (Hn := @neq_a_1a (Loc.add (Loc.opp (Z2V 1)) (loc_equi g))).
    unfold Loc.unit in *; rewrite Z.mod_1_l in Hn; try (generalize n_sup_1; lia).
    destruct Hn.
    rewrite Loc.add_assoc, Loc.add_opp, (Loc.add_comm Loc.origin), Loc.add_origin.
    now symmetry.
  Save.

  
End Move_minus1.

(** The only possible directions are the three used before. *)

Lemma ring_range :  forall g,
    let s := (!! (Config.map (apply_sim (trans (Config.loc (conf_equi (Good g))))) conf_equi) Loc.origin) in
    Loc.eq (r s) (Z2V 1)
    \/ Loc.eq (r s) (Z2V 0)
    \/ Loc.eq (r s) (Loc.opp (Z2V 1)).
Proof.
  intros Rconf s.
  assert (Hrange := pgm_range r s).
  simpl in Hrange.
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

(** ** Final theorem: if the number [k] of robot divides the number [n] of positions of the ring, then no robogram [r] can solve the exploration with stop. *)

Theorem no_exploration_k_divides_n : Z_of_nat (n mod k) = 0 -> ~ (Explores_and_stop r).
Proof.
  generalize no_exploration_idle, no_exploration_moving, no_exploration_moving_m,
  ring_range.
  intros.
  specialize (H2 g).
  unfold m, spect_equi in *; rewrite <-fin_loc in *.
  destruct H2.
  unfold Loc.eq, LocationA.eq, Veq, spect_equi in *.
  apply H0; try assumption;
    rewrite <- loc_fin, H2, Z.mod_mod; try generalize n_sup_1; lia.
  destruct H2; unfold Loc.eq, LocationA.eq, Veq in *.
  apply H; try rewrite <- loc_fin, H2, Z.mod_mod; simpl in *;
    try generalize n_sup_1; lia.
  now apply H1; try rewrite <- loc_fin, H2, Z.mod_mod; simpl in *;
    try generalize n_sup_1; lia.
Save.

         End DiscreteExploration.
