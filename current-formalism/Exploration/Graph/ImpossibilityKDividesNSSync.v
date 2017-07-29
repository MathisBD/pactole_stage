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

(** Ring Size*)

Definition n := MakeRing.n.

(** Number of Robots *)
Parameter k : nat.
Axiom kdn : (n mod k)%nat = 0%nat.
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

(** Defintion of the Configuration *)
Definition create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (Z2V (((Z_of_nat ((proj1_sig (Fin.to_nat f))*(n / k)))))) Loc.unit.


(** the starting configuration where a robots is on the origin, 
   and every other robot is at a distance of [x*(k/n)] where x is between 1 and k *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc :=  pos;
                             Config.info := tt |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.info := tt |}
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
  assert (Hkdn := kdn).
  rewrite <- Nat.div_exact in Hkdn.
  rewrite Hkdn at 2.
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



(** A position where a robot is in config1 divied [k/n] *)
Lemma conf1_new_1 : forall g0: Names.G, V2Z (create_conf1 g0) mod Z.of_nat (n/k) = 0.
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


(** if a position divides [n/k] then a robot is at this position in config1 *)
Lemma conf1_new_2 : forall loc, loc mod Z.of_nat (n / k) = 0 ->
                                exists g:Names.G,
                                  Loc.eq (create_conf1 g) (Z2V loc).
Proof.
  intros loc Hmod.
  intros.
  generalize kdn n_sup_1.
  fold n in *.
  intros Hkdn Hns1.
  unfold Names.G, Names.Gnames, Names.Internals.Gnames, Names.Internals.G, K.nG in *.
  destruct k eqn : Hkg.
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
    assert (Hmod1 :  Z.of_nat (n / k) <> 0).
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
        rewrite <- Nat.div_exact in Hkdn.
        rewrite Hkg, <- Hkdn.
        assumption.
        omega.
        omega.
      + assert (forall a, a mod Z.of_nat (n/k) = 0 -> (a mod n') mod Z.of_nat (n/k) = 0).
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


(** an Injection theorem about config1 *)
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
  assert (Hsol1 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g2) * (n / k)) * 1 < Z.of_nat n).
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
   assert (Hsol2 : 0 <= Z.of_nat (proj1_sig (Fin.to_nat g1) * (n / k)) * 1 < Z.of_nat n).
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
  assert ((0 < (n/k))%nat).
  apply Nat.div_str_pos.
  omega.
  unfold K.nG.
  omega.
Qed.

Parameter g : Names.G.


Variable r : DGF.robogram.

Lemma conf1_1 : forall idg g0: Names.G, exists g2:Names.G,
      Loc.eq (create_conf1 idg)
             (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g2))).
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


Import DGF.

(** Defintion of the demon *)
Definition da1 : demonic_action.
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
  
    
CoFixpoint bad_demon1 : demon := Stream.cons da1 bad_demon1.

Lemma bad_demon1_tail : 
    Stream.tl bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.
  
Lemma bad_demon1_head :
    Stream.hd bad_demon1 = da1.
Proof. reflexivity. Qed.
Theorem kFair_bad_demon : kFair 1 bad_demon1.
Proof.
cofix.
constructor; [| constructor].
* intros [g1 | b1] id2; try ImpByz b1.  apply kReset. simpl. discriminate.
* intros [g1 | b1] id2; try ImpByz b1. 
  apply kReset. simpl. discriminate. 
* simpl. assumption.
Qed.

(** fairness properties *)
Lemma Fair_demon : Fair bad_demon1.
Proof. apply (@kFair_Fair 1%nat). apply kFair_bad_demon. Qed.
                           
Lemma config1_ne_unit : Z_of_nat (n mod k) = 0 ->
      forall g:Names.G, ~ Loc.eq (create_conf1 g) Loc.unit.
Proof.
  intros Hmod g.
  generalize k_sup_1, k_inf_n, n_sup_1.
  intros.
  unfold Names.G, Names.Internals.G, K.nG in *.
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
  + unfold Loc.mul, Loc.unit in *;
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

(** Config1 is a valid conf *)
Lemma  ValidConfig1 : ValidStartingConf config1.
Proof.
  unfold ValidStartingConf.
  intros l' Hf.
  simpl in *.
  destruct Hf as (l, Hf).
  rewrite Spect.multiset_spec in Hf.
  assert (HndAg : SetoidList.NoDupA Loc.eq
                                    (map (fun x : Names.ident => Config.loc (config1 x))
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
    assert (Hkdn := kdn).
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
  assert (forall elt, Spect.M.In elt (snd (!! (config1) l)) ->
                        countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                              (Config.list
                                                                 config1)) = 1%nat).
  {

    intros elt Hspe.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map DefsE.Config.loc
                                                 (DefsE.Config.list
                                                    config1)) > 1)%nat
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
                                   (fun id : Names.ident => (config1 id))))
                           ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
                         (map Config.loc
                              (Config.list
                                 (fun id : Names.ident => (config1 id)))) <= 0)%nat by omega.
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
                                      (fun x : Names.ident => Config.loc (config1 x))
                                        Names.names))).
  destruct Hdec;
  simpl in *.
  rewrite H in Hf.
  lia.
  apply i.
 assert (n0' : ~ Spect.M.In l (snd (!! (config1) Loc.origin))).
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
    V2Z (r.(pgm)
        (!! (Config.map
               (apply_sim (trans (Config.loc (config1 (Good g)))))
               (config1)) Loc.origin)).

(** For each robot on config1, the vision is the same*) 

Lemma spectre_forall_g : forall g0,
    Spect.eq (!! (Config.map
                    (apply_sim (trans (Config.loc (config1 (Good g)))))
                    (config1)) Loc.origin)
             (!! (Config.map
                    (apply_sim (trans (Config.loc (config1 (Good g0)))))
                    (config1)) Loc.origin).
Proof.
  intros.
  simpl; split; try easy.
  unfold Spect.from_config.
  simpl.
  unfold Spect.M.eq.
  intro x.
  rewrite 2 Spect.multiset_spec.
  unfold Spect.from_config in *.
  unfold Config.map in *.
  assert (HndAg : SetoidList.NoDupA Loc.eq
                                    (map (fun x : Names.ident =>
                                            Config.loc (apply_sim (trans (create_conf1 g)) (config1 x))) Names.names)).
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
        rewrite 2 Loc.add_comm with (y := (Loc.opp (create_conf1 g)))
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
    assert (Hkdn := kdn).
    rewrite Nat.mod_divides in Hkdn; try omega.
    destruct Hkdn.
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
                                                               (trans (create_conf1 g)))
                                                            config1) l)) ->
                        countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                              (Config.list
                                                                 (fun id : Names.ident =>
                                                                    apply_sim (trans (create_conf1 g)) (config1 id)))) = 1%nat).
  {
    intros l elt Hspe.
    simpl in *.
    assert ((countA_occ Loc.eq Loc.eq_dec elt (map Config.loc
                                                   (Config.list
                                                      (fun id : Names.ident =>
                                                         apply_sim (trans (create_conf1 g)) (config1 id)))) > 1)%nat
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
                                      apply_sim (trans (create_conf1 g)) (config1 id))))
                           ?= 1)%nat) eqn : Heq; try rewrite <- nat_compare_lt in *;
      try rewrite <- nat_compare_gt in *;
      try apply nat_compare_eq in Heq.
    - assumption.
    - assert (countA_occ Loc.eq Loc.eq_dec elt
                         (map Config.loc
                              (Config.list
                                 (fun id : Names.ident =>
                                    apply_sim (trans (create_conf1 g))
                                              (config1 id)))) <= 0)%nat by omega.
      apply le_not_gt in H0.
      contradiction.
    - exfalso; apply H; apply Heq.
  }
  assert (forall l elt,
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                      (config1 (Good g)))))
                                                 config1) l))
             <->
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                      (config1 (Good g0)))))
                                                 config1) l))).
  {  intros l elt.
     do 2 rewrite Spect.from_config_In.
     assert (Hcc1 := conf1_1 g g0).
     destruct Hcc1 as (g2', Hcc1).
     assert (Hg_opp : forall g1 : Names.G, exists g': Names.G, Loc.eq (create_conf1 g') (Loc.opp (create_conf1 g1))).
     { intros.
       generalize conf1_new_2.
       intros.
       unfold Loc.eq, Veq, Loc.opp.
       rewrite <- loc_fin.
       repeat rewrite Z.mod_mod.
       specialize (H0 (((Z.of_nat MakeRing.n - V2Z (create_conf1 g1))))).
         assert (((Z.of_nat MakeRing.n - V2Z (create_conf1 g1)))
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
     
     assert (forall (g1 g2:Names.G), exists (g':Names.G), Loc.eq (create_conf1 g') (Loc.add (create_conf1 g1)
                                                                      (create_conf1 g2))).
       { generalize conf1_new_2.
         intros.
         unfold Loc.eq, Veq, Loc.add.
         rewrite <- loc_fin.
         repeat rewrite Z.mod_mod.
         
         specialize (H0 (((V2Z (create_conf1 g1) + V2Z (create_conf1 g2))))).
         assert (((V2Z (create_conf1 g1) + V2Z (create_conf1 g2)))
                   mod Z.of_nat (n / k) = 0).
         rewrite Zdiv.Zplus_mod.
         rewrite 2 conf1_new_1.
         simpl; rewrite Z.mod_0_l.
         reflexivity.
         destruct k eqn : Hkg.
         generalize k_sup_1; lia.
         generalize k_inf_n, k_sup_1, kdn; intros ? ? Hkdn.
         rewrite Hkg in *.
         rewrite Nat.mod_divides, <-Hkg in Hkdn.
         destruct Hkdn.      
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
       unfold Config.map, apply_sim, trans, config1; simpl in *.
       destruct (H0 g1 g2').
       exists (Good x0).
       simpl.
       rewrite <- Hc1, H1.
       rewrite Hcc1.
       rewrite Loc.opp_distr_add, Loc.opp_opp.
       rewrite Loc.add_assoc, (Loc.add_comm (create_conf1 g1)), <- Loc.add_assoc.
       now rewrite (Loc.add_comm).
     + assert (Hcc2 : Loc.eq (create_conf1 g0)
                             (Loc.add (create_conf1 g) (create_conf1 g2'))).
       rewrite Hcc1.
       rewrite <- Loc.add_assoc.
       now rewrite Loc.add_opp', Loc.add_origin.
       intros (gc1,Hc1).
       destruct gc1 as [g1| b] eqn : Hg; try ImpByz b.
       unfold Config.map, apply_sim, trans, config1; simpl in *.
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
                                                                (config1 (Good g0)))))
                                        config1) l))
             <-> (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                         (config1 (Good g0)))))
                                 config1) l))[x] = 1%nat).
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
                                                          (config1 (Good g)))))
                             config1) Loc.origin))).
  + assert (i' : Spect.M.In x  (snd (!! (Config.map (apply_sim
                                                (trans (Config.loc
                                                          (config1 (Good g0)))))
                             config1) Loc.origin))) by now rewrite <- H0.
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
                                                          (config1 (Good g0)))))
                             config1) Loc.origin))) by now rewrite <- H0.
    rewrite Spect.M.not_In in n0.
    rewrite Spect.M.not_In in n0'.
    unfold Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.  
Qed.

(** Two configuration are equivalent if all robots of the first are moved of the same [k] numbur to have the second. *)
Definition f_conf conf k : Config.t :=
  fun id =>
      match id with
      | Good g => {| Config.loc := Loc.add k (Config.loc (conf (Good g)));
                     Config.info := tt |}
                      
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


Definition rconfig1 := round r da1 config1.

(** for each configuration [c], if c is equivalent to [config1] as described before, 
     then the vision for each robot is the same in the two configuration [c] and [config1].  *)
Lemma config1_Spectre_Equiv : forall conf l g0,
      (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id))))
            ->
    Spect.eq (!! (Config.map (apply_sim
                                (trans (Config.loc (conf (Good g0)))))
                             (conf)) l)
             (!! (Config.map (apply_sim
                                (trans (Config.loc (config1 (Good g0)))))
                             ( config1)) l).
Proof.
  intros conf l g0 Hconf_equiv.
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
  assert (forall elt, Spect.M.In elt (snd (!! (Config.map (apply_sim
                                                      (trans (Config.loc
                                                                   (conf (Good g0)))))
                             conf) l)) ->
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
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                               (conf (Good g0)))))
                                          conf) l))
             <->
             Spect.M.In elt (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                               (config1 (Good g0)))))
                                          config1) l))).
  {  unfold apply_sim, trans;
     intros elt.
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
       rewrite (Loc.add_comm (create_conf1 g1));
       rewrite Loc.add_assoc.
       rewrite Loc.add_assoc.
       rewrite (Loc.add_comm x0), <- (Loc.add_assoc _ x0),
       Loc.add_opp, Loc.add_origin.
       simpl.
       now rewrite Loc.add_comm.
  }
  assert (Ht_map : forall x : Spect.M.elt, 
             Spect.M.In x (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                                (config1 (Good g0)))))
                                        config1) l))
             <-> (snd (!! (Config.map (apply_sim (trans (Config.loc
                                                         (config1 (Good g0)))))
                                 config1) l))[x] = 1%nat).
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
    rewrite <- Spect.M.support_In in Hsp_In.
    rewrite Spect.multiset_support in Hsp_In.
    assumption.
    intros.
    unfold Spect.from_config in *.
    unfold Spect.M.In.
    omega.
  }
  specialize (Ht_map x).
  destruct (Spect.M.In_dec x (snd (!! (Config.map (apply_sim
                                              (trans (Config.loc
                                                           (conf (Good g0)))))
                             conf) l))).
  + assert (i' : Spect.M.In x (snd (!!
                               (Config.map (apply_sim (trans (Config.loc
                                                                   (config1 (Good g0)))))
                                           config1) l))) by now rewrite <- H2.
    unfold Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    destruct Ht_map as (Ht1, Ht2).
    rewrite H1, Ht1.
    reflexivity.
    apply i'.
    apply i.
  + assert (n0' : ~ Spect.M.In x (snd (!!
                                  (Config.map (apply_sim (trans
                                                            (Config.loc
                                                               (config1 (Good g0)))))
                                              config1) l))) by now rewrite <- H2.
    rewrite Spect.M.not_In in n0.
    rewrite Spect.M.not_In in n0'.
    unfold Spect.from_config, Config.map in *.
    simpl in *.
    rewrite Spect.multiset_spec in *.
    unfold apply_sim, trans in *; simpl in *.
    rewrite n0, n0'.
    reflexivity.
Qed.

(** The key idea is to prove that we can always make robots think that there are in the same configuration.

    So, in [conf1], if a robot moves, it can be in two direction, Forward or Backward, and for each direction, all robots move in the same direction.
the configuration is then the same that before the movement.
    If it does not, it either move to the Backward direction, and it is approximatively the same proof, or it de  *)

(** **  First case: the robots move to the forward direction  **)

Section Move1.
  
  Hypothesis Hm : Loc.eq (Z2V m) (Z2V 1).

Lemma rconfig1_simpl :
  let n_pos g := Loc.add (Z2V 1) (create_conf1 g) in  
  Config.eq rconfig1 (fun id =>
                        match id with
                        | Good g =>
                          {| Config.loc := n_pos g;
                             Config.info := tt
                          |}
                        | Byz b => (config1 (Byz b))
                     end).
Proof.
  intros n_pos [g0|b]; try ImpByz b.  
  unfold rconfig1, n_pos, round;
    repeat split; simpl in *;
  rewrite Loc.add_opp;
  unfold Loc.add.
  unfold m in Hm.
  rewrite (pgm_compat r _ _ (spectre_forall_g g0)) in Hm.
  simpl in *.
  unfold Loc.eq, Veq in *; rewrite <- loc_fin in *.
  rewrite Z.mod_mod in Hm;
  try rewrite Zdiv.Zplus_mod;
  try rewrite Hm;
  repeat rewrite <- loc_fin; repeat rewrite Z.mod_mod; 
  try rewrite Zdiv.Zplus_mod_idemp_r;
  try (generalize n_sup_1; fold n in *; lia);
  fold n in *;
  reflexivity.
Qed.


Definition AlwaysEquiv (e : execution) : Prop :=
  Stream.forever (fun e1 => equiv_conf rconfig1
                                        (Stream.hd e1)) e.
                                                                    
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.forever (fun e1 => ~Stopped e1) e.

    
(** An execution that is satisfing the predicate [AlwaysEquiv]
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
                let local_target : Loc.t := (r (Spect.from_config local_config (Config.loc (local_config (Good g))))) in
                let new_target :=
                    ((trans
                        (Config.loc
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Bijection.section)
                                                                  local_target in
                {| Config.loc := new_target;
                   Config.info := tt |}
              end).
Proof.
  intros conf Hconf_eq [g|b]; unfold round at 1; simpl in *; try ImpByz b.
  assert (Hequiv' : (exists k, forall id,
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id))))).
  { destruct Hconf_eq.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, _);
      unfold f_conf in *.
    assert (Hrs := rconfig1_simpl).
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
    ~ Loc.eq (Config.loc (round r da1 rconfig1 (Good g0)))
      (Config.loc (rconfig1 (Good g0))).
Proof.
  intros g0.
  simpl in *.
  rewrite Loc.add_opp.
  generalize (config1_Spectre_Equiv rconfig1 Loc.origin g0).
  intros.
  assert ((exists k : Loc.t,
         forall id : Names.ident,
         Location.eq (Config.loc (rconfig1 id))
           (Loc.add k (Config.loc (config1 id))))).
  { unfold rconfig1.
    unfold round.
    simpl in *.
    exists (Z2V m).
    intros[g'|b]; try ImpByz b.
    simpl.
    unfold m.
    rewrite <- fin_loc.
    rewrite (pgm_compat r _ _ (spectre_forall_g g')).
    now rewrite Loc.add_opp.
  }
  specialize (H H0).
  rewrite Loc.add_opp in *.
  assert (Spect.eq (!! (Config.map (apply_sim (trans (Config.loc (rconfig1 (Good g0))))) rconfig1) Loc.origin)
                   (!!
             (Config.map
                (apply_sim
                   (trans
                      (Graph.Loc.add
                         (r
                            (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
                               Loc.origin)) (create_conf1 g0)))) rconfig1) Loc.origin)).
  { simpl in *.
    split; try easy.
    rewrite Loc.add_opp in *.
    reflexivity.
  }
  rewrite <- H1, H.
  assert (Hmg : Loc.eq
            (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
               Loc.origin)) (Z2V m)).
  { unfold m. now rewrite <- fin_loc, (pgm_compat r _ _ (spectre_forall_g g0)); simpl.
  }
  rewrite 2 (Loc.add_compat (Hmg) (reflexivity _)).
  rewrite Hm.
  assert (Hneq :=  @neq_a_1a (Loc.add (Z2V 1) (create_conf1 g0))).
  unfold Loc.unit in Hneq.
  rewrite Z.mod_1_l in Hneq; try (generalize n_sup_1; lia).
  intro Hf; destruct Hneq; now symmetry.
Qed.

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
  destruct Hs as (Hl, _).
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
            Location.eq (Config.loc (conf id)) (Loc.add k (Config.loc (config1 id))))).
  { destruct Hequiv.
    exists (Loc.add (Z2V 1) x).
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, _);
    unfold f_conf in *.
    assert (Hrs := rconfig1_simpl).
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
  assert (HSequiv := config1_Spectre_Equiv conf (Loc.origin) g0 Hequiv').
  unfold equiv_conf, f_conf in Hequiv.
  destruct Hequiv as (k, Hequiv).
  destruct (Hequiv (Good g0)) as (Hl0, _).
  intros Hf.
  rewrite HSequiv in Hf.
  simpl in *.
  assert (Hmg : Loc.eq
                  (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
                     Loc.origin)) (Z2V m)).
  { unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0)).
    rewrite <-fin_loc. now simpl. }
  rewrite (Loc.add_compat (Hmg) (reflexivity _)) in Hf.
  rewrite Hm in *.
  assert (Hn := @neq_a_1a (conf (Good g0))).
  unfold Loc.unit in Hn.
  rewrite Z.mod_1_l in Hn;
    try (generalize n_sup_1; lia).
  now destruct Hn.
Qed.

(** any configuration equivalent to the starting one will not stop if executed with 
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
                                (Loc.add k (Config.loc (config1 id))))).
    { destruct H.
      exists (Loc.add (Z2V 1) x).
      intros [g0|b]; try ImpByz b.
      destruct (H (Good g0)) as (Hl, _).
      destruct (rconfig1_simpl (Good g0)) as (Hrl,_).
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
    assert (Haux := config1_Spectre_Equiv).
    assert (Hmove_eq :=
              pgm_compat
                r
                _ (* (!!
                   (Config.map (apply_sim (trans (Config.loc (conf (Good g0)))))
                               (conf)))
                (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g0)))))
                                (config1)))*) _
           (Haux conf Loc.origin g0 Hequiv')).
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
                       Loc.origin)) (Z2V m)).
    {  unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0)).
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
    destruct (rconfig1_simpl (Good g0)) as (Hl0, _);
    simpl in *;
    rewrite Hl, Loc.add_opp, (Loc.add_compat Hmg (reflexivity _));
    rewrite Hm;
    now rewrite Loc.add_assoc, (Loc.add_comm _ x).
    now exists x.
Qed.

(** the starting configuration respect the [AlwaysMoving] predicate *)

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




(** The starting configuration will not stop *)
Lemma never_stop : ~ Will_stop ((execute r bad_demon1 rconfig1)).
Proof.
  apply AlwaysMoving_impl_not_WillStop.
  cbn.
  reflexivity.
  apply config1_AlwaysMoving.
Qed.

  (** final theorem first part: if we move, In the asynchronous model, and if k 
     divide n, then the exploration with stop of a n-node ring is not possible. *)

Theorem no_exploration_moving : Z_of_nat (n mod k) = 0 -> ~ (ValidStartingConfSolExplorationStop r).
Proof.
  intros Hmod Habs.
  specialize (Habs bad_demon1).
  unfold FullSolExplorationStop in *.
  destruct (Habs config1) as (_, Hstop).
  apply ValidConfig1.
  apply Fair_demon.
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

(** ** second part: The robots never move. *)
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
    intros [g0|b]; try ImpByz b.
    simpl in *.    
    assert (Hmg : Loc.eq
                    (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
                       Loc.origin)) (Z2V m)).
    {  unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0)).
    rewrite <-fin_loc. now simpl. }
    rewrite Loc.add_opp, (config1_Spectre_Equiv conf Loc.origin g0);
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

  (** exists a position that will never be visited starting from [config1]*)
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
      assert (Z.of_nat (n mod k) = 0) by (generalize kdn; fold n in *; lia).
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

(** it is false that all position will be visited startion from [config1] *)
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


 (** The exploration is not posiible if the robots never move.*) 
  Theorem no_exploration_idle : Z_of_nat (n mod k) = 0 -> ~ (ValidStartingConfSolExplorationStop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    destruct (Habs config1) as (Hexpl, _).
    apply ValidConfig1.
    apply Fair_demon.
    now apply never_visited.
  Save.

End Stop.

(** ** Third part: The robots move int the Backward direction. *)

Section Move_minus1.

  Hypothesis Hm : Loc.eq (Z2V m) (Loc.opp (Z2V 1)).

  Lemma round_2_config1 :
    Config.eq (round r da1 config1)
              (fun id =>
                 match id with
                 | Good g =>
                   {| Config.loc := Loc.add (Loc.opp (Z2V 1)) (create_conf1 g);
                      Config.info := tt |}
                 | Byz b => (config1 (Byz b))
                 end).
  Proof.
    intros [g0|b]; try ImpByz b.
    unfold round.
    simpl in *.
    split; simpl; try easy. 
    assert (Hr := Loc.add_compat (pgm_compat r _ _ (symmetry (spectre_forall_g g0)))
                                 (reflexivity  (create_conf1 g0))).
    simpl in *.
    rewrite Loc.add_opp.
    unfold Loc.eq in *.
    rewrite Hr.
    unfold m in Hm.
    rewrite <- fin_loc in Hm.
    now rewrite Hm.
  Qed.

  Lemma round_2_2_simplify : Config.eq (f_conf (round r da1 (config1))
                                               (Loc.opp (Z2V 1)))
                                       (round r da1
                                              (round r da1 config1)).
  Proof.
    intros [g0|b]; try ImpByz b.
    rewrite round_2_config1.
    unfold round.
    simpl in *; unfold lift_conf; simpl.
    assert (Location.eq (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans
                                       (Loc.add (Loc.opp (Z2V 1))
                                                (create_conf1 g0))))
                                 (fun id : Names.ident =>
                                    match id with
                                    | Good g1 =>
                                       {|
                     Config.loc := Loc.add (Loc.opp (Z2V 1)) (create_conf1 g1);
                     Config.info := tt |}
                 | Byz _ =>
                     {|
                     Config.loc := Loc.origin;
                     Config.info := tt |}
                                    end))
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (create_conf1 g0))))))
                        (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans (Config.loc (config1 (Good g0)))))
                                 config1)
                           (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                                    (Loc.opp (Loc.add (Loc.opp (Z2V 1))
                                                      (create_conf1 g0))))))
           ).
    { apply pgm_compat; try reflexivity.
      rewrite <- round_2_config1.
      assert (Hc_eq :
                Config.eq
                  (Config.map
                     (apply_sim (trans (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))))
                     (round r da1 config1))
                  (Config.map
                     (apply_sim
                        (trans (Config.loc ((round r da1 config1)
                                              (Good g0)))))
                     (round r da1 (config1)))).
      { apply Config.map_compat; try easy.
        apply apply_sim_compat.
        assert (Location.eq (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                            (Config.loc
                               ((round r da1 config1) (Good g0))))
          by now rewrite (round_2_config1 (Good g0)).
        now rewrite H.
      }
      rewrite Hc_eq.
      rewrite Loc.add_opp.
      rewrite (config1_Spectre_Equiv ((round r da1 config1)) Loc.origin g0).
      reflexivity.
      exists (Loc.opp (Z2V 1)).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_config1).
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
                                               (create_conf1 g0))))
                            (fun id : Names.ident =>
                               match id with
                               | Good g1 =>
                                 {|
                                   Config.loc := Loc.add 
                                                   (Loc.opp (Z2V 1)) 
                                                   (create_conf1 g1);
                                   Config.info := tt |}
                               | Byz _ =>
                                 {|
                                   Config.loc := Loc.origin;
                                   Config.info := tt |}
                               end))
                      (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                               (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))))))
                   (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0)))
                (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0)))
      as [e0|nmove].
    - exfalso.
      rewrite H in e0.
      rewrite Loc.add_opp in e0; fold Loc.origin in e0;
        simpl in *.
      assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g0))) config1)
                         Loc.origin)) (Z2V m)) by
      (unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0));
    rewrite <-fin_loc; now simpl).
      rewrite (Loc.add_compat Hmg (reflexivity _)), Hm in e0.
      apply Loc.add_reg_l in e0.
      assert (Hfalse : Location.eq
                         ((Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0)))
                         (Loc.add (Z2V 1) (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0)))).
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
                  (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                  (Loc.add
                     (r
                        (!!
                           (Config.map
                              (apply_sim (trans (Loc.add (Loc.opp (Z2V 1))
                                                         (create_conf1 g0))))
                              (fun id : Names.ident =>
                                 match id with
                                 | Good g1 =>
                                   {|
                                     Config.loc := Loc.add (Loc.opp (Z2V 1))
                                                           (create_conf1 g1);
                                     Config.info := tt |}
                                 | Byz _ =>
                                   {|
                                     Config.loc := Loc.origin;
                                     Config.info := tt |}
                                 end))
                        (Loc.add (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))
                                 (Loc.opp (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))))))
                     (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g0))))
      ; try now destruct nmove.
      simpl in *.
      repeat split; simpl; 
        try rewrite H;
        assert (Hmg : Loc.eq
                        (r (!! (Config.map (apply_sim
                                              (trans (create_conf1 g0))) config1)
                           Loc.origin)) (Z2V m))
          by  (unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0));
    rewrite <-fin_loc; now simpl);
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
    destruct Hr2c as (Hl2c, _).
    simpl in *.
    intros Hf.
    apply (@neq_a_1a (Loc.add
               (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1)
                  (Loc.add (create_conf1 g0) (Loc.opp (create_conf1 g0)))))
               (create_conf1 g0))).
    rewrite <- Hf.
    unfold Loc.unit.
    rewrite Z.mod_1_l.
    rewrite (Loc.add_assoc (Z2V 1)), 2 Loc.add_opp, (Loc.add_comm (Loc.origin)),
    Loc.add_origin.
    now rewrite Loc.add_opp in *.
    generalize n_sup_1; lia.
  Qed.


  (** When starting from [config1], the execution move at leat at the begining *)
  Lemma moving_no_stop_m : ~Stopped ((execute r bad_demon1 (round r da1 config1))).
  Proof.
    intros Hs.
    generalize n_sup_1; intros Hn1.
    destruct Hs as (Hs, _).
    unfold stop_now in Hs.
    simpl in *.
    specialize (Hs (Good g)).
    destruct Hs as (Hl, _).
    simpl in *.
    now apply (round1_move_g_1_m g).
  Qed.
  
  Lemma round1_move_g_equiv_m : forall g0 conf,
      equiv_conf (round r da1 (config1)) conf ->
      ~ Loc.eq (Config.loc ((round r da1 conf) (Good g0)))
        (Config.loc (conf (Good g0))).
  Proof.
    intros g0 conf Hequiv.
    assert (Hequiv' :
              (exists k, forall id,
                    Location.eq (Config.loc (conf id))
                                (Loc.add k (Config.loc (config1 id))))).
    { destruct Hequiv.
      exists (Loc.add (Loc.opp (Z2V 1)) x).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_config1).
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
    assert (HSequiv := config1_Spectre_Equiv conf Loc.origin g0 Hequiv').
    simpl.
    rewrite Loc.add_opp.
    rewrite (config1_Spectre_Equiv conf Loc.origin g0 Hequiv').
    assert (Hmg : Loc.eq
                      (r (!! (Config.map (apply_sim
                                            (trans (create_conf1 g0))) config1)
                         Loc.origin)) (Z2V m))
        by (unfold m; rewrite (pgm_compat r _ _ (spectre_forall_g g0));
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

  (** any configuration equivalent to the starting one will not stop if executed with 
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
                                  (Loc.add k (Config.loc (config1 id))))).
      { destruct H.
        exists (Loc.add (Loc.opp (Z2V 1)) x).
        intros [g'|b]; try ImpByz b.
        assert (Hr :=  round_2_config1).
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
      destruct Hr as (Hl, _).
      assert (Haux := config1_Spectre_Equiv).
      split; simpl;try apply H.
      rewrite 2 Loc.add_opp, (Haux conf Loc.origin g0 Hequiv').
      simpl.
      apply (Loc.add_reg_l (Loc.opp (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1) Loc.origin)))).
      rewrite Loc.add_assoc, Loc.add_opp'.
      rewrite (Loc.add_comm (Loc.add x _)), 3 Loc.add_assoc, Loc.add_opp'.
      do 2 rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
      destruct (H (Good g0)) as (Hlf, _);
        rewrite Hlf.
      simpl in *.
      unfold m; rewrite <-fin_loc.
      rewrite Loc.add_opp.
      simpl.
      rewrite (Loc.add_comm (create_conf1 g0)).
      rewrite <- Loc.add_assoc.
      rewrite (Loc.add_comm (create_conf1 g0)).
      now rewrite (pgm_compat r _ _ (spectre_forall_g g0)).
  Qed.

  (** the starting configuration respect the [AlwaysMoving] predicate *)

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

  (** starting from the configuration after a round on [config1], the execution will never stop *)
  Lemma never_stop_m : ~ Will_stop (execute r bad_demon1 (round r da1 ((config1)))).
  Proof.
    apply AlwaysMoving_impl_not_WillStop.
    cbn.
    reflexivity.
    apply config1_AlwaysMoving_m.
  Qed.

(** The exploration with stop is not possible if the robots moves backward. *)  
  Theorem no_exploration_moving_m : Z_of_nat (n mod k) = 0 -> ~ (ValidStartingConfSolExplorationStop r).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    destruct (Habs config1) as (_, Hstop).
    apply ValidConfig1.
    apply Fair_demon.
    destruct Hstop;
      try now apply never_stop_m.
    destruct H.
    unfold stop_now in H.
    simpl in *.
    destruct (H (Good g)) as (Hl, _);
      unfold m in Hm; rewrite <- fin_loc in Hm.
    simpl in *.
    rewrite Loc.add_opp, Hm in Hl.
    assert (Hn := @neq_a_1a (Loc.add (Loc.opp (Z2V 1)) (create_conf1 g))).
    unfold Loc.unit in *; rewrite Z.mod_1_l in Hn; try (generalize n_sup_1; lia).
    destruct Hn.
    rewrite Loc.add_assoc, Loc.add_opp, (Loc.add_comm Loc.origin), Loc.add_origin.
    now symmetry.
  Save.

  
End Move_minus1.

(** The only possible directions are the three used before. *)

Lemma range_r :  forall g,
    let s := (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g))))) config1) Loc.origin) in
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

(** ** Finale theorem: if the nuber of robot [k] divides the number of position on the ring [n], then the exploration with stop cannot be performed, and this, for any robogram [r]. *)

Theorem no_exploration : Z_of_nat (n mod k) = 0 -> ~ (ValidStartingConfSolExplorationStop r).
Proof.
  generalize no_exploration_idle, no_exploration_moving, no_exploration_moving_m,
  range_r.
  intros.
  specialize (H2 g).
  unfold m in *; rewrite <-fin_loc in *.
  destruct H2.
  unfold Loc.eq, LocationA.eq, Veq in *.
  apply H0; try assumption;
    rewrite <- loc_fin, H2, Z.mod_mod; try generalize n_sup_1; lia.
  destruct H2; unfold Loc.eq, LocationA.eq, Veq in *.
  apply H; try rewrite <- loc_fin, H2, Z.mod_mod; simpl in *;
    try generalize n_sup_1; lia.
  now apply H1; try rewrite <- loc_fin, H2, Z.mod_mod; simpl in *;
    try generalize n_sup_1; lia.
Save.

         End DiscreteExploration.
