(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain, R. Pelle                  *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

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

Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.

Definition translation_hyp := Sim.translation (translation_hypothesis).
(*Hypothesis translation_hypothesis : 
      forall v x y, Loc.dist (Loc.add x v) (Loc.add y v) = Loc.dist x y. *)

Instance translation_hyp_compat : Proper (Loc.eq ==> Sim.eq) translation_hyp.
Proof. intros l1 l2 Hl x y Hxy. simpl. now rewrite Hxy, Hl. Qed.

Ltac Ldec_full :=
  match goal with
    | |- context[Loc.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Loc.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

(* As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_conf {A} (conf : Names.G -> A) : Names.ident -> A := fun id =>
  match id with
    | Good g => conf g
    | Byz b => Fin.case0 _ b
  end.

CoInductive Always_forbidden (e : execution) : Prop :=
  CAF : forbidden (execution_head e) ->
        Always_forbidden (execution_tail e) -> Always_forbidden e.

Lemma Always_forbidden_compat_lemma : forall e1 e2, eeq e1 e2 -> Always_forbidden e1 -> Always_forbidden e2.
Proof.
coinduction diff.
- rewrite <- H. now destruct H0.
- destruct H. apply (diff _ _ H1). now destruct H0.
Qed.

Instance Always_forbidden_compat : Proper (eeq ==> iff) Always_forbidden.
Proof.
intros e1 e2 He; split; intro.
- now apply (Always_forbidden_compat_lemma He).
- now apply (Always_forbidden_compat_lemma (symmetry He)).
Qed.

Section ExplorationKDivedesN.
Open Scope Z_scope.

(* Fin.t k c'est l'ensemble de 1 à k.*)
Fixpoint Fint_to_nat (k:nat) (f:Fin.t k): nat :=
  match f with
  | @Fin.F1 _ => 0%nat
  | @Fin.FS n' f' => S (Fint_to_nat f')
  end.

(* Lemma test : forall k g, (0 < Fint_to_nat (@Fin.FS k g))%nat. *)
(* Proof. *)
(*   intros. *)
(*   destruct g. *)
(*   simpl in *. *)
(*   omega. *)
(* Qed. *)
  
(*Lemma Fin_0 : forall k (g: Fin.t (S k)), Fint_to_nat g = O -> g = @Fin.F1 k.
Proof.
  intros.
(* Fin.F1: forall n : nat, Fin.t (S n)
   Fin.FS: forall n : nat, Fin.t n -> Fin.t (S n) *)
  replace 0%nat with (Fint_to_nat (@Fin.F1 (S k))) in H.
  f_equal.
  case g.
  Fin.FS_inj
  assert (Hg := Fin.to_nat g).
  assert (Hf1 := Fin.to_nat (@Fin.F1 k)).
  destruct Hg.
  destruct Hf1.
  destruct k.
  assert (x = x0).
  omega.
  assert (x = O).
  omega.
  
  assert (Hp : proj1_sig Hg = proj1_sig (Fin.to_nat (@Fin.F1 k))).
  unfold Fin.to_nat.
  simpl in *.
  unfold proj1_sig.
  destruct k.
  simpl in *.
  destruct H'.
  intros.
  case g.
  inversion g.
  Focus 2.
  destruct g.
  set (n := S k) in *.
  assert (Hn := refl_equal n).
  unfold n at 2 in Hn.
  clearbody n.
  dependent inversion g.
  destruct k.
  destruct g.
Qed.*)


Lemma Fint_to_nat_inj : forall k (g1 g2 : Fin.t k) ,
    Fint_to_nat g1 = Fint_to_nat g2 -> g1 = g2.
Proof.
  intros k g1 g2 Hg.
  unfold Names.G, Names.Internals.G in *.
(*  dependent inversion g2.
  
  simpl in *.
  case g2.
  inversion Hg.
  inversion g2.
  destruct g2.
  simpl in *.
  assert (Heq0 : forall k (g : Fin.t (S k)), Fint_to_nat g = O -> g = Fin.F1).
  { intros.
    destruct g.

  } 
    inversion g2.
  Focus 2.
  dependent inversion g2.
  simpl in *.

Qed.*)
Admitted.
  
Definition create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (((Z_of_nat ((Fint_to_nat f)*(n / kG))))) Loc.unit.

Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := Loc.add Loc.unit pos |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
            end.

Lemma conf1_aux:
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
    
Lemma conf1_new_1 : forall g0: Names.G, (create_conf1 g0) mod Z.of_nat (n/kG) = 0. 
Proof.
  intros g0.
  unfold create_conf1.
  apply conf1_aux.
Qed.


Lemma conf_aux : forall m k, (1 < k)%nat -> (m < k)%nat ->
                             exists g: Fin.t k, Fint_to_nat g = m.
Proof.
  intros m.
  (* generalize k_sup_1; intros Hk1. *)
  induction m.
  intros.
  unfold Fint_to_nat.
  destruct k.
  omega.
  exists Fin.F1.
  reflexivity.
  intros.
  destruct k eqn : Hk.
  omega.
  destruct n0.
  omega.  
  destruct n0.
  destruct m.
  exists (Fin.FS Fin.F1).
  now simpl.
  omega.
  destruct (IHm (S (S n0))).
  omega.
  omega.
  exists (Fin.FS x).
  simpl.
  omega.
Qed.



Lemma conf_aux' : forall k (g: Fin.t k), 
                                         exists m, (m < k)%nat /\ Fint_to_nat g = m.
Proof.
  intros k g.
  induction g.
  simpl in *.
  exists O; omega.
  simpl in *.
  destruct n0.
  destruct IHg.
  omega.
  destruct IHg.
  exists (S x).
  split;
  omega.
Qed.

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


(* Lemma conf1_mult : forall g1 g2, Loc.eq (create_conf1 g1) (create_conf1 g2) -> False. *)

    
Definition loc_add k rconfig :=
  let new_pos := Loc.add k (Config.loc rconfig) in
  {| Config.loc := new_pos;
     Config.robot_info := {| Config.source := new_pos; Config.target := Loc.add new_pos new_pos|} |}.

Definition config2 := Config.map (loc_add Loc.unit) config1.


Lemma loceq_to_confeq : forall conf1 conf2,
(forall id, Loc.eq (Config.loc (conf1 id)) (conf1 id).(Config.robot_info).(Config.source)) ->
(forall id, Loc.eq (Config.loc (conf1 id)) (conf1 id).(Config.robot_info).(Config.target)) ->
(forall id,Loc.eq (Config.loc (conf2 id)) (conf2 id).(Config.robot_info).(Config.source)) ->
(forall id,Loc.eq (Config.loc (conf2 id)) (conf2 id).(Config.robot_info).(Config.target)) ->
(forall id,Loc.eq (Config.loc (conf1 id)) (Config.loc (conf2 id))) -> 
Config.eq conf1 conf2.
Proof.
intros conf1 conf2 Hls1 Hlt1 Hls2 Hlt2 Hll. unfold Config.eq, Config.eq_RobotConf, Config.Info_eq.
intros id.
specialize (Hll id). specialize (Hlt1 id). specialize (Hls1 id).
specialize (Hlt2 id). specialize (Hls2 id).
rewrite <- Hls1, <- Hls2.
rewrite <- Hlt1, <- Hlt2.
split. assumption. split; assumption.
Qed.

Definition rc_map (f : Loc.t -> Loc.t) (rc: Config.RobotConf) : Config.RobotConf := 
{| Config.loc := f (Config.loc rc);
   Config.robot_info := {| Config.source := f (Config.source (Config.robot_info rc));
                           Config.target := f (Config.target (Config.robot_info rc)) |} |}.

Instance rc_map_compat : Proper ((Loc.eq ==> Loc.eq) ==> Config.eq_RobotConf ==> Config.eq_RobotConf) rc_map.
Proof.
intros f1 f2 Hf r1 r2 Hr. unfold Config.eq_RobotConf, Config.Info_eq, rc_map.
split; simpl.  destruct Hr as (Hloc, Hinfo).
unfold Loc.eq, Ddef.eq, eq. rewrite (Hf (Config.loc r1)(Config.loc r2)).
reflexivity. assumption.
split; simpl; destruct Hr as (Hloc, (Hs,Ht)).
unfold Loc.eq, Ddef.eq, eq.
rewrite (Hf (Config.source (Config.robot_info r1))(Config.source (Config.robot_info r2))).
reflexivity. assumption.
unfold Loc.eq, Ddef.eq, eq.
rewrite (Hf (Config.target (Config.robot_info r1))(Config.target (Config.robot_info r2))).
reflexivity. assumption.
Qed.


Lemma conf1_inf_n : forall g:Names.G,
    (Z.of_nat (Fint_to_nat g * (n / kG)) * 1) < Z.of_nat n.
Proof.
  intros.
  unfold Names.G, Names.Internals.G in *.
  assert (Hf := Fin.to_nat g).
  destruct Hf.
  generalize kdn; intros  Hkdn.
  rewrite <- Nat.div_exact in Hkdn.
  unfold K.nG in *.
  rewrite Hkdn at 2.
  generalize  (conf_aux' g).
  intros (m0 , (Hm, Hm')).
  rewrite Hm'.
  rewrite Z.mul_1_r.
  rewrite <- Nat2Z.inj_lt.
  apply mult_lt_compat_r.
  omega.
  generalize k_sup_1, k_inf_n; intros.
  apply Nat.div_str_pos.
  omega.
  generalize k_sup_1; omega.
Qed.
  
Lemma unique_g : forall g1 g2,
               g1 <> g2 -> Loc.eq (Config.loc (config1 (Good g1)))
                                  (Config.loc (config1 (Good g2))) -> False.
Proof.
  intros.
  unfold config1, Loc.eq in H0.
  simpl in *.
  unfold create_conf1 in H0.
  unfold Loc.mul, Loc.unit, def.n in H0.
  assert (Fint_to_nat g1 = Fint_to_nat g2).
  do 2 rewrite Z.mod_mod in H0.
  generalize (conf1_inf_n g1), (conf1_inf_n g2).
  intros.
  do 2 rewrite Z.mod_small in H0; try omega.
  do 2 rewrite Z.mul_1_r in H0.
  apply Nat2Z.inj in H0.
  rewrite Nat.mul_cancel_r in H0.
  assumption.
  assert ((0 < (n/kG))%nat).
  generalize k_sup_1, k_inf_n; intros.
  apply Nat.div_str_pos.
  omega.
  omega.
  generalize n_sup_1; omega.
  generalize n_sup_1; omega.
  generalize n_sup_1; omega.
  intuition.
  generalize (conf_aux' g1).
  apply Fint_to_nat_inj in H1.
  auto.  
Qed.

Parameter g : Names.G.


Variable r : robogram.
Definition move := r (!! config1).

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Lemma conf1_1 : forall idg: Names.G, exists g2:Names.G,
      Loc.eq (create_conf1 idg)
             (Loc.add (create_conf1 g) (Loc.opp (create_conf1 g2))).
Proof.                                                                    
  intros.
  generalize conf1_new_1, k_sup_1, k_inf_n; intros Hc1n Hks1 Hkin.
  unfold Loc.eq.
  assert (Hc_idg := Hc1n idg).
  assert (Hc_g := Hc1n g).
  assert (Hnkg0 : Z.of_nat (n / kG) <> 0).
  assert (H0n : (0 < n/kG)%nat).
  apply Nat.div_str_pos.
  omega.
  omega.
  generalize conf1_new_2; intros Hc1n2.
  unfold Loc.add, Loc.opp, def.n.
  set (n0 := Z.of_nat n).
  specialize (Hc1n2 (create_conf1 g - create_conf1 idg)).
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

Lemma spect_rotation : Spect.eq (!! config1) (!! (Config.map (apply_sim (trans (create_conf1 g))) config1)).
Proof.
(* unfold Spect.multiset. *)
(* unfold Spect.eq. *)
(* intros X. *)
  unfold apply_sim, trans; simpl in *.
  generalize Spect.from_config_In, conf1_1, Spect.pos_in_config.
  intros HSfcI Hconf1_1 HSpic.
  assert (Htrue : forall x:Spect.elt, Spect.In x (!!config1)
              <-> Spect.In x (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))).
  { unfold apply_sim, trans; simpl in *.
    intros x. do 2 rewrite HSfcI.
    split.
    + intros (gc1,Hc1).
      destruct gc1 as [g1| b] eqn : Hg.
      - specialize (Hconf1_1 g1).
        destruct Hconf1_1.
        exists (Good x0).
        simpl in *.
        rewrite <- Hc1, H.
        reflexivity.
      - assert (Hfalse := Names.Bnames_length).
        assert (Hfalse' := Names.In_Bnames b).
        unfold Names.Bnames, K.nB in *.
        apply length_0 in Hfalse.
        rewrite Hfalse in Hfalse'.
        apply in_nil in Hfalse'.
        now exfalso.
    + intros (gc1,Hc1).
      destruct gc1 as [g1| b] eqn : Hg.
      - simpl in *.
        assert (H':= Hconf1_1 g1).
        destruct H'.
        rewrite H in Hc1.
        unfold Loc.add, Loc.opp, def.n in Hc1.
        set (cc1 := create_conf1 g) in Hc1.
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
      - assert (Hfalse := Names.Bnames_length).
        assert (Hfalse' := Names.In_Bnames b).
        unfold Names.Bnames, K.nB in *.
        apply length_0 in Hfalse.
        rewrite Hfalse in Hfalse'.
        apply in_nil in Hfalse'.
        now exfalso.
  }
  apply Spect.elements_injective.
  simpl in *.
  unfold Spect.eq_pair.
  assert (Ht : forall x : Spect.elt,
             Spect.In x (!! config1) <-> (!! config1)[x] = 1%nat).
  { intros x; split; intros Hsp.
    assert (Hsp' := Hsp).
    (* rewrite HSfcI in Hsp. *)
    (* destruct Hsp. *)
    unfold Spect.from_config.
    (* unfold Spect.multiset. *)
    generalize unique_g.
    intros.
    rewrite Spect.multiset_spec. 
    rewrite Config.list_spec.
    rewrite map_map.
    assert (HNoDup_map : NoDup (map (fun x0 : Names.ident => Config.loc (config1 x0)) Names.names)).
    { apply Injective_map_NoDup.
      intros id1 id2 Heq.
      destruct (Names.eq_dec id1 id2).
      assumption.
      exfalso.
      destruct id1 eqn : Hid1,
      id2 eqn : Hid2.
      apply (H g0 g1).
      intuition.
      rewrite H0 in n0.
      auto.
      now rewrite Heq.
      assert (Hfalse := Names.Bnames_length).
        assert (Hfalse' := Names.In_Bnames b).
        unfold Names.Bnames, K.nB in *.
        apply length_0 in Hfalse.
        rewrite Hfalse in Hfalse'.
        apply in_nil in Hfalse'.
        now exfalso.
        assert (Hfalse := Names.Bnames_length).
        assert (Hfalse' := Names.In_Bnames b).
        unfold Names.Bnames, K.nB in *.
        apply length_0 in Hfalse.
        rewrite Hfalse in Hfalse'.
        apply in_nil in Hfalse'.
        now exfalso.
        assert (Hfalse := Names.Bnames_length).
        assert (Hfalse' := Names.In_Bnames b).
        unfold Names.Bnames, K.nB in *.
        apply length_0 in Hfalse.
        rewrite Hfalse in Hfalse'.
        apply in_nil in Hfalse'.
        now exfalso.
        apply Names.names_NoDup.
    }
    assert (HNoDup_map' := HNoDup_map).
    rewrite NoDup_count_occ' in HNoDup_map.
    unfold Spect.from_config in Hsp.
    unfold Config.map in Hsp.
    rewrite Config.list_spec in Hsp.
    rewrite map_map in Hsp.
    assert (Hdec_conf1 : forall g1 g2,
               {Config.loc (config1 (Good g1)) = Config.loc (config1 (Good g2))}
                + {Config.loc (config1 (Good g1)) <> Config.loc (config1 (Good g2))}).
    { 
      intros.
      destruct (Loc.eq_dec (Config.loc (config1 (Good g1)))
               (Config.loc (config1 (Good g2))));
        unfold Loc.eq in *;
        simpl in *;
        unfold create_conf1, Loc.mul, Loc.unit, def.n in *.
      do 2 rewrite Z.mod_mod in e.
      auto.
      generalize n_sup_1; omega.
      generalize n_sup_1; omega.
      generalize n_sup_1; omega.
      do 2 rewrite Z.mod_mod in n0.
      auto.
      generalize n_sup_1; omega.
      generalize n_sup_1; omega.
      generalize n_sup_1; omega.
    }
    assert (Hcount : count_occ Z.eq_dec
               (map (fun x1 : Names.ident => Config.loc (config1 x1)) Names.names)
                   x = 1%nat).
    apply HNoDup_map.
    simpl in *.
    rewrite <- Spect.support_In in Hsp.
    rewrite Spect.multiset_support in Hsp.
    rewrite SetoidList.InA_alt in Hsp.
    destruct Hsp as (x', (Heq, Hsp)).
    assert (forall l1 l2,
           In l1 (map (fun x : Names.ident => Config.loc (config1 x)) Names.names) ->
           In l2 (map (fun x : Names.ident => Config.loc (config1 x)) Names.names) ->
           Loc.eq l1 l2 -> l1 = l2).
    { 
      intros l1 l2 Hl1 Hl2 Hleq.
      induction (map (fun x : Names.ident => Config.loc (config1 x)) Names.names).
      exfalso; apply in_nil in Hl1; assumption.
      apply in_inv in Hl2.
      apply in_inv in Hl1.
      destruct Hl1,Hl2.
      Focus 4.
      apply IHl.
      rewrite NoDup_cons_iff in HNoDup_map'.
      destruct HNoDup_map' as (_, Hl).
      assumption.
      rewrite NoDup_cons_iff in HNoDup_map'.
      destruct HNoDup_map' as (_, Hl).
      rewrite NoDup_count_occ' in Hl.
      intros.
      specialize (Hl x0 H2).
      apply Hl;
      assumption.
      assumption.
      assumption.
      rewrite <- H0; assumption.
      apply NoDup_cons_iff in HNoDup_map'.
      destruct l.
      apply in_nil in H1.
      now exfalso.
      destruct HNoDup_map'.
      apply not_in_cons in H2.
      rewrite H0 in *.



      assert (forall elt,
               In elt (map (fun x0 : Names.ident => Config.loc (config1 x0))
                           Names.names) ->
               0 <= elt < Z.of_nat n).
    { intros elt HSelt.
      rewrite in_map_iff in HSelt.
      destruct HSelt as (x0, (Helt,_)).
      destruct x0 as [g0 | b0].
      unfold config1 in Helt.
      simpl in Helt.
      unfold create_conf1, Loc.mul, Loc.unit, def.n in Helt.
      rewrite <- Helt.
      rewrite Z.mod_small.
      split.
      omega.
      apply conf1_inf_n.
      split; try omega; try apply conf1_inf_n.
      assert (Hfalse := Names.Bnames_length).
      assert (Hfalse' := Names.In_Bnames b0).
      unfold Names.Bnames, K.nB in *.
      apply length_0 in Hfalse.
      rewrite Hfalse in Hfalse'.
      apply in_nil in Hfalse'.
      now exfalso.
    }
    assert (forall elt,
               Spect.In elt (!! config1) ->
               0 <= elt < Z.of_nat n).
    { intros elt Helt.
      unfold Spect.elt in *.
      unfold Spect.from_config in Helt.
      
      rewrite Spect.multiset_spec in Helt. 
    rewrite Config.list_spec.

      unfold Loc.eq, def.n in Heq.
    rewrite Z.mod_small with (a := x') in Heq.
    rewrite Z.mod_small in Heq.
    rewrite Heq; assumption.
    apply H0.
    assumption.
    rewrite Heq.
    apply Zdiv.Z_mod_lt.
    generalize n_sup_1; omega.
    split.
    
    (* Spect.from_elements_In *)

    inversion n0.
      simpl in *.
    revert Hsp.
    revert x.
    
    rewrite <- NoDup_count_occ'.
    cut (Logic.eq (fun x0 : Names.ident =>
         Config.loc
           match x0 with
           | Good g0 =>
               {|
               Config.loc := create_conf1 g0;
               Config.robot_info := {|
                                    Config.source := create_conf1 g0;
                                    Config.target := Loc.add Loc.unit
                                                       (create_conf1 g0) |} |}
           | Byz _ =>
               {|
               Config.loc := Loc.origin;
               Config.robot_info := {|
                                    Config.source := Loc.origin;
                                    Config.target := Loc.origin |} |}
           end)
              (fun x0 : Names.ident =>
                 match x0 with
                 | Good g0 => create_conf1 g0
                 | Byz _ => Loc.origin
                 end)).
    + intros.
      rewrite H0.
      simpl in *.
      destruct Names.names eqn : Hname.
      assert (Ht := Names.names_length).
      unfold K.nB, K.nG in Ht.
      simpl in *.
      rewrite Hname in Ht.
      simpl in *.
      generalize k_sup_1; omega.
      simpl in *.
      destruct i eqn : Hid.
      destruct (Loc.eq_dec (create_conf1 g0) x) eqn : Heq.
      specialize (H g0).
      generalize Names.names_NoDup.
      intros Hnd.
      assert (Hle : forall g', In (Good g') l -> g' <> g0).
      { intros.
        apply Hnd.
      unfold NoDup in Hnd.
      rewrite H.
    rewrite <-Spect.multiset_In in Hsp.
    clear HSfcI Hconf1_1 HSpic Htrue.
    unfold Spect.from_config in *.
    destruct (Config.list config1) eqn : Hlc.
    + simpl in *.
      unfold Spect.multiset in *.
      simpl in *.
      now apply Spect.In_empty in Hsp.
    + apply Spect.multiset_app. (* forall loc,   *)
      unfold Spect.multiset.
      unfold Spect.M.from_elements.
      destruct x.
    admit.
Admitted.

Section Move1.

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

(** **  First case: the robots exchange their positions  **)




Section Move1.

Hypothesis Hmove : move = 1.

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
     simpl in *.
     replace (Z.of_nat (n / kG + Fint_to_nat g0 * (n / kG)) * 1) with (Z.of_nat (n / kG + Fint_to_nat g0 * (n / kG))) by omega.
     replace (Z.of_nat (n / kG + Fint_to_nat g0 * (n / kG))) with ((Z.of_nat (1 * (n / kG) + Fint_to_nat g0 * (n / kG)))).
     rewrite <- Nat.mul_add_distr_r.
     rewrite Zdiv.mod_Zmod in Hmod; try omega.
     rewrite Zdiv.Zmod_divides in *; try omega.
     rewrite Z.mod_mod.
     destruct Hmod.
     rewrite Nat2Z.inj_mul, Nat2Z.inj_add, Zdiv.div_Zdiv; try omega.
     rewrite H2 in *.
     replace (Z.of_nat kG * x ) with (x * Z.of_nat kG) by intuition.
     rewrite Zdiv.Z_div_mult_full.
     replace (x * Z.of_nat kG) with (Z.of_nat kG * x) by intuition.
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
     rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Zdiv.div_Zdiv; try omega.
     replace (Z.of_nat 1 * (Z.of_nat n / Z.of_nat kG)) with (Z.of_nat n / Z.of_nat kG).
     rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Zdiv.div_Zdiv; try omega.
     assert (1 = Z.of_nat 1).
     rewrite Nat2Z.inj_succ.
     now simpl in *.
     rewrite <- H2; omega.
Qed.



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
(* a faire: dans la conf maintenant, je suis aps arreter, et si je bouge, je epux être dans 
la même configuration et donc ne pas etre arreter la fois d'apres non plus et ca coinductivement
bla bla bla *)

(* apres montrer que si on est areter on a pas l'exploration *)
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


Lemma round_move : Loc.eq (Config.loc (round r da1 config1 (Good g)))
                         (Loc.add (Config.loc (config1 (Good g))) (Loc.opp Loc.unit)).
Proof.
  unfold move in Hmove.
  simpl in *.
  unfold Loc.add, Loc.opp, Loc.unit.
  generalize spect_rotation; intro.
  assert (Hpgm := pgm_compat r H).
  rewrite <- Zdiv.Zminus_mod_idemp_r.
  rewrite <- Hpgm, Hmove, Z.mod_1_l.
  reflexivity.
  generalize n_sup_1; unfold def.n; omega.
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
  rewrite round_move in Hs.
  unfold Loc.add, Loc.opp, Loc.unit, def.n in *.
  rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same in Hs.
  simpl in *.
  rewrite Zdiv.Zplus_mod_idemp_r in Hs.
  replace (create_conf1 g + -1) with (create_conf1 g - 1) in Hs by omega.
  apply neq_a_a1 with (a := create_conf1 g).
  unfold Loc.eq in *.
  rewrite Z.mod_mod in Hs.
  assumption.
  unfold def.n; omega.
  omega.
Qed.  


(* Lemma n_np1_st : forall conf, Spect.eq (!!conf) (!!config1) ->
                              ~Stopped (execute r bad_demon1 conf).
Proof.
intros conf Heqc Habs.
destruct Habs as (Hs, _).
unfold stop_now in Hs.
simpl in *.
specialize (Hs (Good g)).
unfold Config.eq_RobotConf in Hs.
destruct Hs as (Hs, _).
simpl in *.
unfold move in *.
unfold apply_sim, trans in Hs;
simpl in *.
set (Config.map
                      (fun infoR : Config.RobotConf =>
                       {|
                       Config.loc := Loc.add (Config.loc (conf (Good g)))
                                       (Loc.opp (Config.loc infoR));
                       Config.robot_info := Config.robot_info infoR |}) conf)
as conf2.
fold conf2 in Hs.
unfold Loc.eq, Loc.add, Loc.opp in *.
cut (Loc.eq (Config.loc (conf (Good g)))
          (Loc.opp
             (r
                (!!
                   (Config.map
                      (fun infoR : Config.RobotConf =>
                       {|
                       Config.loc := Loc.add (Config.loc (conf (Good g))) (Loc.opp (Config.loc infoR));
                       Config.robot_info := Config.robot_info infoR |}) conf)))))
       (create_conf1 g +
         (Z.of_nat def.n -
          r
            (!! conf)))).
intros Hf.
rewrite Hf, Hmove in Hs.
clear Hf.
unfold Loc.eq in Hs.
replace ((create_conf1 g + (Z.of_nat def.n - 1)) mod Z.of_nat def.n)
with ((create_conf1 g - 1) mod Z.of_nat def.n) in Hs.
now apply neq_a_a1 in Hs.
replace ((create_conf1 g + (Z.of_nat def.n - 1))) with
(create_conf1 g + Z.of_nat def.n - 1) by omega.
replace (create_conf1 g + Z.of_nat def.n - 1) with
(Z.of_nat def.n + (create_conf1 g - 1)) by omega.
rewrite <- Zdiv.Zplus_mod_idemp_l, Zdiv.Z_mod_same_full.
replace ((0 + (create_conf1 g - 1))) with ((create_conf1 g - 1)) by omega.
reflexivity.
unfold Loc.eq, Loc.add, Loc.opp; simpl in *.
generalize n_sup_1; intros Hn1.
unfold def.n.
repeat rewrite Z.mod_mod; try omega.
rewrite Zdiv.Zplus_mod_idemp_r.
unfold Config.map.
Qed.

Lemma no_will_s : ~ Will_stop (execute r bad_demon1 config1).
Proof.
intros Habs.
destruct Habs eqn : H.
now apply moving_no_stop.
simpl in *.

auto.
Qed. *)

(* final theorem first part: if we move, In the asynchronous model, if k divide n, 
   then the exploration with stop of a n-node ring is not possible. *)

Theorem no_exploration : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
Proof.
intros Hmod Habs.
specialize (Habs bad_demon1).
unfold FullSolExplorationStop in *.
destruct (Habs config1) as (Hvisit, Hstop).
destruct Hstop.
now apply moving_no_stop in H.
destruct Hstop.
now apply 
simpl in *.
+ Hstopped.
  clear Hvisit Habs Hstopped.
  simpl in *. 
  unfold stop_now, move in *.
  specialize (H g).
  unfold config1 in *; simpl in *.
  apply neq_a_1a in H.
  auto.
+ destruct Hwill_stop. admit.
  destruct (create_conf1 g.
  simpl in *. admit.
  simpl in *.
  
  unfold create_conf1 in H.
specialize (Hvisit Loc.unit).
destruct Hvisit as [Hvisited| Hwill_be_visited].
+ destruct Hvisited.
  simpl in *. unfold is_visited, config1 in H.
  simpl in *.
  generalize (config1_ne_unit Hmod); intros.
  destruct H as (g, Hfalse); specialize (H0 g);
  contradiction.
+ destruct Hstop as [Hstopped| Hwill_stop]. admit.
  destruct Hwill_stop as [Hstopped| Hwill_stop].
  destruct Hstopped as (Hstop, Hstopped), Hwill_be_visited as [Hvisited|Hwill_be_v];
  hnf in *; simpl in *; try (
  destruct Hvisited;
  simpl in *;
  unfold is_visited in *;
  destruct H as (g, visited)).
  - specialize (Hstop g).
    hnf in *.
    unfold Loc.add, Loc.opp in Hstop; simpl in *.
    
    admit.
  - unfold move in *.
  
  destruct s.
  unfold stop_now in *.
  generalize (config1_ne_unit Hmod); intros Hneq_unit.
   
   
  
  
  destruct Hwill_be_visited.
 - destruct H.
   simpl in *.
   unfold round in H.
   hnf in H.
   destruct H.
   destruct (step da1 (Good x)); simpl in *. Focus 2.
   generalize (config1_ne_unit Hmod); intros.
   specialize (H1 x). contradiction.
   hnf in *.
   destruct Hstop eqn : Hs.
   * destruct s.
     unfold stop_now in *.
     generalize (s x). intros sx.
     simpl in *.
     hnf in sx.
     generalize n_sup_1; intros.
     unfold Loc.add, Loc.unit, def.n in sx.
     rewrite Z.mod_mod in sx; try omega.
     
     unfold move in *.
     assert (Heq : Config.eq config1 (Config.map (apply_sim (t (create_conf1 x))) config1)).
     { unfold Config.map, apply_sim.
       destruct (t (create_conf1 x)) eqn : Ht.
       unfold sim_f.
       
     destruct (t (create_conf1 x)) eqn : Ht.
     destruct (sim_f) eqn : Hsim.
     rewrite Hmove in *.
     admit.
   * simpl in *.
   unfold apply_sim, Config.map, DiscreteSimilarity.retraction, Common.Sim.sim_f, Loc.unit, Loc.eq
   in *;
   simpl in *.
   destruct (t (create_conf1 x)) eqn : Ht.
   destruct (sim_f) eqn : Hsim.
   intuition.
   
   
Save.
