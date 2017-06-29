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
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid Compare_dec Morphisms FinFun.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
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
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
 Lemma n_pos : n <> 0. Proof. generalize n_sup_1. omega. Qed.
End def.

Module Gra := MakeRing.
(** The setting is a ring. *)

  (** There are KG good robots and no byzantine ones. *)


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(K).
Export DefsE.
Export Gra.
Export MakeRing.

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
  Loc.mul (Loc_inv (((Z_of_nat ((proj1_sig (Fin.to_nat f))*(n / kG)))))) Loc.unit.


(* the starting configuration where a robots is on the origin, 
   and every other robot is at a distance of [x*(kG/n)] where x is between 1 and kG *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc :=  pos;
                             Config.info :=
                               {| Info.source := Loc.add (Loc.opp Loc.unit) pos;
                                  Info.target := pos  |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.info := {| Info.source := pos; Info.target := pos |} |}
            end.

Set Printing Implicit.
Unset Printing Dependent Evars Line.

Lemma conf1_new_aux:
  forall gg: nat,  
    Loc (Loc.mul (Loc_inv (((Z_of_nat (gg*(n / kG)))))) Loc.unit) mod Z.of_nat (n/kG) = 0.
Proof.
  intros.
  unfold Loc.unit, Loc.mul.
  rewrite <- 3 loc_fin.
  generalize ImpossibilityKDividesN.conf1_new_aux.
  intros.
  unfold Graph.n, ImpossibilityKDividesN.def.n; fold n.
  rewrite Z.mod_mod;
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold n, ImpossibilityKDividesN.def.n; lia).
  unfold n, ImpossibilityKDividesN.def.n.
  rewrite <- Loc_eq_mod.
  assert (Hlem : forall x, ImpossibilityKDividesN.Loc.eq (x mod Z.of_nat n) x).
  {
    unfold n; fold ImpossibilityKDividesN.def.n.
    intros; now rewrite <- Loc_eq_mod.
  }
  unfold ImpossibilityKDividesN.Loc.mul, ImpossibilityKDividesN.Loc.unit in *.
  rewrite Z.mul_mod;
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia).
  unfold n, ImpossibilityKDividesN.def.n.
  repeat rewrite Z.mod_mod; try (rewrite 1 Zdiv.Zmod_1_l, Zdiv.Zmult_mod_idemp_l);
    try (generalize ImpossibilityKDividesN.n_sup_1; unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia).
  unfold n, ZnZ.ImpossibilityKDividesN.def.n.
  assert (htruc : forall x, (x mod Z.of_nat n) mod Z.of_nat (n/kG) = 0 -> x mod Z.of_nat (n/kG) = 0).
  { intros x Hmod.
    generalize kdn; intro.
    assert (Z.of_nat n mod Z.of_nat kG = 0).
    rewrite <- Zdiv.mod_Zmod; unfold n, kG. rewrite H0; lia.
    generalize k_sup_1; lia.
    assert (Z.of_nat (n/kG) > 0)%Z.
    { generalize k_sup_1, k_inf_n.
      intros.
      unfold n, kG in *.
      rewrite Zdiv.div_Zdiv.
      apply Z.lt_gt.
      apply Znumtheory.Zdivide_Zdiv_lt_pos; try omega.
      apply Z.mod_divide; try lia.
      omega.
    }
    rewrite <- Z.div_exact, <- Zdiv.div_Zdiv in H1;
      try (generalize ImpossibilityKDividesN.k_sup_1; unfold kG; lia).
    rewrite H1, Z.mul_comm, Z.rem_mul_r, <- Zdiv.Zplus_mod_idemp_r,
    <- Z.mul_mod_idemp_l, Z.mod_same,
    Z.mul_0_l, Z.mod_0_l, Z.add_0_r, Z.mod_mod in Hmod;
      try (generalize ZnZ.ImpossibilityKDividesN.k_sup_1; unfold kG; lia); try lia.
  }    
  apply htruc.
  unfold n; rewrite Z.mod_mod;
    try (generalize ZnZ.ImpossibilityKDividesN.n_sup_1;
         unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia).
  unfold n, kG, ZnZ.ImpossibilityKDividesN.def.n.
  simpl.
  apply H.
Qed.



(* A position where a robot is in config1 divied [k/n] *)
Lemma conf1_new_1 : forall g0: Names.G, Loc (create_conf1 g0) mod Z.of_nat (n/kG) = 0.
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
                                  Loc.eq (create_conf1 g) (Loc_inv loc).
Proof.
  intros loc Hmod.
  generalize Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_new_2.
  intros.
  specialize (H loc).
  unfold Loc.eq, LocationA.eq, MakeRing.Veq.
  unfold create_conf1, ImpossibilityKDividesN.Loc.eq; rewrite <- loc_fin.
  fold ImpossibilityKDividesN.Loc.eq.
  destruct H.
  now unfold n, kG in *.
  exists x.
  unfold Loc.mul, ImpossibilityKDividesN.Loc.mul, Loc.unit.
  rewrite Z.mul_mod.
  repeat rewrite <- loc_fin in *.
  rewrite <- Z.mul_mod.
  unfold ImpossibilityKDividesN.create_conf1, ImpossibilityKDividesN.Loc.eq,
    ImpossibilityKDividesN.Loc.mul, n, kG, Loc.unit in *.
  repeat rewrite <- loc_fin in *.
  repeat rewrite <- Loc_eq_mod.
  rewrite <- Zdiv.Zmult_mod.
  rewrite Z.mod_mod in H.
  apply H.
  generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n; lia.
  generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n; lia.
  generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n; lia.
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
  generalize Pactole.Exploration.ZnZ.ImpossibilityKDividesN.unique_g.
  intros.
  specialize (H g1 g2 H0).
  apply H.
  unfold config1, create_conf1 in *.
  simpl in *.
  unfold Loc.mul, Loc.unit in *.
  unfold ImpossibilityKDividesN.Loc.mul, ImpossibilityKDividesN.Loc.eq in *.
  repeat rewrite <- loc_fin in *.
  unfold Graph.n, n, ZnZ.ImpossibilityKDividesN.def.n in *; fold n in *.
  rewrite 7 Z.mod_mod in *; try rewrite 2 Z.mul_mod in *;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  unfold ImpossibilityKDividesN.create_conf1, ImpossibilityKDividesN.Loc.mul.
  unfold ZnZ.ImpossibilityKDividesN.def.n; fold n kG.
  rewrite 4 Z.mod_mod in *; try rewrite <- 2 Z.mul_mod in *;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia). 
  apply H1.
Qed.


(* The same that [NoDup_count_occ'] but with the abstraction. *)

Parameter g : Names.G.


Variable r : Equiv.DGF.robogram.


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
  generalize Pactole.Exploration.ZnZ.ImpossibilityKDividesN.conf1_1.
  unfold Loc.eq, LocationA.eq, MakeRing.Veq, create_conf1, Loc.eq, Loc.add, Loc.opp,
  Loc.mul, Loc.unit, n, kG, ImpossibilityKDividesN.Loc.eq,
  ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.mul,
  ImpossibilityKDividesN.Loc.opp in *.
  intros.
  specialize (H idg g0).
  destruct H.
  exists x.
  repeat rewrite <- loc_fin.
  repeat rewrite (Z.mul_mod (Graph.Loc _)), Zdiv.Zplus_mod, Zdiv.Zminus_mod in *;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia). 
  repeat rewrite <- loc_fin in *.
  repeat rewrite Z.mod_mod,
  <- (Z.mul_mod ), <- Zdiv.Zplus_mod, <- Zdiv.Zminus_mod in *; 
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).  
  unfold ImpossibilityKDividesN.create_conf1,
  ImpossibilityKDividesN.Loc.mul, n, kG in *.
  rewrite Z.mod_mod in *;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  rewrite <- Zdiv.Zplus_mod in H.
  rewrite Zdiv.Zplus_mod_idemp_r.
  repeat rewrite Z.mod_mod;
  repeat rewrite Z.mul_mod_idemp_l in *; repeat rewrite Z.mul_mod_idemp_r in *;
  repeat rewrite Zdiv.Zplus_mod_idemp_l in *;
    repeat rewrite Zdiv.Zplus_mod_idemp_r in *;
    rewrite Z.mod_mod in H;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  assumption.
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
  generalize Pactole.Exploration.ZnZ.ImpossibilityKDividesN.unique_g_2.
  unfold Loc.eq, LocationA.eq, MakeRing.Veq, create_conf1, Loc.eq, Loc.add, Loc.opp,
  Loc.mul, Loc.unit, n, kG, ImpossibilityKDividesN.Loc.eq,
  ImpossibilityKDividesN.Loc.add,ImpossibilityKDividesN.create_conf1,
  ImpossibilityKDividesN.Loc.mul,
  ImpossibilityKDividesN.Loc.opp in *.
  intros.
  specialize (H g0 g1 g2 H0).
  destruct H.
  unfold ZnZ.ImpossibilityKDividesN.def.n, Graph.n in *;
    fold n in *.
  repeat rewrite <- loc_fin in *.
  repeat rewrite Z.mod_mod;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  repeat rewrite Z.mul_mod_idemp_l; repeat rewrite Z.mul_mod_idemp_r;
  repeat rewrite Zdiv.Zplus_mod_idemp_l;
  repeat rewrite Zdiv.Zplus_mod_idemp_r.
  rewrite 17 Z.mod_mod in H1;
    rewrite 3 Z.mul_mod_idemp_l in H1; rewrite 3 Z.mul_mod_idemp_r in H1;
      repeat rewrite Zdiv.Zplus_mod_idemp_l in H1;
      repeat rewrite Zdiv.Zplus_mod_idemp_r in H1;
      try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  assumption.
Qed.


(* The spectre of the initial configuration is the same that the one during 
   its computaion [round]. *)

Import Equiv.DGF.
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
                             if Loc.eq_dec (Config.loc (Rconf))
                                           (Info.target (Config.info
                                                             (Rconf)))
                             then 
                               Active (trans (Config.loc (Rconf)))
                             else
                               Moving true))
                 
    |}.
  Proof.
    - intuition.
      unfold lift_conf in H.
      unfold Loc.eq_dec, Names.G in *.
      destruct (LocationA.eq_dec (Config.loc Rconfig)
                                 (Info.target (Config.info
                                                   Rconfig)));
        try assumption;
        now simpl in *.
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
      rewrite Hl_rc.
      unfold Aom_eq.
      reflexivity.
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
  generalize config1_ne_unit.
  intros.
  unfold n, kG in H0.
  specialize (H H0 g0).
  intro; apply H.
  unfold Loc.eq, LocationA.eq, MakeRing.Veq,  create_conf1, Loc.mul, Loc.unit,
  ImpossibilityKDividesN.Loc.eq, ImpossibilityKDividesN.create_conf1,
  ImpossibilityKDividesN.Loc.mul, n, kG in *.
  rewrite Z.mod_mod, Z.mul_mod, <- 3 loc_fin, 7 Z.mod_mod, <- Z.mul_mod in H1;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia).
  rewrite Z.mod_mod;
    try (generalize n_sup_1; unfold ZnZ.ImpossibilityKDividesN.def.n, n; lia). 
  assumption.
Qed.

(** **  First case: the robots moves **)

Lemma neq_a_1a : forall a, ~Location.eq
        (Graph.Loc_inv
           (((Loc (Loc_inv 1) mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n +
              Graph.Loc a mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n)
             mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n) mod 
            Z.of_nat Graph.n)) a.
Proof.
  generalize neq_a_1a.
  intros.
  specialize (H (Loc a)).
    unfold Loc.eq, LocationA.eq, MakeRing.Veq, Loc.add, Loc.unit.
  unfold ImpossibilityKDividesN.Loc.eq, ImpossibilityKDividesN.Loc.add in *.
  repeat rewrite <- loc_fin.
  unfold ImpossibilityKDividesN.Loc.unit; repeat rewrite Z.mod_1_l;
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold ZnZ.ImpossibilityKDividesN.def.n, n;  lia).
  fold ImpossibilityKDividesN.Loc.unit.
  unfold Graph.n, n in *.
  rewrite 3 Z.mod_mod; rewrite Z.mod_mod in H;
    try (generalize ImpossibilityKDividesN.n_sup_1;
         unfold ZnZ.ImpossibilityKDividesN.def.n;  lia).
  repeat rewrite Zdiv.Zplus_mod_idemp_l in *;
    repeat rewrite Zdiv.Zplus_mod_idemp_r in *.
  intro; symmetry in H0; now apply H.
Qed.
(*
Definition move := r.(Equiv.DGF.pgm)
                       (!! (Config.map
                              (apply_sim (trans (Info.target
                                                   (Config.info (conf (Good g0))))))
                              (round r da1 config1))).
*)
Parameter m : Z.
Hypothesis Hmove : forall g,
    Loc (r.(Equiv.DGF.pgm)
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
  unfold Loc.add, ImpossibilityKDividesN.Loc.add.
  rewrite Zdiv.Zplus_mod, Hk.
  destruct (Hc (Good g)) as (Hc',_). 
  rewrite Hc'.
  rewrite <- Zdiv.Zplus_mod.
  reflexivity.
  unfold Loc.add, ImpossibilityKDividesN.Loc.add.
  rewrite 2 (Zdiv.Zplus_mod (Loc k1)) , Hk.
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

Definition AlwaysEquiv (e : execution) : Prop :=
  Stream.next_forever (fun e1 => equiv_conf config1
                                        (Stream.hd e1)) e.
                                                                    
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.next_forever (fun e1 => ~Stopped e1) e.

    
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


Section Move1.
  
  Hypothesis Hm : Loc.eq (Loc_inv m) (Loc_inv 1).


(* This function moves every robots of [k] nodes. *)


(* the same than [count_occ_map], but with the abstraction. *)

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
        rewrite 2 Loc.add_comm with (v := (Loc.opp (Config.loc (conf (Good g0)))))
          in Hloc;
        apply Loc.add_reg_l in Hloc;
        destruct Hg1 as (Hg1,_), Hg2 as (Hg2,_);
        rewrite Hg1, Hg2 in Hloc;
        simpl in *;
        apply Loc.add_reg_l in Hloc.
        unfold Loc.opp, ImpossibilityKDividesN.Loc.opp.
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
       unfold Loc.opp, ImpossibilityKDividesN.Loc.opp, Loc.add.
       repeat rewrite <- loc_fin.
       repeat rewrite Zdiv.Zminus_mod_idemp_l; repeat rewrite Zdiv.Zminus_mod_idemp_r.
       repeat rewrite Zdiv.Zplus_mod_idemp_l; repeat rewrite Zdiv.Zplus_mod_idemp_r;
         repeat rewrite Z.mod_mod;
       try (unfold n; generalize n_sup_1; lia).
       rewrite
         (ImpossibilityKDividesN.Loc.add_compat
            (Graph.Loc (Config.loc (conf (Good g1))))
            (Loc (Loc.add x0 (create_conf1 g1))) (Loc_compat Hl_g1)
            _ _ (reflexivity _)).
       rewrite <- (Zdiv.Zminus_mod_idemp_r _ (Loc (Config.loc (conf (Good g0)))));
         unfold n; fold ZnZ.ImpossibilityKDividesN.def.n; rewrite Hl.
       unfold Loc.add;repeat rewrite <- loc_fin.
       unfold ImpossibilityKDividesN.Loc.add, ZnZ.ImpossibilityKDividesN.def.n; fold n;
         repeat rewrite <- loc_fin.
       set (N := Z.of_nat n).
       repeat rewrite Z.mod_mod;
       try (unfold N, n; generalize n_sup_1; lia).
       repeat rewrite Zdiv.Zminus_mod_idemp_l;
       repeat rewrite Zdiv.Zminus_mod_idemp_r;
       repeat rewrite Zdiv.Zplus_mod_idemp_l;
       repeat rewrite Zdiv.Zplus_mod_idemp_r;
       repeat rewrite Zdiv.Zminus_mod_idemp_l;
       repeat rewrite Zdiv.Zminus_mod_idemp_r.
       rewrite Z.sub_add_distr.
       simpl.
       now replace (Graph.Loc x0 + Graph.Loc (create_conf1 g1) +
                (N - Graph.Loc x0 - Graph.Loc (create_conf1 g0)))
       with (Graph.Loc (create_conf1 g1) + (N - Graph.Loc (create_conf1 g0))) by lia.

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
        do 2 rewrite Loc.add_comm with (v := Loc.opp _) in Heq;
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
         equiv_conf config1 conf
    -> Config.eq
         (round r da1 (round r da1 conf))
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
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Isomorphism.section)
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
    exists x.
    intros [g0|b]; try ImpByz b.
    destruct (H (Good g0)) as (Hl, (_, Ht));
      split; try rewrite Hl; try rewrite Ht; easy.
  }
  destruct Hconf_eq as (x0, Hconf_eq).
  unfold f_conf in *.
  destruct (Hconf_eq (Good g)) as (Hlg0, (Hsg0, Htg0));simpl in *.
  simpl.
  assert (Hequiv := config1_Spectre_Equiv).
  assert (Hequiv_g := config1_Spectre_Equiv conf g Hequiv').
  simpl.
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
  rewrite Loc.add_opp in e; fold Loc.origin in e. simpl.
  assert (Hn := neq_a_1a).
  specialize (Hn (Config.loc (conf (Good g)))).
  destruct Hn.
  unfold Loc.add in *.
  unfold Loc.eq, LocationA.eq, Veq in *.
  rewrite <- loc_fin in *.
  rewrite Hmove in *.
  rewrite <- Loc_eq_mod in *.
  unfold ImpossibilityKDividesN.Loc.add in *.
  rewrite Zdiv.Zplus_mod, Hm in e.
  unfold Loc.unit, ImpossibilityKDividesN.Loc.unit.
  repeat rewrite <- loc_fin in *.
  unfold n, ZnZ.ImpossibilityKDividesN.def.n in *.
  repeat rewrite Zdiv.Zplus_mod_idemp_l in *.
  repeat rewrite Zdiv.Zplus_mod_idemp_r in *.
  rewrite Z.mod_mod in e;
  repeat rewrite Z.mod_mod;
    try (generalize n_sup_1; lia).
  apply (e).
  simpl in *.
  destruct (Loc.eq_dec (Config.loc (conf (Good g)))
           (Loc.add
              (r
                 (!!
                    (Config.map (apply_sim (trans (Config.loc (conf (Good g)))))
                       conf))
                 (Loc.add (Config.loc (conf (Good g)))
                    (Loc.opp (Config.loc (conf (Good g))))))
              (Config.loc (conf (Good g))))); try now destruct n0.
  simpl in *.
  reflexivity.
Qed.


Lemma round1_move_g_1 : forall g0,
    ~ Loc.eq (Config.loc (round r da1 (round r da1 config1) (Good g0)))
      (Config.loc (config1 (Good g0))).
Proof.
  intros g0.
  unfold move in Hmove.
  simpl in *.
  assert (Hpgm := pgm_range r (!! config1) (create_conf1 g0)).
  intros Hfalse.
  assert (Hequiv_triv : equiv_conf config1 config1).
  exists Loc.origin.
  unfold f_conf.
  intros [g_i|b_i]; simpl.
  repeat split; simpl;
  rewrite (Loc.add_comm Loc.origin);
  now rewrite Loc.add_origin.
  reflexivity.
  rewrite (round_2_simplify_1 Hequiv_triv (Good g0)) in *.
  simpl in *.
  specialize (Hmove g0).
  simpl in *.
  rewrite Loc.add_opp in Hfalse; fold Loc.origin in Hfalse.
  unfold Loc.add in Hfalse.
  unfold Loc.eq, LocationA.eq , Veq in Hm.
  rewrite <- loc_fin, <- Loc_eq_mod in Hm.
  unfold ImpossibilityKDividesN.Loc.eq in Hfalse.
  unfold ImpossibilityKDividesN.Loc.add in Hfalse.
  rewrite Hmove, Zdiv.Zplus_mod, Hm in Hfalse.
   assert (Hn := neq_a_1a).
  specialize (Hn (create_conf1 g0)).
  destruct Hn.
  unfold Loc.add in *.
  unfold Loc.eq, LocationA.eq, Veq, ImpossibilityKDividesN.Loc.add in *.
  rewrite <- loc_fin in *.
  unfold Loc.unit, ImpossibilityKDividesN.Loc.unit.
  repeat rewrite <- loc_fin in *.
  unfold n, ZnZ.ImpossibilityKDividesN.def.n in *.
  repeat rewrite Zdiv.Zplus_mod_idemp_l in *.
  repeat rewrite Zdiv.Zplus_mod_idemp_r in *.
  rewrite 2 Z.mod_mod in Hfalse;
  repeat rewrite Z.mod_mod;
    try (generalize n_sup_1; lia).
  apply (Hfalse).
Qed.


(* utiliser le prédicat d'équivalence (equiv_conf) pour prouver le spectre. *)



Lemma moving_no_stop : ~Stopped (((execute r bad_demon1 config1))).
Proof.
  intros Hs.
  generalize n_sup_1; intros Hn1.
  destruct Hs as (Hs,_).
  unfold stop_now in Hs.
  simpl in *.
  rewrite round_2_simplify_1 in Hs.
  specialize (Hs (Good g)).
  simpl in *.
  assert (Hmove' := Hmove g).
  simpl in *.
  destruct Hs as (Hl, (Hs, Ht)).
  simpl in *.
  rewrite Loc.add_opp in *.
  fold Loc.origin in *.
  unfold Loc.add in *; 
  rewrite Hmove' in *.
  simpl in *.
  unfold round in Hl.
  simpl in *.
  destruct (Loc.eq_dec (create_conf1 g) (create_conf1 g)) as [_|nfalse];
    try now destruct nfalse.
  simpl in *.
  destruct (Location.eq_dec
                (Loc.add
                   (r (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))
                      (Loc.add (create_conf1 g) (Loc.opp (create_conf1 g))))
                   (create_conf1 g)) (create_conf1 g)).
  rewrite Loc.add_opp in e; fold Loc.origin in e.
  unfold Loc.add, ImpossibilityKDividesN.Loc.add in e;
    unfold Loc.eq, LocationA.eq, Veq in Hm;
    rewrite  <- loc_fin,<- Loc_eq_mod in Hm.  
  rewrite Hmove',Zdiv.Zplus_mod, Hm in e.
  now apply neq_a_1a in e.
  unfold Loc.add, ImpossibilityKDividesN.Loc.add in *;
    unfold Loc.eq, LocationA.eq, Veq in Hm;
    rewrite  <- loc_fin,<- Loc_eq_mod in Hm.  
  rewrite Zdiv.Zplus_mod, Hm in *.
  symmetry in Hl;
    now apply neq_a_1a in Hl.
  exists Loc.origin.
  unfold f_conf.
  intros [g|b];
  repeat split;simpl;
    try rewrite (Loc.add_comm Loc.origin), Loc.add_origin; try easy.
Qed.  


Lemma round1_move_g_equiv : forall g0 conf,
    equiv_conf config1 conf ->
    ~ Loc.eq (Config.loc (round r da1 (round r da1 conf) (Good g0)))
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
    exists x.
    intros [g'|b]; try ImpByz b.
    destruct (H (Good g')) as (Hl, (_, Ht));
      split; try rewrite Hl; try rewrite Ht; easy.
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
   unfold Loc.add, ImpossibilityKDividesN.Loc.add in *;
    unfold Loc.eq, LocationA.eq, Veq in Hm;
    rewrite  <- loc_fin,<- Loc_eq_mod in Hm.  
   rewrite Hmove, Zdiv.Zplus_mod, Hm in *.
  now apply neq_a_1a in Hf.
Qed.

(* any configuration equivalent to the starting one will not stop if executed with 
   [r] and [bad_demon1] *)
Lemma moving_never_stop : forall conf,
    equiv_conf config1 conf ->
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
    now exists x.
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
    equiv_conf config1 conf
    -> AlwaysEquiv (execute r bad_demon1 conf).
Proof.
  cofix.
  intros.
  constructor.
  + now simpl.
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
      exists x.
      intros [g0|b]; try ImpByz b.
      destruct (H (Good g0)) as (Hl, (_, Ht));
        split; try rewrite Hl; try rewrite Ht; easy.
    }
    unfold equiv_conf.
    destruct H.
    exists (Loc.add x (Loc_inv m)).
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
    specialize (Hmove g0).
    simpl in *.
    unfold Loc.add, ImpossibilityKDividesN.Loc.add in *;
    unfold Loc.eq, LocationA.eq, Veq in Hm;
    rewrite  <- loc_fin,<- Loc_eq_mod in Hm.
    assert (Hmove_eq' := Loc_compat Hmove_eq).
   rewrite Hmove, Hm in Hmove_eq'.
    repeat split; simpl in *;
      try rewrite Loc.add_opp, Hmove_eq;
      destruct (H (Good g0)) as (Hl, (Hs, Ht));
      unfold Veq in *; repeat rewrite <- loc_fin in *;
      rewrite Zdiv.Zplus_mod;
      try rewrite Hl; try rewrite Ht;
        unfold f_conf;
          simpl in *;
        unfold ImpossibilityKDividesN.Loc.eq, n, ZnZ.ImpossibilityKDividesN.def.n in *;
        rewrite Hm;
        repeat rewrite Z.mod_mod;
        repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
        try (generalize n_sup_1; lia);
    unfold Loc.opp, ImpossibilityKDividesN.Loc.opp;
    rewrite <- loc_fin;
    rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same; simpl;
    unfold n, ZnZ.ImpossibilityKDividesN.def.n; repeat rewrite Z.mod_mod;
    try (rewrite Zdiv.Zplus_mod_idemp_r, Z.add_opp_diag_r, Z.mod_0_l;
    fold ImpossibilityKDividesN.Loc.origin Loc.origin;
    try (rewrite <- Zdiv.Zplus_mod_idemp_l, Hmove_eq'));
    repeat rewrite Z.mod_1_l;
    unfold Loc.add, ImpossibilityKDividesN.Loc.add;
    try (rewrite <- loc_fin);
    unfold n, ZnZ.ImpossibilityKDividesN.def.n, Loc.unit, ImpossibilityKDividesN.Loc.unit;
    repeat rewrite Z.mod_mod;
    try (rewrite Zdiv.Zplus_mod_idemp_r);
    try (generalize n_sup_1; unfold Loc.origin, ImpossibilityKDividesN.Loc.origin;
         lia).
    f_equiv; lia.
    rewrite <- loc_fin.
    repeat rewrite Z.mod_1_l;
    simpl;
    try (rewrite <- (Zdiv.Zplus_mod_idemp_r _ (Loc x + 1)), (Zdiv.Zplus_mod_idemp_l),
    Zdiv.Zplus_mod_idemp_r);
    replace (Loc x + 1 + (-1 + Graph.Loc (create_conf1 g0)))
    with  (Graph.Loc x + Graph.Loc (create_conf1 g0)) by lia;
    try (generalize n_sup_1; unfold n, Loc.origin, ImpossibilityKDividesN.Loc.origin;
         lia).
    f_equiv; lia.
    now exists x.
Qed.

(* the starting configuration respect the [AlwaysMoving] predicate *)

Lemma config1_AlwaysMoving : AlwaysMoving (execute r bad_demon1 config1).
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
Lemma never_stop : ~ Will_stop ((execute r bad_demon1 config1)).
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

  Hypothesis Hm : Loc.eq (Loc_inv m) (Loc_inv 0).

  Lemma round_simplify_0 : forall conf,
      equiv_conf config1 conf -> 
      Config.eq (round r da1 conf) conf.
  Proof.
    intros.
    unfold round.
    simpl in *.
    unfold lift_conf; simpl.
    intros [g|b]; try ImpByz b.
    destruct (Loc.eq_dec (Config.loc (conf (Good g)))
                         (Info.target (Config.info (conf (Good g))))).
    simpl in *.
    destruct (Location.eq_dec
         (Loc.add
            (r
               (!!
                  (Config.map (apply_sim (trans (Config.loc (conf (Good g))))) conf))
               (Loc.add (Config.loc (conf (Good g)))
                  (Loc.opp (Config.loc (conf (Good g))))))
            (Config.loc (conf (Good g)))) (Config.loc (conf (Good g)))); try easy.
    destruct n0.
    specialize (Hmove g).
    simpl in *.
    rewrite config1_Spectre_Equiv.
    simpl in *.
    rewrite Loc.add_opp; fold Loc.origin.
    unfold Loc.add.
    rewrite Hmove.
    unfold Loc.eq, LocationA.eq, Veq in Hm.
    rewrite <- loc_fin, <- Loc_eq_mod in Hm.
    unfold ImpossibilityKDividesN.Loc.add.
    rewrite Zdiv.Zplus_mod, Hm, <- Zdiv.Zplus_mod.
    rewrite <- loc_fin, Zdiv.Zmod_0_l.
    simpl.
    rewrite <- Loc_eq_mod.
    unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq.
    rewrite <- loc_fin.
    repeat rewrite Z.mod_mod; try generalize n_sup_1;
      unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia.
    destruct H.
    unfold f_conf in H;
      exists x;
      intros [g'|b]; try ImpByz b;
      destruct (H (Good g')) as (Hl, (_ , Ht));
      repeat split; simpl; try rewrite Hl;
        try rewrite Ht;
        try easy.
    destruct n0.
    destruct H.
    unfold f_conf in H;
      destruct (H (Good g)) as (Hl, (_ , Ht));
      repeat split; simpl; try rewrite Hl;
        try rewrite Ht;
        try easy.
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
      assert (Z.of_nat (n mod kG) = 0) by (unfold n, kG; generalize kdn; omega).
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
      apply (execute_compat (reflexivity r) (reflexivity bad_demon1)
                            (symmetry (round_simplify_0 Hequiv))).
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

Section Move_minus1.

  Hypothesis Hm : Loc.eq (Loc_inv m) (Loc.opp (Loc_inv 1)).

  Lemma round_2_config1 :
    Config.eq (round r da1 (round r da1 config1))
              (fun id =>
                 match id with
                 | Good g =>
                   {| Config.loc := Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g);
                      Config.info :=
                        {| Info.source := create_conf1 g;
                           Info.target := Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)
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
      unfold Location.eq, LocationA.eq, Veq, Loc.add, ImpossibilityKDividesN.Loc.add
        in *.
      repeat rewrite <- loc_fin, <-Loc_eq_mod in *.
      rewrite Hmove, <- Zdiv.Zplus_mod_idemp_l, Hm , Zdiv.Zplus_mod_idemp_l in e0.
      unfold Loc.opp, ImpossibilityKDividesN.Loc.opp in e0.
      repeat rewrite <- loc_fin in e0.
      assert (Hfalse :  Location.eq
     (Graph.Loc_inv
        (((Loc (Loc_inv 1) mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n +
           Graph.Loc ((create_conf1 g))
                     mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n)
          mod Z.of_nat ZnZ.ImpossibilityKDividesN.def.n) mod 
         Z.of_nat Graph.n)) ((create_conf1 g))).
      { unfold Location.eq, Veq.
        rewrite <- loc_fin.
        rewrite <- e0.
        unfold n, ZnZ.ImpossibilityKDividesN.def.n;
          set (N := Z.of_nat ImpossibilityKDividesN.n).
        rewrite <- (Zdiv.Zminus_mod_idemp_l N), Z.mod_same.
        rewrite <- loc_fin, 2 Z.mod_1_l.
        repeat rewrite Zdiv.Zplus_mod_idemp_l;
          repeat rewrite Zdiv.Zplus_mod_idemp_r.
        replace (1 + (0 - 1 + Graph.Loc (create_conf1 g))) with
        (Loc (create_conf1 g)) by lia.
        unfold ImpossibilityKDividesN.Loc.eq, N, ZnZ.ImpossibilityKDividesN.def.n.
        repeat rewrite Z.mod_mod;
          try (generalize n_sup_1; lia).
          try (generalize n_sup_1; unfold N; lia).
          try (generalize n_sup_1; unfold n, N; lia).
          try (generalize n_sup_1; unfold N; lia).
      }      
      now apply neq_a_1a in Hfalse.
    - simpl in *.
      destruct (Loc.eq_dec (create_conf1 g)
           (Loc.add
              (r (!! (Config.map (apply_sim (trans (create_conf1 g))) config1))
                 (Loc.add (create_conf1 g) (Loc.opp (create_conf1 g))))
              (create_conf1 g)))
        as [?|n0'];
        try (now destruct n0); try now destruct n0'.
      simpl in *.
      now repeat split; simpl; unfold Veq, Loc.add, Loc.opp in *;
        repeat rewrite <- loc_fin, <- Loc_eq_mod in *;
      rewrite ImpossibilityKDividesN.Loc.add_opp;
      fold Loc.origin;
      rewrite Hmove;
      unfold Loc.eq, LocationA.eq, Veq in Hm;
        repeat rewrite <- loc_fin, <- Loc_eq_mod in *;
        rewrite Hm;
      repeat rewrite <- Loc_eq_mod.
  Qed.

  Lemma round_2_2_simplify : Config.eq (f_conf (round r da1 (round r da1 (config1)))
                                               (Loc.opp (Loc_inv 1)))
                                       (round r da1
                                              (round r da1
                                                     (round r da1
                                                            (round r da1 config1)))).
  Proof.
    intros [g|b]; try ImpByz b.
    rewrite round_2_config1.
    unfold round.
    simpl in *; unfold lift_conf; simpl.
    destruct (Loc.eq_dec (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                         (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))
      as [?|nfalse]; try now destruct nfalse.
    simpl in *.
    assert (Location.eq (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans
                                       (Loc.add (Loc.opp (Loc_inv 1))
                                                (create_conf1 g))))
                                 (* (trans (Config.loc ((round r da1 (round r da1 config1)) (Good g)))))*) 
                                 (fun id : Names.ident =>
                                    match id with
                                    | Good g0 =>
                                      {|
                                        Config.loc := Loc.add 
                                                        (Loc.opp (Loc_inv 1)) 
                                                        (create_conf1 g0);
                                        Config.info :=
                                          {|
                                            Info.source := create_conf1 g0;
                                            Info.target := Loc.add
                                                               (Loc.opp (Loc_inv 1))
                                                               (create_conf1 g0)
                                          |} |}
                                    | Byz _ =>
                                      {|
                                        Config.loc := Loc.origin;
                                        Config.info :=
                                          {|
                                            Info.source := Loc.origin;
                                            Info.target := Loc.origin |} |}
                                    end)))
                           (Loc.add (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                                    (Loc.opp (Loc.add (Loc.opp (Loc_inv 1))
                                                      (create_conf1 g)))))
                        (r
                           (!!
                              (Config.map
                                 (apply_sim
                                    (trans (Config.loc (config1 (Good g)))))
                                 config1))
                           (Loc.add (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                                    (Loc.opp (Loc.add (Loc.opp (Loc_inv 1))
                                                      (create_conf1 g)))))
           ).
    { apply pgm_compat; try reflexivity.
      rewrite <- round_2_config1.
      assert (Hc_eq :
                Config.eq
                  (Config.map
                     (apply_sim (trans (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))))
                     (round r da1 (round r da1 config1)))
                  (Config.map
                     (apply_sim
                        (trans (Config.loc ((round r da1 (round r da1 config1))
                                              (Good g)))))
                     (round r da1 (round r da1 config1)))).
      { apply Config.map_compat; try easy.
        apply apply_sim_compat.
        assert (Location.eq (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                            (Config.loc
                               (round r da1 (round r da1 config1) (Good g))))
          by now rewrite (round_2_config1 (Good g)).
        now rewrite H.
      }
      rewrite Hc_eq.
      rewrite (config1_Spectre_Equiv (round r da1 (round r da1 config1)) g).
      reflexivity.
      exists (Loc.opp (Loc_inv 1)).
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
                               (trans (Loc.add (Loc.opp (Loc_inv 1))
                                               (create_conf1 g))))
                            (fun id : Names.ident =>
                               match id with
                               | Good g0 =>
                                 {|
                                   Config.loc := Loc.add 
                                                   (Loc.opp (Loc_inv 1)) 
                                                   (create_conf1 g0);
                                   Config.info :=
                                     {|
                                       Info.source := create_conf1 g0;
                                       Info.target := Loc.add (Loc.opp (Loc_inv 1))
                                                                (create_conf1 g0)
                                     |} |}| Byz _ =>
                                 {|
                                   Config.loc := Loc.origin;
                                   Config.info := {|
                                                         Info.source := Loc.origin;
                                                         Info.target := Loc.origin |} |}
                               end)))
                      (Loc.add (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                               (Loc.opp (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))))
                   (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))
                (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))
      as [?|nmove].
    - exfalso.
      rewrite H in e0.
      rewrite Loc.add_opp in e0; fold Loc.origin in e0;
      simpl in *. unfold Loc.add in e0; rewrite Hmove in e0.
      assert (Hfalse : Location.eq
                         ((Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))
                         (Loc.add (Loc_inv 1) (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))).
      { unfold Loc.eq, LocationA.eq, Veq in Hm.
        rewrite <- loc_fin, <- Loc_eq_mod in Hm.
        unfold Location.eq, Veq, Loc.add, Loc.opp in *;
          repeat rewrite <- loc_fin in *.
        unfold ImpossibilityKDividesN.Loc.opp in *;
          unfold ImpossibilityKDividesN.Loc.add in *;
          rewrite Zdiv.Zplus_mod in *.
        rewrite Hm in *.
        rewrite 12 Z.mod_mod in e0;
          try (unfold n, ZnZ.ImpossibilityKDividesN.def.n; generalize n_sup_1; lia);
          rewrite Z.mod_1_l in *;
          repeat rewrite Z.mod_mod;
          try (unfold n, ZnZ.ImpossibilityKDividesN.def.n; generalize n_sup_1; lia);
          unfold ImpossibilityKDividesN.Loc.eq in *;
          unfold n, ZnZ.ImpossibilityKDividesN.def.n in *;
          set (N := Z.of_nat ImpossibilityKDividesN.n) in *;
          try (rewrite <- (Zdiv.Zminus_mod_idemp_l N 1) in * );
          try (rewrite Z.mod_same in * );
          try (rewrite Zdiv.Zplus_mod_idemp_r, <- (Zdiv.Zplus_mod_idemp_r _ 1));
          try (rewrite <- e0 at 2);
          try (rewrite 2 (Zdiv.Zplus_mod_idemp_l (0-1)),
               (Zdiv.Zplus_mod_idemp_r _ (0-1)), 3 Z.mod_mod);
          try (rewrite Zdiv.Zplus_mod_idemp_r);
          try (rewrite Zdiv.Zplus_mod_idemp_l);
          try (now replace (1 + (0 - 1 + (0 - 1 + Graph.Loc (create_conf1 g))))
               with (0 - 1 + Graph.Loc (create_conf1 g)) by lia);
          try (unfold N; generalize n_sup_1; lia).
      }
      unfold Loc.add, ImpossibilityKDividesN.Loc.add in Hfalse.
      symmetry in Hfalse.
      rewrite Zdiv.Zplus_mod in Hfalse.
      now apply neq_a_1a in Hfalse.
    - simpl in *.
      destruct (Loc.eq_dec
                  (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                  (Loc.add
                     (r
                        (!!
                           (Config.map
                              (apply_sim (trans (Loc.add (Loc.opp (Loc_inv 1))
                                                         (create_conf1 g))))
                              (fun id : Names.ident =>
                                 match id with
                                 | Good g0 =>
                                   {|
                                     Config.loc := Loc.add (Loc.opp (Loc_inv 1))
                                                           (create_conf1 g0);
                                     Config.info :=
                                       {|

                                         Info.source := create_conf1 g0;
                                         Info.target := Loc.add
                                                            (Loc.opp (Loc_inv 1))
                                                            (create_conf1 g0) |} |}
                                 | Byz _ =>
                                   {|
                                     Config.loc := Loc.origin;
                                     Config.info :=
                                       {|
                                         Info.source := Loc.origin;
                                         Info.target := Loc.origin |} |}
                                 end)))
                        (Loc.add (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))
                                 (Loc.opp (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g)))))
                     (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g))))
      ; try now destruct nmove.
      simpl in *.
      repeat split; simpl; unfold Veq, Loc.add, Loc.opp in *;
      repeat rewrite <- loc_fin;
      repeat rewrite <- loc_fin in H;
      clear n0 nmove;
      unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq,
      ImpossibilityKDividesN.Loc.add, n, ZnZ.ImpossibilityKDividesN.def.n in *;
        rewrite (Zdiv.Zplus_mod (Loc (r _ _)));
      simpl in *;
      rewrite H;
      repeat rewrite Z.mod_mod;
      repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
      repeat rewrite Z.mod_1_l;
      try (unfold ImpossibilityKDividesN.Loc.opp at 4);
      try rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same;
      repeat rewrite Zdiv.Zminus_mod_idemp_r;
      repeat rewrite Zdiv.Zplus_mod_idemp_r;
      replace  ((ImpossibilityKDividesN.Loc.opp 1 + Graph.Loc (create_conf1 g) +
                 (0 - (ImpossibilityKDividesN.Loc.opp 1 + Graph.Loc (create_conf1 g)))))
      with (0) by lia;
      try rewrite Z.mod_0_l;
      fold ImpossibilityKDividesN.Loc.origin Loc.origin;
      try rewrite Hmove;
      unfold Loc.eq, LocationA.eq, Veq in Hm;
        repeat rewrite <- loc_fin, <- Loc_eq_mod;
        try rewrite Hm;
        repeat rewrite <- Loc_eq_mod;
      try rewrite <- loc_fin, <- Loc_eq_mod in Hm;
      try rewrite <- (Zdiv.Zplus_mod_idemp_l m); 
        fold ZnZ.ImpossibilityKDividesN.def.n in *;
        try rewrite Hm;
      repeat rewrite <- loc_fin;
      try rewrite Z.mod_1_l;
      unfold n, ZnZ.ImpossibilityKDividesN.def.n;
      try (now repeat rewrite Zdiv.Zplus_mod_idemp_l);
      try (unfold Loc.origin, ImpossibilityKDividesN.Loc.origin;
           generalize n_sup_1; lia).
  Qed.
    
  Lemma round1_move_g_1_m : forall g0,
      ~ Loc.eq (Config.loc (round r da1 (round r da1 (round r da1 (round r da1 config1))) (Good g0)))
        (Config.loc ((round r da1 (round r da1 config1)) (Good g0))).
  Proof.
    intros g0.
    simpl in *.
    rewrite <- (round_2_2_simplify (Good g0)).
    unfold f_conf.
    simpl in *.
    rewrite (round_2_config1 (Good g0)). 
    simpl in *.
    intros Hf.
    apply (@neq_a_1a (Loc.add (Loc.opp (Loc_inv 1)) (create_conf1 g0))).
    rewrite <- Hf.
    unfold Loc.add, Loc.opp, ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp, n, ZnZ.ImpossibilityKDividesN.def.n.
    repeat rewrite <- loc_fin.
    repeat rewrite Z.mod_1_l;
      try (generalize n_sup_1; unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia);
    repeat rewrite Z.mod_mod;
      try (generalize n_sup_1; unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia);
    try rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same;
      try (generalize n_sup_1; unfold n, ZnZ.ImpossibilityKDividesN.def.n; lia);
    try rewrite (Zdiv.Zplus_mod_idemp_l ((0 - 1)));
    try rewrite Zdiv.Zplus_mod_idemp_r;
    replace (1 +
         (0 - 1 +
          ((0 - 1) mod Z.of_nat n + Graph.Loc (create_conf1 g0)) mod Z.of_nat n))
    with (((0 - 1) mod Z.of_nat n + Graph.Loc (create_conf1 g0)) mod Z.of_nat n)
      by lia;
    try now rewrite <- Loc_eq_mod.
  Qed.


  (* utiliser le prédicat d'équivalence (equiv_conf) pour prouver le spectre. *)



  Lemma moving_no_stop_m : ~Stopped ((execute r bad_demon1 (round r da1 (round r da1 config1)))).
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

Lemma round_2_simplify_m1 :
  forall conf,
         equiv_conf (round r da1 (round r da1 config1)) conf
    -> Config.eq
         (round r da1 (round r da1 conf))
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
                           (conf (Good g))))⁻¹).(Iso.Iso.sim_V).(Isomorphism.section)
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
    exists (Loc.add (Loc.opp (Loc_inv 1)) x).
    intros [g'|b]; try ImpByz b.
    assert (Hr :=  round_2_config1).
    specialize (Hr (Good g')).
    destruct Hr as (Hl, (_, Ht)).
    simpl in *.
    destruct (H (Good g')) as (Hl', (_,Ht')).
    rewrite Hl', Ht' in *.
    unfold f_conf in *.
    simpl in *.
    rewrite Hl, Ht in *.
    repeat split;simpl; 
    rewrite Loc.add_assoc, (Loc.add_comm x); easy.
  }
  destruct Hconf_eq as (x0, Hconf_eq).
  unfold f_conf in *.
  destruct (Hconf_eq (Good g)) as (Hlg0, (Hsg0, Htg0));simpl in *.
  simpl.
  assert (Hequiv := config1_Spectre_Equiv).
  assert (Hequiv_g := config1_Spectre_Equiv conf g Hequiv').
  simpl.
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
                     (Loc_inv m)) by now rewrite <- Hmove, <- fin_loc.
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
              (Config.loc (conf (Good g))))); try now destruct n0.
  simpl in *.
  reflexivity.
  destruct nfalse; rewrite Hlg0, Htg0.
  assert (Hr := round_2_config1 (Good g)).
  simpl in *.
  destruct Hr as (Hl, (_, Ht)).
  simpl in *.
  now rewrite Hl, Ht.
Qed.

  
  Lemma round1_move_g_equiv_m : forall g0 conf,
      equiv_conf (round r da1 (round r da1 config1)) conf ->
      ~ Loc.eq (Config.loc (round r da1 (round r da1 conf) (Good g0)))
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
      exists (Loc.add (Loc.opp (Loc_inv 1)) x).
      intros [g'|b]; try ImpByz b.
      assert (Hr :=  round_2_config1).
      specialize (Hr (Good g')).
      destruct Hr as (Hl, (_, Ht)).
      simpl in *.
      destruct (H (Good g')) as (Hl', (_,Ht')).
      rewrite Hl', Ht' in *.
      unfold f_conf in *.
      simpl in *.
      rewrite Hl, Ht in *.
      repeat split;simpl; 
        rewrite Loc.add_assoc, (Loc.add_comm x); easy.
    }
    rewrite (round_2_simplify_m1 Hequiv (Good g0)) in *.
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
    assert (Hmove' : Loc.eq
                       (r (!! (Config.map (apply_sim (trans (create_conf1 g0))) config1))
                          Loc.origin)
                       (Loc_inv m)) by now rewrite <- Hmove, <- fin_loc.
    unfold Location.eq,LocationA.eq, Veq, ImpossibilityKDividesN.Loc.eq in Hf.
    rewrite Hm in *.
    rewrite (Loc.add_compat Hmove' (reflexivity _)) in Hf.
    exfalso.
    apply (@neq_a_1a (Config.loc (conf (Good g0)))).
    unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq.
    rewrite <- Hf at 1.
    unfold Loc.add, Loc.opp, ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp, n, ZnZ.ImpossibilityKDividesN.def.n.
    rewrite Zdiv.Zminus_mod, Z.mod_same;
      repeat rewrite <- loc_fin;
      repeat rewrite Z.mod_mod;
      repeat rewrite Zdiv.Zminus_mod_idemp_r;
      repeat rewrite Zdiv.Zplus_mod_idemp_l;
      repeat rewrite Zdiv.Zplus_mod_idemp_r;
      try (generalize n_sup_1; unfold n; lia).
      now replace (1 + (0 - 1 + Graph.Loc (Config.loc (conf (Good g0))))) with
      (Graph.Loc (Config.loc (conf (Good g0)))) by lia.
  Qed.

  (* any configuration equivalent to the starting one will not stop if executed with 
   [r] and [bad_demon1] *)
  Lemma moving_never_stop_m : forall conf,
      equiv_conf (round r da1 (round r da1 config1)) conf ->
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
    CAE_m : equiv_conf (round r da1 (round r da1 config1)) (Stream.hd e) ->
            AlwaysEquiv_m (Stream.tl (Stream.tl e)) -> AlwaysEquiv_m e.


  
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
      equiv_conf (round r da1 (round r da1 config1)) conf
      -> AlwaysEquiv_m (execute r bad_demon1 conf).
  Proof.
    cofix.
    intros.
    constructor.
    + now simpl in *.
    + apply AlwaysEquiv_conf1_m.
      assert (Hr := round_2_config1).
      assert (Hequiv' :
                (exists k, forall id,
                      Location.eq (Config.loc (conf id))
                                  (Loc.add k (Config.loc (config1 id)))
                      /\
                      Location.eq (Info.target (Config.info (conf id)))
                                  (Loc.add k (Info.target
                                                (Config.info (config1 id)))))).
      { destruct H.
        exists (Loc.add (Loc.opp (Loc_inv 1)) x).
        intros [g'|b]; try ImpByz b.
        assert (Hr' :=  round_2_config1).
        specialize (Hr' (Good g')).
        destruct Hr' as (Hl', (_, Ht')).
        simpl in *.
        destruct (H (Good g')) as (Hl'', (_,Ht'')).
        rewrite Hl'', Ht'' in *.
        unfold f_conf in *.
        simpl in *.
        rewrite Hl', Ht' in *.
        repeat split;simpl; 
          rewrite Loc.add_assoc, (Loc.add_comm x); easy.
      }
      unfold equiv_conf.
      destruct H.
      exists (Loc.add x (Loc_inv m)).
      rewrite (round_2_config1) in *.
      simpl.
      rewrite round_2_simplify_m1.
      simpl.
      intros id.
      simpl.
      destruct id; try ImpByz b.
      specialize (Hr (Good g0));
      simpl in *.
      destruct Hr as (Hl, (_, Ht)).
      simpl in *.
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
      specialize (Hmove' g0).
      simpl in *.
      assert (Hmove'' : Loc.eq
                          (r (!! (Config.map (apply_sim (trans (create_conf1 g0)))
                                             config1))
                             Loc.origin)
                          (Loc_inv m)) by now rewrite <- (Hmove g0), <- fin_loc.
      repeat split; simpl;
      unfold Location.eq,LocationA.eq, Veq, ImpossibilityKDividesN.Loc.eq in *;
      try rewrite Hm in Hmove'';
      unfold Loc.add, ImpossibilityKDividesN.Loc.add; rewrite Zdiv.Zplus_mod;
      try rewrite (pgm_compat r
                  _ _ (reflexivity _) (Loc.add (Config.loc (conf (Good g0)))
             (Loc.opp (Config.loc (conf (Good g0))))) Loc.origin (Loc.add_opp _));
      try rewrite Hmove_eq, Hmove'', <- (Zdiv.Zplus_mod_idemp_r (Loc (Loc_inv m))), Hm;
      destruct (H (Good g0)) as (Hl', _); simpl in Hl';
      unfold Location.eq, Veq, ImpossibilityKDividesN.Loc.eq in *;
      unfold Loc.add, Loc.opp, ImpossibilityKDividesN.Loc.add, ImpossibilityKDividesN.Loc.opp, n, ZnZ.ImpossibilityKDividesN.def.n in *;
      try rewrite Zdiv.Zminus_mod, Z.mod_same;
        repeat rewrite <- loc_fin;
        repeat rewrite Z.mod_mod;
        repeat rewrite Zdiv.Zminus_mod_idemp_r;
        repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
        try (generalize n_sup_1; unfold n; lia);
        try rewrite <- Zdiv.Zplus_mod_idemp_r;
        try rewrite Hl';
        try rewrite Zdiv.Zminus_mod, Z.mod_same;
        repeat rewrite <- loc_fin;
        repeat rewrite Z.mod_mod;
        repeat rewrite Zdiv.Zminus_mod_idemp_r;
        repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
        try (generalize n_sup_1; unfold n; lia);
        try (rewrite <- (Z.mod_mod m), (loc_fin m); unfold n; try rewrite Hm);
        try rewrite Zdiv.Zminus_mod, Z.mod_same;
        repeat rewrite <- loc_fin;
        repeat rewrite Z.mod_mod;
        repeat rewrite Zdiv.Zminus_mod_idemp_r;
        repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
        try (generalize n_sup_1; unfold n; lia);
      try rewrite Z.add_comm;
      fold n;
      try rewrite <- Zdiv.Zplus_mod_idemp_r,
      <- (Zdiv.Zplus_mod_idemp_r (0-1+Loc (create_conf1 g0))), Zplus_assoc_reverse,
      (Z.add_comm ((0 - 1 + Loc (create_conf1 g0)) mod Z.of_nat n)
                  ((0 - 1) mod Z.of_nat n));
      symmetry; 
      try now rewrite Zplus_assoc_reverse.
      rewrite Z.add_comm.
      rewrite <- Zdiv.Zplus_mod_idemp_r, (Zdiv.Zplus_mod_idemp_r (0-1)),
      Zdiv.Zplus_mod_idemp_r.
      f_equiv; lia.
      now exists x; rewrite round_2_config1.
  Qed.

  (* the starting configuration respect the [AlwaysMoving] predicate *)

  Lemma config1_AlwaysMoving_m : AlwaysMoving (execute r bad_demon1
                                                       (round r da1 (round r da1
                                                                           config1))).
  Proof.
    apply AlwaysEquiv_impl_AlwaysMoving_m.
    now simpl.
    apply AlwaysEquiv_conf1_m.
    exists Loc.origin.
    unfold f_conf.
    intros [g|b]; try ImpByz b.
    now repeat split;simpl; rewrite (Loc.add_comm Loc.origin), Loc.add_origin.
  Qed.
  
  Lemma never_stop_m : ~ Will_stop (execute r bad_demon1 (round r da1 (round r da1 (config1)))).
  Proof.
    apply AlwaysMoving_impl_not_WillStop.
    cbn.
    reflexivity.
    apply config1_AlwaysMoving_m.
  Qed.

  
  Theorem no_exploration_moving_m : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
  Proof.
    intros Hmod Habs.
    specialize (Habs bad_demon1).
    unfold FullSolExplorationStop in *.
    destruct (Habs (round r da1 (round r da1 (config1)))) as (_, Hstop).
    now apply never_stop_m.
  Save.

End Move_minus1.


Lemma range_r :  forall g,
    let s := (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g))))) config1)) in
    Loc.eq (r s Loc.origin) (Loc_inv 1)
    \/ Loc.eq (r s Loc.origin) (Loc_inv 0)
    \/ Loc.eq (r s Loc.origin) (Loc.opp (Loc_inv 1)).
Proof.
  intros Rconf s.
  assert (Hrange := pgm_range r s Loc.origin).
  destruct Hrange as (lp, (ep, (Hl, He))).
  unfold Graph.find_edge, Graph.Eeq in *.
  destruct (ImpossibilityKDividesN.Loc.eq_dec (Loc Loc.origin)
                                              (ImpossibilityKDividesN.Loc.add
                                                 (Loc lp) 1)).
  do 2 right.
  rewrite Hl.
  rewrite <- (Loc.add_origin (Loc.opp (Loc_inv 1))).
  rewrite Loc.add_comm.
  unfold Loc.add, n, Loc.opp; fold ZnZ.ImpossibilityKDividesN.def.n.
  rewrite (ImpossibilityKDividesN.Loc.add_compat _ _ e _ _ (reflexivity _)).
  rewrite <- 2 loc_fin, <- ImpossibilityKDividesN.Loc.add_assoc,
  Z.mod_1_l, <- Loc_eq_mod;
    try (generalize n_sup_1; unfold n; lia);
    now unfold ZnZ.ImpossibilityKDividesN.def.n;
    fold n;
    rewrite <- 2 Loc_eq_mod,
    ImpossibilityKDividesN.Loc.add_opp, ImpossibilityKDividesN.Loc.add_origin,
    <- fin_loc;
    try (generalize n_sup_1; unfold n; lia).
  destruct (ImpossibilityKDividesN.Loc.eq_dec
              (ImpossibilityKDividesN.Loc.add (Loc Loc.origin) 1) (Loc lp)).
  left.
  rewrite Hl.
  unfold Loc.origin in *.
  rewrite <- loc_fin, ImpossibilityKDividesN.Loc.add_comm, ImpossibilityKDividesN.Loc.add_origin in *.
  rewrite e.
  now rewrite <- fin_loc.
  destruct (ImpossibilityKDividesN.Loc.eq_dec (Loc Loc.origin) (Loc lp)); try easy.
  right; left.
  fold ImpossibilityKDividesN.Loc.origin Loc.origin.
  unfold Loc.eq, LocationA.eq, Veq.
  now rewrite Hl, e.
Qed.


Theorem no_exploration : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
Proof.
  generalize no_exploration_idle, no_exploration_moving, no_exploration_moving_m,
  range_r.
  intros.
  specialize (Hmove g);
    specialize (H2 g).
  destruct H2.
  unfold Loc.eq, LocationA.eq, Veq in H2.
  apply H0; try assumption;
  rewrite Hmove in H2; rewrite H2.
  now rewrite <- fin_loc.
  destruct H2; unfold Loc.eq, LocationA.eq, Veq in *.
  now apply H; rewrite Hmove in H2; try rewrite <- loc_fin, <- Loc_eq_mod.
  now apply H1; rewrite Hmove in H2; try rewrite <- loc_fin, <- Loc_eq_mod.
Save.

End DiscreteExploration.

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
Qed.