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
Require Import Pactole.ContinuousDVGraphFormalism.
Require Import Pactole.Exploration.ZnZ.Definitions.
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
(* Require Import Pactole.GraphEquivalence. *)
Require Import Pactole.FiniteGraphFormalism.

(* On a un espace V/E qui représente un graphe.
   On veux transposer Z/nZ sur un graphe V/E.
   Apres on veux utiliser ConfigA2D pour avoir un graph continu.
   pourquoi V/E <=> Z/nZ?
    - Z/nZ représente un anneau donc un graphe.
    - V c'est tout les entiers entre 0 et n
    - E c'est entre les nombres qui se suivent.


   un anneau avec V et E c'est : 
   [n] noeuds V et pour tout E [(src : V) * (tgt : V)], src = tgt (+/-) 1.
 *)

Set Implicit Arguments.

(* in a ring, edges can only be in three directions *)
Inductive direction := Forward | Backward | AutoLoop.

Module MakeRing <: FiniteGraphDef
    with Definition n := n (* ring size *)
    with Definition V := Fin.t n (* set of nodes *)
    with Definition E := ((Fin.t n * direction)%type). (* set of edges *)

  Definition n := n.
  Definition V := Fin.t n.

  (* Loc is a function to pass from a node as in a finite set to a integer, 
     which can be easily computate *)
  Definition Loc (v : V): Loc.t := ((Z.of_nat (proj1_sig (Fin.to_nat v))) mod Z.of_nat n)%Z.

  Definition dir := direction. 

  Definition E := (V * dir)%type.
  Definition Veq v1 v2 := Loc.eq (Loc v1) (Loc v2).

  (* the following lemmas are used to easily prove that 
           (Z.to_nat (l mod Z.of_nat n)) = (l mod Z.of_nat n) *)
  Lemma Loc_sup_0 : forall l : Loc.t, (0 <= l mod Z.of_nat n)%Z.
  Proof.
  intros;
      unfold Loc.add; try apply Zdiv.Z_mod_lt; generalize n_sup_1; intro Hn;
        unfold def.n, n in *.
    rewrite <- Nat2Z.inj_0; apply inj_gt.
    omega.
  Qed.
  
  Lemma Loc_inf_n (l : Loc.t): Z.to_nat (l mod Z.of_nat n)%Z < n.
  Proof.
    intros;
      unfold Loc.add; try apply Zdiv.Z_mod_lt; generalize n_sup_1; intro Hn;
        unfold def.n, n in *.
    rewrite <- Nat2Z.id, <- Z2Nat.inj_lt;
    try (apply Zdiv.Z_mod_lt;
    rewrite <- Nat2Z.inj_0; apply inj_gt;
    omega).
    omega.
  Qed.

  (* a function to pass a integer to a finit set *)
  Definition Loc_inv (l : Loc.t) : V := (Fin.of_nat_lt (Loc_inf_n l)).

  Lemma loc_fin : forall l, (l mod Z.of_nat n = (Loc (Loc_inv l)))%Z.
  Proof.
    intros.
    unfold Loc, Loc_inv.
    rewrite Fin.to_nat_of_nat.
    simpl.
    rewrite Z2Nat.id.
    rewrite Z.mod_mod.
    reflexivity.
    generalize n_sup_1; unfold n; omega.
    apply Zdiv.Z_mod_lt.
    generalize n_sup_1; unfold n; omega.
  Qed.


  (* a simplifying lemma *)
  Lemma fin_loc : forall v, Veq v (Loc_inv (Loc v)).
  Proof.
    intros.
    unfold Veq.
    unfold Loc.eq.
    rewrite <-loc_fin, Z.mod_mod.
    reflexivity.
    unfold def.n; generalize n_sup_1; omega.
  Qed.

  Instance Loc_inv_compat : Proper (Loc.eq ==> Veq) Loc_inv.
  Proof.
    intros l1 l2 Hl.
    unfold Veq.
    rewrite <- 2 loc_fin.
    unfold Loc.eq, def.n in *; rewrite 2 Z.mod_mod; try (generalize n_sup_1; omega).
  Qed.
    
  Definition tgt (e:E) : V:= let t :=
                              match snd e with
                              | Forward => Loc.add (Loc (fst e)) 1
                              | Backward => Loc.add (Loc (fst e)) (-1)
                              | AutoLoop => Loc (fst e)
                              end
                          in Loc_inv t.
  Definition src (e:E) : V := (fst e).

  Parameter threshold : E -> R.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  

  Definition Eeq (e1 e2 : E) := Veq (fst e1) (fst e2)
                          /\ snd e1 = snd e2.
  
  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.
  
  Lemma Veq_equiv : Equivalence Veq.
  Proof.
    unfold Veq.
    split.
    - now intro v.
    - now intros v1 v2 Hv.
    - intros v1 v2 v3 Hv1 Hv3. now transitivity (Loc v2).
  Qed.

  Instance Loc_compat : Proper (Veq ==> Loc.eq) Loc.
  Proof.
    intros v1 v2 Hv.
    now unfold Veq, Loc.eq in *.
  Qed.  
  
  
  Lemma Eeq_equiv : Equivalence Eeq.
  Proof.
    split.
    + intros e.
      unfold Eeq.
      repeat split; reflexivity.
    + intros e1 e2 (Hes, Het).
      unfold Eeq.
      repeat split; now symmetry.
    + intros e1 e2 e3 (Hs12, Ht12) (Hs23, Ht23). 
      unfold Eeq.
      repeat split. unfold Veq in *. now rewrite Hs12, Hs23.
      now transitivity (snd e2).
  Qed.

  Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Proof.
    intros e1 e2 He.
    unfold Eeq in He.
    unfold tgt.
    destruct He as (Ht, Hd); unfold src, Loc.add in *.
    rewrite Hd; destruct (snd e2).
    unfold Veq in *.
    rewrite <- 2 loc_fin.
    assert (Ht' : Loc.eq (Loc (fst e1) + 1) (Loc (fst e2) +1)).
    { unfold Loc.eq.
      now rewrite <- Zdiv.Zplus_mod_idemp_l, Ht, Zdiv.Zplus_mod_idemp_l.
    }
    now rewrite Ht'.
    assert (Ht' : Loc.eq (Loc (fst e1) + -1) (Loc (fst e2) + -1)).
    { unfold Loc.eq.
      now rewrite <- Zdiv.Zplus_mod_idemp_l, Ht, Zdiv.Zplus_mod_idemp_l.
    }
    now rewrite Ht'.
    assert (Z.of_nat n <> 0%Z).
    generalize n_sup_1; unfold n; omega.
    unfold Veq, Loc.eq in *.
    now rewrite <- 2 fin_loc.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof.
    intros e1 e2 He.
    now unfold Eeq in He.
  Qed.


    
  Lemma Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Proof.
    unfold V, Veq. intros. apply Loc.eq_dec.
  Qed.

  Lemma dir_eq_dec : forall d d': direction, {d = d'} + { d <> d'}.
  Proof.
    intros.
    destruct d, d'; intuition; right; discriminate.
  Qed.
    
  Lemma Eeq_dec : forall e e' : E, {Eeq e e'} + {~Eeq e e'}.
  Proof.
    intros.
    unfold Eeq.
    destruct (Veq_dec (fst e) (fst e')),
    (dir_eq_dec (snd e) (snd e')); intuition.
  Qed.

  Definition find_edge v1 v2 := if Loc.eq_dec (Loc v1) (Loc.add (Loc v2) 1) then
                                  Some (v1, Backward)
                                else
                                  if Loc.eq_dec (Loc.add (Loc v1) 1) (Loc v2) then
                                    Some (v1, Forward)
                                  else
                                    if Loc.eq_dec (Loc v1) (Loc v2) then
                                      Some (v1, AutoLoop)
                                    else
                                      None.

 
    
  Lemma find_edge_Some : forall e :E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof.
    intros.
    unfold find_edge, Eeq, src, tgt, opt_eq, Veq in *.
    destruct (snd e) eqn : Hdir.
    - destruct (Loc.eq_dec (Loc (fst e))
        (Loc.add (Loc (Loc_inv (Loc.add (Loc (fst e)) 1))) 1)).
      + rewrite <- loc_fin in e0.
        generalize k_sup_1, k_inf_n.
        intros.
        assert (H2n : 2 < n) by (unfold n; omega).
        clear H; clear H0.
        exfalso.
        unfold Loc.eq, Loc.add, def.n in e0.
        fold n in *.
        rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod in e0.
        set (X := (Loc (fst e))%Z) in *; set (N := Z.of_nat n) in *.
        rewrite <- Z.mod_mod in e0 at 1; try (unfold N; omega).
        rewrite Zdiv.Zplus_mod_idemp_l in e0.
        replace (X+1+1)%Z with (X + (1 + 1))%Z in e0 by omega.
        rewrite <- Zdiv.Zplus_mod_idemp_l in e0.
        generalize Zdiv.Z_mod_lt; intros Hlt;
          specialize (Hlt X N); destruct Hlt as (Hl0, HlN); try (unfold N; omega).
        destruct (Z.compare (X mod N + 2) N) eqn : Heq;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *;
        simpl in *.
        * rewrite Heq in e0.
          rewrite Z.mod_same in e0; try (unfold N; omega).
          replace (X mod N)%Z with (N - 2)%Z in e0 by omega.
          rewrite <- Zdiv.Zminus_mod_idemp_l in e0; try (unfold N; omega).
          rewrite Z.mod_same in e0; try (unfold N; omega).
          simpl in *.
          apply Zdiv.Z_mod_zero_opp_full in e0.
          simpl in e0.
          rewrite Z.mod_small in e0; try (unfold N; omega).
        * rewrite Z.mod_small in e0; try omega.
          rewrite Z.mod_small with (a := (X mod N + 2)%Z) in e0; try omega.
        * assert (X mod N = N - 1)%Z.
          destruct (Z.compare (X mod N + 1)%Z N) eqn : Heq_1;
            try rewrite Z.compare_lt_iff in *;
            try rewrite Z.compare_eq_iff in *;
            try rewrite Z.compare_gt_iff in *; try omega.
          rewrite H in *.
          replace (N - 1 + 2)%Z with (N + 1) %Z in e0 by omega.
          rewrite Z.mod_small, <- Zdiv.Zplus_mod_idemp_l, Z.mod_same in e0;
            try (unfold N; omega).
          simpl in e0.
          rewrite Z.mod_1_l in e0; try (unfold N; omega).
          assert (N = 2)%Z by omega.
          unfold N in *; omega.
        * omega.
      + destruct (Loc.eq_dec (Loc.add (Loc (fst e)) 1)
        (Loc (Loc_inv (Loc.add (Loc (fst e)) 1)))).
        * repeat split; try now simpl.
        * destruct n1.
          rewrite <- loc_fin. unfold Loc.eq; rewrite Z.mod_mod; try reflexivity.
          unfold def.n; generalize n_sup_1; omega.
    - destruct (Loc.eq_dec (Loc (fst e))
        (Loc.add (Loc (Loc_inv (Loc.add (Loc (fst e)) (-1)))) 1)).
      + repeat split; try now simpl.
      + destruct n0.
        rewrite <- loc_fin.
        unfold Loc.add.
        rewrite Zdiv.Zplus_mod_idemp_l.
        unfold Loc.eq; rewrite Z.mod_mod; try omega.
        rewrite Zdiv.Zplus_mod_idemp_l; simpl. 
        replace (Loc (fst e) + -1 + 1)%Z with (Loc (fst e) + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (Loc (fst e) + 1 - 1)%Z with (Loc (fst e) + 0)%Z by omega.
        assert (Loc (fst e) + 0 = Loc (fst e))%Z.
        omega.
        rewrite H.
        reflexivity.
        generalize n_sup_1.
        unfold def.n; omega.
    - destruct (Loc.eq_dec (Loc (fst e))
        (Loc.add (Loc (Loc_inv (Loc (fst e)))) 1)).
      rewrite Loc.add_comm, <- loc_fin in e0.
      unfold Loc.add in e0.
      rewrite Zdiv.Zplus_mod_idemp_r in e0;
        try now apply neq_a_1a in e0.
      destruct (Loc.eq_dec (Loc.add (Loc (fst e)) 1)
        (Loc (Loc_inv (Loc (fst e))))).
      rewrite <- loc_fin in *; unfold Loc.add in *;
        rewrite Zdiv.Zplus_mod_idemp_l in n0.
      unfold Loc.eq in *.
      rewrite 2 Z.mod_mod in *; try (unfold def.n; generalize n_sup_1; lia).
      destruct (Loc.eq_dec (Loc (fst e)) (Loc (Loc_inv (Loc (fst e)))));
      rewrite <- loc_fin in *.
      now split; simpl.
      destruct n2.
      unfold Loc.eq; rewrite Z.mod_mod; now unfold def.n; generalize n_sup_1; lia.
  Qed.
  
  Lemma find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Proof.
    intros a b; split; unfold find_edge;
      destruct (Loc.eq_dec (Loc a) (Loc.add (Loc b) 1)).
    - intros Hnone.
      discriminate.
    - destruct (Loc.eq_dec (Loc.add (Loc a) 1) (Loc b)); try discriminate.
      destruct (Loc.eq_dec (Loc a) (Loc b)); try discriminate.
      intros Hnone.
      clear Hnone.
      intros e (Hsrc, Htgt).
      unfold Veq, Loc.eq, Loc.add, src, tgt in *.
      rewrite <- loc_fin in *.
      destruct (snd e).
      + rewrite <- Htgt in n1.
        destruct n1.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l with (a := Loc (fst e)).
        rewrite Hsrc.
        rewrite Zdiv.Zplus_mod_idemp_l, 3 Z.mod_mod;
          unfold def.n; generalize n_sup_1; lia.
      + destruct n0.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l.
        rewrite <- Hsrc, <- Htgt.
        unfold Loc.add.
        try repeat rewrite Z.mod_mod, Zdiv.Zplus_mod_idemp_l;
          try (unfold n, def.n; generalize n_sup_1; omega).
        replace (Loc (fst e) + -1 + 1)%Z with (Loc (fst e) + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (Loc (fst e) + 1 - 1)%Z with ((Loc (fst e)) + 0)%Z by omega.
        assert (Loc (fst e) + 0 = Loc (fst e))%Z.
        omega.
        rewrite H.
        reflexivity.
      + destruct n2; now rewrite <- Hsrc, <- Htgt, Z.mod_mod;
        generalize n_sup_1; unfold def.n; lia.
    - intros He.
      specialize (He (a, Backward)).
      destruct He.
      split; unfold Veq, src, tgt; simpl.
      reflexivity.
      rewrite <- loc_fin in *.
      unfold Loc.add.
      rewrite <- Zdiv.Zplus_mod_idemp_l, e.
      unfold Loc.add.
      rewrite 2 Zdiv.Zplus_mod_idemp_l.
      replace (Loc b + -1 + 1)%Z with (Loc b + 1 + -1)%Z by omega. 
      rewrite Z.add_opp_r with (m := 1%Z).
      replace (Loc b + 1 - 1)%Z with (Loc b + 0)%Z by omega.
      assert (Loc b + 0 = Loc b)%Z.
      omega.
      rewrite H.
      unfold Loc.eq; rewrite 2 Z.mod_mod;
        try (unfold def.n; generalize n_sup_1; omega).
    - intros Ho.
      destruct (Loc.eq_dec (Loc.add (Loc a) 1) (Loc b)).
      specialize (Ho (a, Forward)).
      destruct Ho.
      split; unfold src, tgt, Veq. now unfold fst.
      unfold Loc.eq in *.
      unfold n; fold def.n.
      simpl.
      rewrite <- loc_fin.
      rewrite <- e; simpl.
      rewrite Z.mod_mod; generalize n_sup_1; unfold def.n; lia.
      destruct (Loc.eq_dec (Loc a) (Loc b)).
      specialize (Ho (a,AutoLoop)).
      destruct Ho; simpl.
      split; try easy.
      unfold tgt.
      simpl.
      unfold Veq.
      rewrite <- loc_fin; rewrite <- e; unfold Loc.eq, def.n; rewrite Z.mod_mod;
        generalize n_sup_1;
        try lia.
      reflexivity.
  Qed.

  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
    intros v1 v2 Hv12 v3 v4 Hv34. 
    unfold Eeq, find_edge; simpl.
    destruct (Loc.eq_dec (Loc v1) (Loc.add (Loc v3) 1)),
             (Loc.eq_dec (Loc v2) (Loc.add (Loc v4) 1)).
    simpl.
    repeat split; try reflexivity. assumption.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv12, <- Zdiv.Zplus_mod_idemp_l, Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv12, <- Zdiv.Zplus_mod_idemp_l, <- Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (Loc.add (Loc v1) 1) (Loc v3)),
    ( Loc.eq_dec (Loc.add (Loc v2) 1) (Loc v4)).
    simpl.
    now split.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv34, <- Zdiv.Zplus_mod_idemp_l, Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv34, <- Zdiv.Zplus_mod_idemp_l, <- Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (Loc v1) (Loc v3)), (Loc.eq_dec (Loc v2) (Loc v4)).
    simpl; try now split.
    destruct n3. unfold Veq in *. now rewrite Hv12, Hv34 in e.
    destruct n3. unfold Veq in *; now rewrite <- Hv12, <- Hv34 in e.
    now split.
  Qed.

  Set Printing Implicit.

  
  Lemma find2st : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) ->
                                Veq v1 (src e) /\ Veq v2 (tgt e).  
  Proof.
    intros v1 v2 e Hsome.
    assert (Z.of_nat def.n <> 0%Z).
    generalize n_sup_1; unfold n; fold def.n; omega.
    unfold find_edge in *.
    destruct (Loc.eq_dec (Loc v1) (Loc.add (Loc v2) 1)).
    simpl in *.
    unfold Eeq, Veq, src, tgt, Loc.eq in *.
    rewrite <- loc_fin.
    destruct Hsome as (Hsomef,Hsomes); rewrite <- Hsomes, <- Hsomef.
    simpl in *.
    split; try reflexivity.
    unfold Loc.add.
    rewrite <- Zdiv.Zplus_mod_idemp_l.
    rewrite <- Hsomef, e0.
    rewrite Zdiv.Zplus_mod_idemp_l.
    unfold Loc.add, Veq, Loc.eq, Loc.add.
    rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod; try omega.
    replace ((Loc v2) + 1 + -1)%Z with (Loc v2)%Z.
    rewrite Z.mod_mod; generalize n_sup_1; unfold def.n; lia.
    symmetry.
    rewrite Zeq_plus_swap. omega.
    destruct (Loc.eq_dec (Loc.add (Loc v1) 1) (Loc v2)).
    simpl in *.
    unfold src, tgt.
    destruct Hsome as (Hsomef,Hsomes). simpl in *.
    unfold Veq, Loc.eq, Loc.add in *.
    rewrite <- loc_fin in *.
    rewrite Z.mod_mod in *; try omega.
    rewrite <- Hsomes.
    rewrite <- Zdiv.Zplus_mod_idemp_l, <- Hsomef, Zdiv.Zplus_mod_idemp_l.
    split; try reflexivity.
    rewrite e0, Z.mod_mod.
    reflexivity.
    omega.
    destruct (Loc.eq_dec (Loc v1) (Loc v2)).
    cbn in *.
    destruct Hsome as (Hsomef,Hsomes). simpl in *.
    unfold Veq, Loc.eq, Loc.add, src, tgt in *.
    rewrite <- loc_fin in *.
    rewrite Z.mod_mod in *; try omega.
    rewrite <- Hsomes.
    split; try easy.
    now rewrite <- e0, <-Hsomef.
    split; easy.
  Qed.
    
End MakeRing.


Module LocationA : LocationADef (MakeRing).
  Definition t := MakeRing.V.
  Definition eq := MakeRing.Veq.
  Definition eq_equiv : Equivalence eq := MakeRing.Veq_equiv.
  Definition eq_dec : forall l l' : t, {eq l l'} + {~eq l l'} := MakeRing.Veq_dec.
End LocationA.
  
Module N : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End N.

Module Names := Robots.Make (N).

Module ConfigA := Configurations.Make (LocationA)(N)(Names).





