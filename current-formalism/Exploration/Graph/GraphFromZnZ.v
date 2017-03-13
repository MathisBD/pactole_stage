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
Require Import Pactole.AtomicGraphFormalism.
Require Import Pactole.Exploration.ZnZ.Definitions.
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
Require Import Pactole.GraphEquivalence.

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


  Inductive direction := Forward | Backward.

Module MakeRing <: GraphDef 
    with Definition V := Loc.t
    with Definition Veq := Loc.eq
    with Definition E := ((Loc.t * direction)%type).

  Definition dir := direction. 

  Definition V := Loc.t.
  Definition E := (Loc.t * dir)%type.
  Definition Veq := Loc.eq.
  Definition tgt (e:E) := match snd e with
                          | Forward => Loc.add (fst e) 1
                          | Backward => Loc.add (fst e) (-1)
                          end.
  Definition src (e:E) := fst e.

  Parameter threshold : E -> R.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  

  Definition Eeq (e1 e2 : E) := Veq (fst e1) (fst e2)
                          /\ snd e1 = snd e2.
  
  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.
  
  Lemma Veq_equiv : Equivalence Veq. Proof. unfold Veq; apply Loc.eq_equiv. Qed.

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
      repeat split. now transitivity (src e2). now transitivity (snd e2).
  Qed.

  Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Proof.
    intros e1 e2 He.
    unfold Eeq in He.
    unfold tgt.
    destruct He as (Ht, Hd); unfold src, Loc.add in *.
    rewrite Hd; destruct (snd e2);
    now rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof.
    intros e1 e2 He.
    now unfold Eeq in He.
  Qed.


    
  Lemma Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Proof.
    unfold V, Veq; apply Loc.eq_dec.
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
    destruct (Veq_dec (src e) (src e')),
    (dir_eq_dec (snd e) (snd e')); intuition.
  Qed.

  Definition find_edge v1 v2 := if Loc.eq_dec v1 (Loc.add v2 1) then
                                  Some (v1, Backward)
                                else
                                  if Loc.eq_dec (Loc.add v1 1) v2 then
                                    Some (v1, Forward)
                                  else
                                    None.

  Lemma find_edge_Some : forall e :E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof.
    intros.
    unfold find_edge, Eeq, src, tgt, opt_eq, Veq in *.
    destruct (snd e) eqn : Hdir.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) 1) 1)).
      + generalize k_sup_1, k_inf_n.
        intros.
        assert (H2n : 2 < n) by omega.
        clear H; clear H0.
        exfalso.
        unfold Loc.eq, Loc.add, def.n in e0.
        rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod in e0.
        set (X := (fst e)%Z) in *; set (N := Z.of_nat n) in *.
        replace (X+1+1)%Z with (X + (1 + 1))%Z in e0 by omega.
        rewrite <- Z.mod_mod in e0 at 1; try (unfold N; omega).
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
      + destruct (Loc.eq_dec (Loc.add (fst e) 1) (Loc.add (fst e) 1)).
        * repeat split; try now simpl.
        * destruct n0.
          reflexivity.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (-1)) 1)).
      + repeat split; try now simpl.
      + destruct n.
        unfold Loc.add.
        rewrite Zdiv.Zplus_mod_idemp_l.
        unfold Loc.eq; rewrite Z.mod_mod; try omega.
        replace (fst e + -1 + 1)%Z with (fst e + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (fst e + 1 - 1)%Z with (fst e + 0)%Z by omega.
        assert (fst e + 0 = fst e)%Z.
        omega.
        rewrite H.
        reflexivity.
        generalize n_sup_1.
        unfold def.n; omega.
  Qed.
  
  Lemma NoAutoLoop : forall e, ~Veq (src e) (tgt e).
  Proof.
    intros e.
    intros Hf.
    unfold src, tgt in Hf.
    destruct (snd e).
    + unfold Veq in *.
      unfold Loc.eq, Loc.add in *.
      unfold def.n in *.
      generalize n_sup_1; intro ns1.
      rewrite Z.mod_mod in *; try omega.
      rewrite <- Zdiv.Zplus_mod_idemp_l in Hf.
      destruct (Z.compare (fst e mod Z.of_nat n + 1)%Z (Z.of_nat n)) eqn : Heq;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *;
        simpl in *; try omega.
      rewrite Heq in Hf; rewrite Z.mod_same in Hf; try omega.
      rewrite Z.mod_small with (a := (fst e mod Z.of_nat n + 1)%Z) in Hf.      
      omega.
      split; try omega.
      generalize Zdiv.Z_mod_lt.
      intros Ho.
      specialize (Ho (fst e) (Z.of_nat n)).
      omega.
      generalize Zdiv.Z_mod_lt.
      intros Ho.
      specialize (Ho (fst e) (Z.of_nat n)).
      assert (Z.of_nat n > 0)%Z.
      omega.
      specialize (Ho H); clear H.
      omega.
    + unfold Veq in Hf; generalize neq_a_a1 ; intros Hn.
      specialize (Hn (fst e)).
      destruct Hn.
      unfold Loc.eq, Loc.add in *.
      rewrite Z.mod_mod in Hf.
      replace (fst e + -1)%Z with (fst e - 1)%Z in Hf by omega.
      assumption.
      unfold def.n; generalize n_sup_1; omega.
  Qed.


  Lemma find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Proof.
    intros a b; split; unfold find_edge; destruct (Loc.eq_dec a (Loc.add b 1)).
    - intros Hnone.
      discriminate.
    - destruct (Loc.eq_dec (Loc.add a 1) b); try discriminate.
      intros Hnone.
      clear Hnone.
      intros e (Hsrc, Htgt).
      unfold Veq, Loc.eq, Loc.add, src, tgt in *.
      destruct (snd e).
      + rewrite <- Htgt in n0.
        destruct n0.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l with (a := (fst e)).
        rewrite Hsrc.
        rewrite Zdiv.Zplus_mod_idemp_l.
        reflexivity.
      + destruct n.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l.
        rewrite <- Hsrc, <- Htgt.
        unfold Loc.add.
        try repeat rewrite Z.mod_mod, Zdiv.Zplus_mod_idemp_l.
        rewrite Zdiv.Zplus_mod_idemp_l.
        replace (fst e + -1 + 1)%Z with (fst e + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (fst e + 1 - 1)%Z with (fst e + 0)%Z by omega.
        assert (fst e + 0 = fst e)%Z.
        omega.
        rewrite H.
        reflexivity.
        unfold def.n; generalize n_sup_1; omega.
    - intros He.
      specialize (He (a, Backward)).
      destruct He.
      split; unfold Veq, src, tgt; simpl.
      reflexivity.
      rewrite e.
      unfold Loc.add.
      rewrite Zdiv.Zplus_mod_idemp_l.
      replace (b + -1 + 1)%Z with (b + 1 + -1)%Z by omega. 
      rewrite Z.add_opp_r with (m := 1%Z).
      replace (b + 1 - 1)%Z with (b + 0)%Z by omega.
      assert (b + 0 = b)%Z.
      omega.
      rewrite H.
      unfold Loc.eq; rewrite Z.mod_mod.
      reflexivity.
      unfold def.n; generalize n_sup_1; omega.
    - intros Ho.
      destruct (Loc.eq_dec (Loc.add a 1) b).
      specialize (Ho (a, Forward)).
      destruct Ho.
      split; unfold src, tgt, Veq, Loc.add, Loc.eq in *; try (rewrite e); simpl.
      reflexivity.
      rewrite e.
      reflexivity.
      reflexivity.
  Qed.

  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
    intros v1 v2 Hv12 v3 v4 Hv34. 
    unfold Eeq, find_edge; simpl.
    destruct (Loc.eq_dec v1 (Loc.add v3 1)),
             (Loc.eq_dec v2 (Loc.add v4 1)).
    simpl.
    repeat split; try reflexivity. assumption.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv12, <- Zdiv.Zplus_mod_idemp_l, Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv12, <- Zdiv.Zplus_mod_idemp_l, <- Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (Loc.add v1 1) v3),
    ( Loc.eq_dec (Loc.add v2 1) v4).
    simpl.
    now split.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv34, <- Zdiv.Zplus_mod_idemp_l, Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv34, <- Zdiv.Zplus_mod_idemp_l, <- Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    simpl; now split.
  Qed.

  Lemma find2st : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) ->
                                Veq v1 (src e) /\ Veq v2 (tgt e).  
  Proof.
    intros v1 v2 e Hsome.
    unfold find_edge in *.
    destruct (Loc.eq_dec v1 (Loc.add v2 1)).
    simpl in *.
    rewrite <- Hsome.
    unfold src, tgt.
    simpl.
    split; try reflexivity.
    rewrite e0.
    unfold Loc.add, Veq, Loc.eq.
    rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod.
    replace (v2 + 1 + -1)%Z with v2 by omega.
    reflexivity.
    unfold def.n; generalize n_sup_1; omega.
    destruct (Loc.eq_dec (Loc.add v1 1) v2).
    simpl in *.
    rewrite <- Hsome; simpl.
    split; try reflexivity.
    rewrite e0.
    reflexivity.
    contradiction.
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

Module DGF_G := DGF (MakeRing)(N)(Names)(LocationA)(ConfigA).

Module AGF_G := AGF (MakeRing)(N)(Names)(LocationA)(ConfigA).



