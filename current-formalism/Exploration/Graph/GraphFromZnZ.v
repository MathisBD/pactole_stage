(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
   T. Balabonski, R. Pelle, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
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
Require Import Pactole.FiniteGraphFormalism.



Set Implicit Arguments.
(** In a ring, an edge with a fixed source is characterized by one of these three directions. *)
Inductive direction := Forward | Backward | AutoLoop.

Module MakeRing <: FiniteGraphDef.
   
  Parameter n : nat.
  Axiom n_sup_1 : 1 < n.
  Definition V := Fin.t n.

  Open Scope Z_scope.
(** ** Vertices *)
  
  (** [V2Z] is a function to pass from a vertex to an integer. *)
  Definition V2Z (v : V): Z := ((Z.of_nat (proj1_sig (Fin.to_nat v))) mod Z.of_nat n)%Z.

  Definition Veq v1 v2 := (V2Z v1) mod Z.of_nat n =  (V2Z v2) mod Z.of_nat n.

   Instance V2Z_compat : Proper (Veq ==>
                                    (fun x y => x mod Z.of_nat n = y mod Z.of_nat n))
                                    V2Z.
  Proof.
    intros v1 v2 Hv.
    now unfold Veq in *.
  Qed.  
  
  (* the following lemmas are used to easily prove that 
           (Z.to_nat (l mod Z.of_nat n)) = (l mod Z.of_nat n) *)
  Lemma Loc_sup_0 : forall l : Z, (0 <= l mod Z.of_nat n)%Z.
  Proof.
    intros;
      try apply Zdiv.Z_mod_lt; generalize n_sup_1; intro Hn.
    rewrite <- Nat2Z.inj_0; apply inj_gt.
    omega.
  Qed.
  
  Lemma Loc_inf_n (l : Z): (Z.to_nat (l mod Z.of_nat n)%Z < n)%nat.
  Proof.
    intros; try apply Zdiv.Z_mod_lt; generalize n_sup_1; intro Hn.
    rewrite <- Nat2Z.id, <- Z2Nat.inj_lt;
    try (apply Zdiv.Z_mod_lt;
    rewrite <- Nat2Z.inj_0; apply inj_gt;
    omega).
    omega.
  Qed.

  
  (** A function to pass a integer to a vertex. *)
  Definition Z2V (l : Z) : V := (Fin.of_nat_lt (Loc_inf_n l)).



  Lemma loc_fin : forall l, (l mod Z.of_nat n = (V2Z (Z2V l)))%Z.
  Proof.
    intros.
    unfold V2Z, Z2V.
    rewrite Fin.to_nat_of_nat.
    simpl.
    rewrite Z2Nat.id.
    rewrite Z.mod_mod.
    reflexivity.
    generalize n_sup_1; omega.
    apply Zdiv.Z_mod_lt.
    generalize n_sup_1; omega.
  Qed.


  (* a simplifying lemma *)
  Lemma fin_loc : forall v, Veq v (Z2V (V2Z v)).
  Proof.
    intros.
    unfold Veq.
    rewrite <-loc_fin, Z.mod_mod.
    reflexivity.
    generalize n_sup_1; omega.
  Qed.
 

  Instance Z2V_compat : Proper ((fun x y => x mod Z.of_nat n = y mod Z.of_nat n)
                                  ==> Veq) Z2V.
  Proof.
    intros l1 l2 Hl.
    unfold Veq.
    rewrite <- 2 loc_fin.
    rewrite 2 Z.mod_mod; try (generalize n_sup_1; omega).
  Qed.
  

  

  
  Lemma Veq_equiv : Equivalence Veq.
  Proof.
    unfold Veq.
    split.
    - now intro v.
    - now intros v1 v2 Hv.
    - intros v1 v2 v3 Hv1 Hv3. now transitivity (V2Z v2 mod Z.of_nat n).
  Qed.

 Lemma Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Proof.
    unfold V, Veq. intros. apply Z_eq_dec.
  Qed.

  (** The module representing the ring, using the vertices as positions. *)
  Module Loc <: DecidableType.
    Definition t := V.
  Definition eq := Veq.
  Definition eq_dec : forall x y, {eq x y} + {~eq x y} := Veq_dec.
  Instance eq_equiv : Equivalence eq := Veq_equiv.
  
  Definition origin :=
    Z2V (0 mod Z.of_nat n).
  Definition add (x y : t) :=
    Z2V (((V2Z x) + (V2Z y)) mod Z.of_nat n).
  Definition mul (x y : t) :=
    Z2V ((Z.mul (V2Z x) (V2Z y)) mod Z.of_nat n).
  Definition unit :=
    Z2V (1 mod Z.of_nat n).
  Definition opp (x : t) :=
    Z2V (((Z.of_nat n) - (V2Z x)) mod Z.of_nat n).



  Instance add_compat : Proper (eq ==> eq ==> Veq) add.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold eq, Veq, add in *.
    rewrite <- 2 loc_fin.
    rewrite 4 Z.mod_mod; try (now generalize n_sup_1; lia);
    now rewrite Zdiv.Zplus_mod, Hx, Hy, <- Zdiv.Zplus_mod. 
  Qed.

  Instance mul_compat : Proper (eq ==> eq ==> Veq) mul.
  Proof.
    intros x1 x2 Hx y1 y2 Hy.
    unfold eq, Veq, mul in *.
    rewrite <- 2 loc_fin.
    rewrite 4 Z.mod_mod; try (now generalize n_sup_1; lia);
      now rewrite Zdiv.Zmult_mod, Hx, Hy, <- Zdiv.Zmult_mod.
  Qed.

  Instance opp_compat : Proper (eq ==> Veq) opp.
  Proof.
    intros x y Hxy.
    unfold eq, Veq, opp in *.
    rewrite <- 2 loc_fin.
    rewrite 4 Z.mod_mod; try (now generalize n_sup_1; lia);
      now rewrite Zdiv.Zminus_mod, Hxy, <- Zdiv.Zminus_mod.
  Qed.

  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof.
    intros.
    unfold add, opp, origin.
    repeat rewrite <- loc_fin.
    rewrite 2 Zdiv.Zplus_mod_idemp_r.
    replace (V2Z u + (Z.of_nat n - V2Z u)) with (Z.of_nat n) by omega.
    rewrite Zdiv.Z_mod_same_full;
      reflexivity.
  Qed.

  Lemma add_assoc: forall x y z, eq (add x (add y z)) (add (add x y) z).
  Proof.
    intros.
    unfold eq, Veq, add.
    repeat rewrite <- loc_fin.
    repeat rewrite Zdiv.Zplus_mod_idemp_l;
      repeat rewrite Zdiv.Zplus_mod_idemp_r.    
    replace(V2Z x + (V2Z y + V2Z z)) with ( V2Z x + V2Z y + V2Z z) by omega.
      reflexivity.
  Qed.

  Lemma add_comm: forall x y, eq (add x y) (add y x).
  Proof.
    intros. unfold add. apply fast_Zplus_comm. reflexivity.
  Qed.

  Lemma add_opp' : forall u, eq (add (opp u) u) origin.
  Proof.
    intros;
      unfold eq, Veq.
      rewrite add_comm.
      apply add_opp.
  Qed.

  Lemma add_origin: forall x, eq (add x origin) x.
  Proof.
    intros;
      unfold add, origin, eq, Veq.
    repeat rewrite <- loc_fin.
    rewrite Z.mod_0_l; repeat rewrite Z.mod_mod;
      try (now generalize n_sup_1; lia).
    now replace (V2Z x + 0) with (V2Z x) by omega.
  Qed.
  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof.
    intros.
    apply add_compat in H.
    specialize (H (opp w) (opp w) (reflexivity _)). 
    unfold Veq in H.
    rewrite 2 (add_comm _ (opp _)), 2 (add_assoc (opp _) _) in H.
    rewrite 2 (add_compat (add_opp' w) (reflexivity _)) in H.
    do 2 rewrite add_comm, add_origin in H.
    apply H.
  Qed.
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v))
                                       (add (opp u) (opp v)).
  Proof.
    intros. unfold eq, Veq, opp, add.
    repeat rewrite <- loc_fin.
    repeat rewrite Zdiv.Zminus_mod_idemp_r.
    repeat rewrite <- Zdiv.Zminus_mod_idemp_l with (a:= Z.of_nat n), Zdiv.Z_mod_same_full.
    rewrite <- 2 Zdiv.Zplus_mod.
    simpl.
    rewrite 4 Z.mod_mod; try (now generalize n_sup_1; lia).
    f_equiv. omega.
Qed.  
 
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof.
    intros.
    unfold eq, Veq, opp.
    repeat rewrite <- loc_fin.
     rewrite <- Zdiv.Zminus_mod_idemp_l, Zdiv.Z_mod_same_full.
     rewrite <- Zdiv.Zminus_mod_idemp_l with (a:= Z.of_nat n), Zdiv.Z_mod_same_full.
     rewrite 2 Z.mod_mod;
       try (now generalize n_sup_1; lia).
     repeat rewrite Zdiv.Zminus_mod_idemp_r. 
     now replace (0-(0- V2Z u)) with (V2Z u) by omega.
  Qed.
  
End Loc.
(** ** Edges *) 

  Definition dir := direction. 

  (** An edge is starting from a node, and has a direction. To simulate a non oriented edge, the considered edge has to be replicated in the opposite direction. *)
  Definition E := (V * dir)%type.
    
  Definition tgt (e:E) : V:= let t :=
                              match snd e with
                              | Forward => Loc.add (fst e) (Z2V 1)
                              | Backward => Loc.add (fst e) (Z2V (-1))
                              | AutoLoop => (fst e)
                              end
                          in t.
  Definition src (e:E) : V := (fst e).

  Parameter threshold : E -> R.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  

  Definition Eeq (e1 e2 : E) := Veq (fst e1) (fst e2)
                                /\ if (Nat.eq_dec n 2)
                                   then
                                     match snd e1, snd e2 with
                                     | AutoLoop, AutoLoop => True
                                     | AutoLoop, _ | _, AutoLoop  => False
                                     | _, _ => True
                                     end
                                   else
                                     snd e1 = snd e2.
  
  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.
  
  
  Lemma Eeq_equiv : Equivalence Eeq.
  Proof.
    split.
    + intros e.
      unfold Eeq.
      destruct (Nat.eq_dec n 2);
      try destruct (snd e);
      repeat split; reflexivity.
    + intros e1 e2 (Hes, Het).
      unfold Eeq.
      destruct (Nat.eq_dec n 2);
        try destruct (snd e1), (snd e2);
        (try now exfalso);
        try (repeat split; now symmetry).
    + intros e1 e2 e3 (Hs12, Ht12) (Hs23, Ht23). 
      unfold Eeq.
      destruct (Nat.eq_dec n 2);
      try destruct (snd e1), (snd e2), (snd e3);
        (try now exfalso);
      try (repeat split; unfold Veq in *; now rewrite Hs12, Hs23).
  Qed.

  Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Proof.
    intros e1 e2 He.
    unfold Eeq in He.
    unfold tgt.
    destruct He as (Ht, Hd); unfold src, Loc.add in *.
    destruct (Nat.eq_dec n 2).
    - destruct (snd e1), (snd e2); try (now exfalso);
      unfold Veq in *;
      repeat rewrite <- loc_fin;
      try now rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod.
      rewrite e in *.
      replace (-1) with (0 - 1) by lia.
      rewrite <- (Z.mod_same (Z.of_nat 2)).
      rewrite Zdiv.Zminus_mod_idemp_l.
      simpl in *.
      now rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod.
      lia.
      rewrite e in *.
      replace (-1) with (0 - 1) by lia.
      rewrite <- (Z.mod_same (Z.of_nat 2)).
      rewrite Zdiv.Zminus_mod_idemp_l.
      simpl in *.
      now rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod.
      lia.
      assumption.
    - rewrite Hd; destruct (snd e2).
      unfold Veq in *;
        repeat rewrite <- loc_fin.
      rewrite Z.mod_1_l; repeat rewrite Z.mod_mod; try (now generalize n_sup_1; lia).
      rewrite 2 (Zdiv.Zplus_mod _ 1).
      now rewrite Ht.
      now rewrite 2 (Zdiv.Zplus_mod (V2Z _) _), Ht.
      assumption.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof.
    intros e1 e2 He.
    now unfold Eeq in He.
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
    destruct (Nat.eq_dec n 2).
    destruct (snd e), (snd e'), (Veq_dec (fst e) (fst e')); intuition.
    destruct (Veq_dec (fst e) (fst e')),
    (dir_eq_dec (snd e) (snd e')); intuition.
  Qed.

  Definition find_edge v1 v2 := if Loc.eq_dec (v1) (Loc.add (v2) (Z2V 1)) then
                                  Some (v1, Backward)
                                else
                                  if Loc.eq_dec (Loc.add (v1) (Z2V 1)) (v2) then
                                    Some (v1, Forward)
                                  else
                                    if Loc.eq_dec (v1) (v2) then
                                      Some (v1, AutoLoop)
                                    else
                                      None.

 
    
  Lemma find_edge_Some : forall e :E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof.
    intros.
    unfold find_edge, Eeq, src, tgt, opt_eq, Veq in *.
    destruct (Nat.eq_dec n 2), (snd e) eqn : Hdir.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (Z2V 1)) (Z2V 1))).
      + simpl.
        now split.
      + destruct (Loc.eq_dec (Loc.add (fst e) (Z2V 1)) (Loc.add (fst e) (Z2V 1))).
        * simpl.
          now split.
        * now destruct n1.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (Z2V (-1))) (Z2V 1))).
      + now simpl.
      + destruct n0.
        rewrite <- Loc.add_assoc.
        unfold Loc.add at 2.
        repeat rewrite <- loc_fin.
        rewrite e0; simpl.
        rewrite Z.mod_same; try lia.
        rewrite <- (Z.mod_0_l (Z.of_nat n)); try lia.
        fold Loc.origin.
        now rewrite Loc.add_origin.
    - destruct ( Loc.eq_dec (fst e) (Loc.add (fst e) (Z2V 1))).
      + simpl.
        unfold Loc.eq, Loc.add, Veq in *; repeat rewrite <- loc_fin in e1.
        rewrite e0 in e1; simpl in *.
        rewrite 2 Z.mod_mod, Z.mod_1_l in e1; try lia.
        rewrite 2 Zdiv.Zmod_even in e1.
        rewrite Z.even_add in e1.
        now destruct (Z.even (V2Z (fst e)))eqn : Hv; try rewrite Hv in *; simpl in *.
      + destruct (Loc.eq_dec (Loc.add (fst e) (Z2V 1)) (fst e)).
        * now destruct n0.
        * destruct (Loc.eq_dec (fst e) (fst e)); try now simpl in *.
          now destruct n2.
    - destruct ( Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (Z2V 1)) (Z2V 1))).
      + assert (H2n : 2 < Z.of_nat n) by (generalize n_sup_1; lia).
        exfalso.
        unfold Loc.eq, Veq, Loc.add in e0.
        rewrite <- 3 loc_fin in e0.
        rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod in e0;
          try (generalize n_sup_1; lia).
        set (X := (V2Z (fst e))%Z) in *; set (N := Z.of_nat n) in *.
        rewrite <- Z.mod_mod in e0 at 1; try (omega).
        rewrite Zdiv.Zplus_mod_idemp_l in e0.
        rewrite Z.mod_1_l in e0; try (generalize n_sup1; lia).
        replace (X+1+1)%Z with (X + (1 + 1))%Z in e0 by omega.
        rewrite <- Zdiv.Zplus_mod_idemp_l in e0.
        generalize Zdiv.Z_mod_lt; intros Hlt;
          specialize (Hlt X N); destruct Hlt as (Hl0, HlN); try (omega).
        destruct (Z.compare (X mod N + 2) N) eqn : Heq;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *;
        simpl in *.
        * rewrite Heq in e0.
          rewrite Z.mod_same in e0; try (omega).
          replace (X mod N)%Z with (N - 2)%Z in e0 by omega.
          rewrite <- Zdiv.Zminus_mod_idemp_l in e0; try (omega).
          rewrite Z.mod_same in e0; try (omega).
          simpl in *.
          apply Zdiv.Z_mod_zero_opp_full in e0.
          simpl in e0.
          rewrite Z.mod_small in e0; try (lia).
        * rewrite Z.mod_small in e0; try omega.
          rewrite 2 Z.mod_small with (a := (X mod N + 2)%Z) in e0; try omega.
        * assert (X mod N = N - 1)%Z.
          destruct (Z.compare (X mod N + 1)%Z N) eqn : Heq_1;
            try rewrite Z.compare_lt_iff in *;
            try rewrite Z.compare_eq_iff in *;
            try rewrite Z.compare_gt_iff in *; try omega.
          rewrite H in *.
          replace (N - 1 + 2)%Z with (N + 1) %Z in e0 by omega.
          rewrite Z.mod_small, <- Zdiv.Zplus_mod_idemp_l, Z.mod_same in e0;
            try (omega).
          simpl in e0.
          rewrite 2 Z.mod_1_l in e0; try (omega).
        * omega.
          
      + destruct (Loc.eq_dec (Loc.add (fst e) (Z2V 1)) (Loc.add (fst e) (Z2V 1))).
        * repeat split; try now simpl.
        * destruct n2.
          reflexivity.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (Z2V (-1))) (Z2V 1))).
      + repeat split; try now simpl.
      + destruct n1.
        rewrite <- Loc.add_assoc.
        assert (Loc.eq (Loc.add (Z2V (-1)) (Z2V 1)) Loc.origin).
        { unfold Loc.eq, Loc.add, Veq, Loc.origin.
          repeat rewrite <- loc_fin.
          rewrite <- Zdiv.Zplus_mod.
          now simpl.
        }
        now rewrite H, Loc.add_origin.
    - destruct (Loc.eq_dec (fst e) (Loc.add (fst e) (Z2V 1))).
      simpl.
      unfold Loc.eq, Veq, Loc.add in *; exfalso; rewrite <- 2 loc_fin in e0.
      generalize n_sup_1.
      intros.
      rewrite Z.mod_1_l in *; try omega.
      rewrite 2 Z.mod_mod, <- Zdiv.Zplus_mod_idemp_l in *; try omega.
      destruct ((V2Z (fst e)) mod Z.of_nat n ?= Z.of_nat n) eqn : Hn;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *.
      + rewrite Hn, <- Zdiv.Zplus_mod_idemp_l, Zdiv.Z_mod_same_full in *.
        simpl in *;  rewrite Z.mod_1_l in *;
          omega.
      + destruct (V2Z (fst e) mod Z.of_nat n) eqn : Hp.
        * simpl in *.
          rewrite Z.mod_1_l in *; omega.
        * apply Zlt_le_succ in Hn.
          unfold Z.succ in Hn.
          apply Zle_lt_or_eq in Hn.
          destruct Hn.
          rewrite Zdiv.Zmod_small in e0; try split; try omega.
          apply Zle_0_pos.
          rewrite Z.add_comm, H0, Zdiv.Z_mod_same_full in *.
          generalize Zle_0_pos.
          omega.
        * assert (Hn0: 0 < Z.of_nat n) by omega.
          generalize (Z.mod_pos_bound (V2Z (fst e)) (Z.of_nat n) Hn0); intros.
          rewrite Hp in H0.
          generalize (Pos2Z.neg_is_neg p).
          omega.
      + assert (Hn0: 0 < Z.of_nat n) by omega.
        generalize (Z.mod_pos_bound (V2Z (fst e)) (Z.of_nat n) Hn0); intros.
        omega.
      + destruct (Loc.eq_dec (Loc.add (fst e) (Z2V 1)) (fst e)); try now destruct n1.
        destruct (Loc.eq_dec (fst e) (fst e)). 
        now split.
        now destruct n3.
  Qed.
  
  Lemma find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Proof.
    intros a b; split; unfold find_edge;
      destruct (Loc.eq_dec (a) (Loc.add (b) (Z2V 1))).
    - intros Hnone.
      discriminate.
    - destruct (Loc.eq_dec (Loc.add (a) (Z2V 1)) (b)); try discriminate.
      destruct (Loc.eq_dec (a) (b)); try discriminate.
      intros _.
      intros e (Hsrc, Htgt).
      unfold Loc.eq, Veq, Loc.add, src, tgt in *.
      rewrite <- loc_fin in *.
      destruct (snd e).
      + rewrite <- Htgt in n1.
        destruct n1.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l with (a := V2Z (fst e)).
        rewrite Hsrc.
        repeat rewrite <- loc_fin.
        rewrite Zdiv.Zplus_mod_idemp_l, 2 Z.mod_mod;
          generalize n_sup_1; lia.
      + destruct n0.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l.
        rewrite <- Hsrc, <- Htgt.
        unfold Loc.add.
        repeat rewrite <-loc_fin.
        try repeat rewrite Z.mod_mod; repeat rewrite Zdiv.Zplus_mod_idemp_l;
          try (generalize n_sup_1; omega).
        rewrite Zdiv.Zplus_mod.
        rewrite 3 Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l.
        now replace (V2Z (fst e) + -1 + 1)%Z with (V2Z (fst e))%Z by lia. 
      + now destruct n2; repeat rewrite <- loc_fin in *;
          rewrite <- Hsrc, <- Htgt.
    - intros He.
      specialize (He (a, Backward)).
      destruct He.
      split; unfold Loc.eq, Veq, src, tgt; simpl.
      reflexivity.
      unfold Loc.eq, Veq, src, tgt, Loc.add in *; simpl.
      repeat rewrite <- loc_fin in *.
      rewrite <- Zdiv.Zplus_mod_idemp_l, e.
      repeat rewrite Zdiv.Zplus_mod_idemp_l.
      rewrite Zdiv.Zplus_mod.
      rewrite 3 Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l.
      repeat rewrite Z.mod_mod; try (now generalize n_sup_1; lia).
      now replace (V2Z b + 1 + -1)%Z with (V2Z b)%Z by lia. 
    - intros Ho.
      destruct (Loc.eq_dec (Loc.add (a) (Z2V 1)) (b)).
      specialize (Ho (a, Forward)).
      destruct Ho.
      split; unfold src, tgt, Veq. now unfold fst.
      unfold Loc.eq in *.
      simpl.
      apply e.
      destruct (Loc.eq_dec (a) (b)).
      specialize (Ho (a,AutoLoop)).
      destruct Ho; simpl.
      split; try easy.
      reflexivity.
  Qed.

  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
    intros v1 v2 Hv12 v3 v4 Hv34. 
    unfold Eeq, find_edge; simpl.
    destruct (Loc.eq_dec (v1) (Loc.add (v3) (Z2V 1))),
             (Loc.eq_dec (v2) (Loc.add (v4) (Z2V 1))).
    simpl.
    repeat split; try (destruct (Nat.eq_dec n 2); reflexivity). assumption.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv12, <- Zdiv.Zplus_mod_idemp_l, Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv12, <- Zdiv.Zplus_mod_idemp_l, <- Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (Loc.add (v1) (Z2V 1)) (v3)),
    ( Loc.eq_dec (Loc.add (v2) (Z2V 1)) (v4)).
    simpl.
    now destruct (Nat.eq_dec n 2); split.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv34, <- Zdiv.Zplus_mod_idemp_l, Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv34, <- Zdiv.Zplus_mod_idemp_l, <- Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (v1) (v3)), (Loc.eq_dec (v2) (v4)).
    simpl; try destruct (Nat.eq_dec n 2); now split.
    destruct n3. unfold Loc.eq, Veq in *. now rewrite Hv12, Hv34 in e.
    destruct n3. unfold Loc.eq, Veq in *; now rewrite <- Hv12, <- Hv34 in e.
    now split.
  Qed.
  
  Lemma find2st : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) ->
                                Veq v1 (src e) /\ Veq v2 (tgt e).  
  Proof.
    intros v1 v2 e Hsome.
    assert (Z.of_nat n <> 0%Z).
    generalize n_sup_1; omega.
    unfold find_edge in *.
    destruct (Loc.eq_dec (v1) (Loc.add (v2) (Z2V 1))).
    simpl in *.
    unfold Eeq, Loc.eq, Veq, src, tgt in *.
    destruct (Nat.eq_dec n 2) in Hsome.
    - simpl in *.
      destruct (snd e);
      split; destruct Hsome; try easy;
      rewrite (Loc.add_compat (symmetry H0) (reflexivity _));
      rewrite (Loc.add_compat e0 (reflexivity _));
      unfold Loc.add; repeat rewrite <- loc_fin, e1;
      repeat rewrite Zdiv.Zplus_mod_idemp_l;
        repeat rewrite Zdiv.Zplus_mod_idemp_r;
      repeat rewrite Z.mod_mod; try lia;
      simpl;
      rewrite Z.mod_1_l; try lia.
      replace (V2Z v2 + 1+1) with (V2Z v2 + 2) by lia.
      rewrite <- Zdiv.Zplus_mod_idemp_r, Z.mod_same; try now f_equiv; lia.
      f_equiv; lia.
    - destruct Hsome as (Hsomef,Hsomes); rewrite <- Hsomes, <- Hsomef.
      simpl in *.
      split; try reflexivity.
      unfold Loc.add.
      repeat rewrite <- loc_fin.
      rewrite <- Zdiv.Zplus_mod_idemp_l.
      rewrite <- Hsomef, e0.
      rewrite Zdiv.Zplus_mod_idemp_l.
      unfold Loc.add, Veq, Loc.eq, Loc.add.
      repeat rewrite <- loc_fin.
      rewrite 2 Zdiv.Zplus_mod_idemp_r.
      rewrite 2 Zdiv.Zplus_mod_idemp_l.
      rewrite 2 Z.mod_mod; try omega.
      f_equiv; lia.
    - destruct (Loc.eq_dec (Loc.add (v1) (Z2V 1)) (v2)).
      simpl in *.
      unfold src, tgt.
      destruct Hsome as (Hsomef,Hsomes). simpl in *.
      destruct (snd e).
      rewrite Hsomef in *.
      split; try now symmetry.
      rewrite Hsomef in *.
      destruct (Nat.eq_dec n 2); try discriminate.
      unfold Loc.add in *;
      rewrite <- e0.
      split; try easy.
      unfold Veq; repeat rewrite <- loc_fin.
      rewrite e1 in *.
      simpl.
      replace (-1 mod 2) with (1 mod 2).
      reflexivity.
      replace (-1 mod 2) with ((0 - 1) mod 2).
      rewrite <- (Z.mod_same 2), Zdiv.Zminus_mod_idemp_l.
      now simpl.
      lia.
      now simpl.
      destruct (Nat.eq_dec n 2); try easy.
      destruct (Loc.eq_dec (v1) (v2)).
      cbn in *.
      destruct Hsome as (Hsomef,Hsomes).
      simpl in *.
      unfold src, tgt.
      destruct (snd e);
        try now destruct (Nat.eq_dec n 2).
      rewrite e0 in *; now split.
      contradiction.
  Qed.
    
End MakeRing.

(** A decidable type created from the ring *)
Module LocationA : LocationADef (MakeRing).
  Definition t := MakeRing.V.
  Definition eq := MakeRing.Veq.
  Definition eq_equiv : Equivalence eq := MakeRing.Veq_equiv.
  Definition eq_dec : forall l l' : t, {eq l l'} + {~eq l l'} := MakeRing.Veq_dec.
End LocationA.






