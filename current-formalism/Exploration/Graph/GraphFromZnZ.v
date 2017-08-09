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
Require Import Pactole.DiscreteSpace.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.FiniteGraphFormalism.
Set Implicit Arguments.


(* On a un espace V/E qui représente un graphe.
   On veux transposer Z/nZ sur un graphe V/E.
   Apres on veux utiliser ConfigA2D pour avoir un graph continu.
   pourquoi V/E <=> Z/nZ?
    - Z/nZ représente un anneau donc un graphe.
    - V c'est tout les entiers entre 0 et n
    - E c'est entre les nombres qui se suivent. *)

(** In a ring, an edge with a fixed source is characterized by one of these three directions. *)
Inductive direction := Forward | Backward | AutoLoop.

Module MakeRing (Import Def : DiscreteSpace.RingDef) <: FiniteGraphDef
    with Definition n := Def.n (* ring size *)
    with Definition V := {m : nat | m < Def.n} (* set of nodes *)
    with Definition E := (({m : nat | m < Def.n} * direction)%type). (* set of edges *)
  
  Definition n := n.
  Definition V := {m : nat | m < n}.
  
  (* to_Z is a function to pass from a node as in a finite set to a integer, 
     which can be easily computate *)
  Definition to_Z (v : V): Z := Z.of_nat (proj1_sig v).
  
  Definition dir := direction.
  
  Definition E := (V * dir)%type.
  Definition Veq := @Logic.eq V.
  
  Instance to_Z_compat : Proper (Veq ==> Z.eq) to_Z.
  Proof. unfold Veq. repeat intro. now subst. Qed.
  
  (* the following lemmas are used to easily prove that 
           (Z.to_nat (l mod Z.of_nat n)) = (l mod Z.of_nat n) *)
  Lemma to_Z_sup_0 : forall l : Z, (0 <= l mod Z.of_nat n)%Z.
  Proof.
  intros.
  apply Zdiv.Z_mod_lt; assert (Hn := n_sup_1).
  rewrite <- Nat2Z.inj_0; apply inj_gt.
  unfold n. omega.
  Qed.
  
  Lemma to_Z_inf_n (l : Z): Z.to_nat (l mod Z.of_nat n)%Z < n.
  Proof.
  intros.
  rewrite <- Nat2Z.id, <- Z2Nat.inj_lt;
  try apply Zdiv.Z_mod_lt;
  assert (Hn := n_sup_1); unfold n in *; omega.
  Qed.
  
  Lemma to_Z_injective : injective Veq Z.eq to_Z.
  Proof.
  intros [x Hx] [y Hy] Heq.
  unfold to_Z in Heq. hnf in Heq |- *. simpl in Heq.
  apply Nat2Z.inj in Heq. subst. f_equal. apply le_unique.
  Qed.
  
  (* a function to pass a integer to a finit set *)
  Definition of_Z (l : Z) : V := exist _ (Z.to_nat (l mod Z.of_nat n)) (to_Z_inf_n l).
  
  Lemma Z2Z : forall l, (to_Z (of_Z l) = l mod Z.of_nat n)%Z.
  Proof.
  intros. unfold to_Z, of_Z. simpl.
  rewrite Z2Nat.id; trivial; [].
  apply Z.mod_pos_bound. generalize n_sup_1; unfold n; omega.
  Qed.
  
  Instance of_Z_compat : Proper (Z.eq ==> Veq) of_Z.
  Proof. intros l1 l2 Hl. hnf. now rewrite Hl. Qed.
  
  Lemma V2V : forall v, Veq (of_Z (to_Z v)) v.
  Proof.
  intros [k Hk]. hnf. unfold to_Z, of_Z. apply eq_proj1. simpl.
  rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; omega.
  Qed.
  
  Definition src (e : E) : V := (fst e).
  
  Definition tgt (e : E) : V :=
    let t := match snd e with
               | Forward => (to_Z (fst e) + 1)%Z
               | Backward => (to_Z (fst e) - 1)%Z
               | AutoLoop => to_Z (fst e)
             end
    in of_Z t.
  
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
  
  Instance Veq_equiv : Equivalence Veq := eq_equivalence.
  
  Lemma Eeq_equiv : Equivalence Eeq.
  Proof. unfold Eeq. split.
  + intros e.
    split; try reflexivity; [].
    now repeat destruct_match.
  + intros e1 e2 (Hs, Ht).
    split; try (now symmetry); [].
    revert Ht. repeat destruct_match; auto.
  + intros e1 e2 e3 (Hs12, Ht12) (Hs23, Ht23).
    split; try (now etransitivity; eauto); [].
    revert Ht12 Ht23. repeat destruct_match; auto; congruence.
  Qed.
  
  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof. intros e1 e2 He. apply He. Qed.
  
  Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Proof.
  intros e1 e2 He. apply eq_proj1.
  unfold Eeq, tgt, Veq, to_Z, of_Z in *.
  destruct He as (Ht, Hd). rewrite Ht. clear Ht. revert Hd.
  repeat destruct_match; simpl; intro; try tauto || discriminate; [|];
  destruct (fst e2) as [k ?]; simpl;
  match goal with |H : n = 2 |- _ => rewrite H in *; clear H end;
  destruct k as [| [| k]]; simpl; omega.
  Qed.
  
  Definition Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'} := @subset_dec n.
  
  Lemma dir_eq_dec : forall d d': direction, {d = d'} + {d <> d'}.
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
  
  Definition find_edge v1 v2 :=
    if Veq_dec v1 (of_Z (to_Z v2 + 1)) then Some (v1, Backward) else
    if Veq_dec (of_Z (to_Z v1 + 1)) v2 then Some (v1, Forward)  else
    if Veq_dec v1 v2 then Some (v1, AutoLoop) else None.
  
  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
  intros v1 v2 Hv12 v3 v4 Hv34.
  unfold Eeq, find_edge; simpl.
  repeat destruct_match; simpl; easy || congruence.
  Qed.
  
  Lemma find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Proof.
    assert (Hn : 1 < n) by (generalize Def.n_sup_1; unfold n; omega).
    intros a b; split; unfold find_edge;
    destruct (Veq_dec a (of_Z (to_Z b + 1))) as [Heq_a | Hneq_a].
    - discriminate.
    - destruct (Veq_dec (of_Z (to_Z a + 1)) b) as [Heq_b | Hneq_b],
               (Veq_dec a b); try discriminate.
      intros _ e (Hsrc, Htgt).
      unfold Veq, src, tgt in *.
      destruct (snd e); rewrite Hsrc in Htgt.
      + contradiction.
      + elim Hneq_a. rewrite <- Htgt. rewrite Z2Z. apply eq_proj1.
        unfold of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
        replace (to_Z a - 1 + 1)%Z with (to_Z a) by ring.
        unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; try omega; [].
        apply proj2_sig.
      + now rewrite V2V in Htgt.
    - intros Hedge. elim (Hedge (a, Backward)).
      split; unfold Veq, src, tgt; simpl; try reflexivity; [].
      rewrite Heq_a, Z2Z. apply eq_proj1.
      unfold Z.sub, of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
      replace (to_Z b + 1 + -1)%Z with (to_Z b) by omega.
      unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; omega || apply proj2_sig.
    - intro Hedge. destruct (Veq_dec (of_Z (to_Z a + 1)) b) as [Heq_b | Hneq_b].
      + elim (Hedge (a, Forward)).
        split; unfold Veq, src, tgt; simpl; try reflexivity; [].
        now rewrite <- Heq_b.
      + destruct (Veq_dec a b) as [Heq |]; trivial; [].
        elim (Hedge (a, AutoLoop)).
        split; unfold Veq, src, tgt; simpl; try reflexivity; [].
        now rewrite V2V, Heq.
  Qed.
  
  Lemma find_edge_Some : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) <->
                                Veq v1 (src e) /\ Veq v2 (tgt e).
  Proof.
  assert (Hn : 1 < n) by (generalize Def.n_sup_1; unfold n; omega).
  intros v1 v2 e.
  destruct (find_edge v1 v2) eqn:Hcase.
  * simpl. split; intro Heq.
    + rewrite <- Heq. clear Heq e. unfold find_edge in *.
      revert Hcase. repeat destruct_match; intro Hcase; inv Hcase.
      - unfold tgt. simpl. split; try reflexivity; [].
        revert_all. intro Heq.
        rewrite Heq, Z2Z. apply eq_proj1.
        unfold Veq, of_Z. simpl. rewrite Zdiv.Zminus_mod_idemp_l.
        ring_simplify (to_Z v2 + 1 - 1)%Z.
        unfold to_Z. rewrite Z.mod_small, Nat2Z.id; trivial; [].
        split; apply Zle_0_nat || apply Nat2Z.inj_lt, proj2_sig.
      - unfold tgt. simpl. now split.
      - unfold tgt. simpl. split; try reflexivity; [].
        revert_all. intro Heq. now rewrite Heq, V2V.
    + unfold find_edge in *.
      revert Hcase. repeat destruct_match; intro Hcase; inv Hcase.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd. destruct Heq as [Heq1 Heq2].
        unfold src, tgt in *. destruct (Nat.eq_dec n 2), (snd e); trivial; exfalso; [| |].
        ++ revert Hadd. rewrite Heq2, <- Heq1. hnf. rewrite V2V. intro Hadd.
           apply (f_equal to_Z) in Hadd. revert Hadd. rewrite Z2Z. unfold to_Z.
           destruct v1 as [k Hk]. simpl. clear Heq1 Heq2.
           match goal with H : n = 2 |- _ => rewrite H in * end. clear -Hk.
           destruct k as [| [| k]]; simpl in *.
           -- rewrite Z.mod_small; lia.
           -- rewrite Z.mod_same; lia.
           -- exfalso. omega.
        ++ rewrite Heq2, <- Heq1 in Hadd. hnf in Hadd. rewrite Z2Z in Hadd.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd. clear Heq1 Heq2 e v2.
           unfold of_Z, to_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l, <- Z.add_assoc.
           destruct v1 as [k Hk]. simpl.
           change 2%Z with (Z.of_nat 2). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod; try lia; [].
           destruct (Nat.eq_dec k (n - 1)); [| destruct (Nat.eq_dec k (n - 2))]; subst.
           -- replace (n - 1 + 2) with (1 + 1 * n) by omega. rewrite Nat.mod_add; try lia; [].
              rewrite Nat2Z.id, Nat.mod_1_l; lia.
           -- replace (n - 2 + 2) with n by omega. rewrite Nat.mod_same, Nat2Z.id; lia.
           -- rewrite Nat.mod_small, Nat2Z.id; lia.
        ++ rewrite Heq2, <- Heq1 in Hadd. hnf in Hadd. rewrite Z2Z in Hadd.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd. clear -Hn.
           unfold of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
           destruct v1 as [k Hk]. unfold to_Z. simpl.
           replace (Z.of_nat k + 1)%Z with (Z.of_nat (k + 1)) by lia.
           rewrite <- Zdiv.mod_Zmod, Nat2Z.id; try omega; [].
           destruct (Nat.eq_dec k (n - 1)).
           -- subst. rewrite Nat.sub_add, Nat.mod_same; lia.
           -- rewrite Nat.mod_small; lia.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd.
        destruct Heq as [Heq1 Heq2].
        rewrite Heq2 in Hadd. hnf in Hadd. apply (f_equal to_Z) in Hadd.
        unfold src, tgt in *. destruct (Nat.eq_dec n 2), (snd e); trivial; exfalso; [| |].
        ++ revert Hadd. rewrite <- Heq1, V2V, Z2Z. destruct v1 as [k Hk]. unfold to_Z. simpl.
           match goal with H : n = 2 |- _ => rename H into Heq end.
           clear -Hk Heq. rewrite Heq in *. clear Heq.
           destruct k as [| [| k]]; simpl in *.
           -- rewrite Z.mod_small; lia.
           -- rewrite Z.mod_same; lia.
           -- exfalso. omega.
        ++ rewrite <- Heq1, 2 Z2Z in Hadd. revert Hadd. clear dependent v2. clear Heq1.
           unfold to_Z. destruct v1 as [k Hk]. simpl. change 1%Z with (Z.of_nat 1).
           rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod; try lia; [].
           destruct (Nat.eq_dec k (n - 1)); [| destruct (Nat.eq_dec k 0)]; subst.
           -- replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; try lia; [].
              rewrite <- Nat2Z.inj_sub, <- Zdiv.mod_Zmod, Nat.mod_small; lia.
           -- simpl. change (-1)%Z with (- (1))%Z.
              rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; lia.
           -- rewrite <- Nat2Z.inj_sub, <- Zdiv.mod_Zmod, 2 Nat.mod_small; lia.
        ++ hnf in Hadd. rewrite <- Heq1, V2V, Z2Z in Hadd. clear -Hadd Hn.
           revert Hadd. unfold to_Z. destruct v1 as [k Hk]. simpl.
           change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod; try lia; [].
           intro Hadd. apply Nat2Z.inj in Hadd.
           destruct (Nat.eq_dec k (n - 1)) as [Heq |].
           -- subst. replace (n - 1 + 1) with n in Hadd by omega. rewrite Nat.mod_same in Hadd; lia.
           -- rewrite Nat.mod_small in Hadd; lia.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd. apply (f_equal to_Z) in Hadd. revert Hadd.
        destruct Heq as [Heq1 Heq2]. rewrite Heq1, Heq2. unfold src, tgt, Veq, of_Z, to_Z.
        destruct (Nat.eq_dec n 2), e as [[k Hk] []]; simpl; trivial; clear dependent v1; clear Heq2.
        ++ rewrite Z2Nat.id;
           match goal with H : n = 2 |- _ => rewrite H in *; clear H end;
           destruct k as [| [| k]]; simpl; omega || rewrite Z.mod_same || rewrite Z.mod_small; lia.
        ++ rewrite Z2Nat.id; try (apply Z.mod_pos_bound; lia); [].
           match goal with H : n = 2 |- _ => rewrite H in *; clear H end.
           destruct k as [| [| k]]; simpl; omega || (now rewrite Z.mod_small; lia) || idtac; [].
           change (-1)%Z with (- (1))%Z. rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; lia.
        ++ rewrite Z2Nat.id; try (apply Z.mod_pos_bound; lia); [].
           change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod; try lia; [].
           destruct (Nat.eq_dec k (n - 1)); subst.
           -- replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; lia.
           -- rewrite Nat.mod_small; lia.
        ++ rewrite Z2Nat.id; try (apply Z.mod_pos_bound; lia); [].
           destruct (Nat.eq_dec k 0); subst.
           -- simpl. change (-1)%Z with (- (1))%Z.
              rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; lia.
           -- rewrite Z.mod_small; lia.
  * rewrite find_edge_None in Hcase. simpl. intuition. now apply (Hcase e).
  Qed.
  
  Lemma find_some_edge : forall e : E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof. intro. now rewrite find_edge_Some. Qed.
  
End MakeRing.


Module LocG (Def : DiscreteSpace.RingDef)(Ring : FiniteGraphDef) : LocationAFiniteDef (Ring).
  Definition t := Ring.V.
  Definition eq := Ring.Veq.
  Definition eq_equiv : Equivalence eq := Ring.Veq_equiv.
  Definition eq_dec : forall l l' : t, {eq l l'} + {~eq l l'} := Ring.Veq_dec.
End LocG.
