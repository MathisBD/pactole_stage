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
Require Import Pactole.DiscreteGraphFormalism.
Require Import Pactole.ContinuousDVGraphFormalism.
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

  Definition tgt (e : E) : V :=
    let t := match snd e with
               | Forward => (to_Z (fst e) + 1)%Z
               | Backward => (to_Z (fst e) - 1)%Z
               | AutoLoop => to_Z (fst e)
             end
    in of_Z t.
  Definition src (e : E) : V := (fst e).

  Parameter threshold : E -> R.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.


  Definition Eeq (e1 e2 : E) := Veq (fst e1) (fst e2)
                          /\ snd e1 = snd e2.

  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.

  Instance Veq_equiv : Equivalence Veq := eq_equivalence.

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
  unfold Eeq, tgt, Veq in *.
  destruct He as (Ht, Hd).
  f_equal. rewrite Hd; destruct (snd e2); now rewrite Ht.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof. intros e1 e2 He. apply He. Qed.


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
    destruct (Veq_dec (fst e) (fst e')),
    (dir_eq_dec (snd e) (snd e')); intuition.
  Qed.

  Definition find_edge v1 v2 :=
    if Veq_dec v1 (of_Z (to_Z v2 + 1)) then Some (v1, Backward) else
    if Veq_dec (of_Z (to_Z v1 + 1)) v2 then Some (v1, Forward) else
    if Veq_dec v1 v2 then Some (v1, AutoLoop) else None.

  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
  intros v1 v2 Hv12 v3 v4 Hv34.
  unfold Eeq, find_edge; simpl.
  repeat destruct_match; simpl; easy || congruence.
  Qed.

(*   Set Printing Implicit. *)

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
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ rewrite Heq2, <- Heq1 in Hadd. hnf in Hadd. rewrite Z2Z in Hadd.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd. clear -Hn.
           unfold of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
           (* wrong if n=2 *) admit.
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
        destruct Heq as [Heq1 Heq2]. rewrite Heq2 in Hadd.
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ hnf in Hadd. rewrite <- Heq1 in Hadd. revert Hadd.
           (* wrong if n=2 *) admit.
        ++ hnf in Hadd. rewrite <- Heq1 in Hadd. clear -Hadd Hn.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd.
           unfold of_Z, to_Z. simpl.
           replace (Z.of_nat (proj1_sig v1) + 1)%Z with (Z.of_nat ((proj1_sig v1) + 1)) by lia.
           rewrite <- 2 Zdiv.mod_Zmod, 2 Nat2Z.id; try omega; [].
           destruct (Nat.eq_dec (proj1_sig v1) (n - 1)) as [Heq |].
           -- rewrite Heq, Nat.sub_add, Nat.mod_same, Nat.mod_small; lia.
           -- assert (proj1_sig v1 < n) by apply proj2_sig.
              rewrite 2 Nat.mod_small; lia.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd.
        destruct Heq as [Heq1 Heq2]. rewrite Heq2 in Hadd.
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ hnf in Hadd. rewrite <- Heq1 in Hadd. clear -Hadd Hn.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd.
           unfold of_Z, to_Z. simpl.
           replace (Z.of_nat (proj1_sig v1) + 1)%Z with (Z.of_nat ((proj1_sig v1) + 1)) by lia.
           rewrite <- Zdiv.mod_Zmod, Nat2Z.id; try omega; [].
           destruct (Nat.eq_dec (proj1_sig v1) (n - 1)) as [Heq |].
           -- rewrite Heq, Nat.sub_add, Nat.mod_same; lia.
           -- assert (proj1_sig v1 < n) by apply proj2_sig.
              rewrite Nat.mod_small; lia.
        ++ hnf in Hadd. rewrite <- Heq1 in Hadd. clear -Hadd Hn.
           apply (f_equal (@proj1_sig nat (fun x => lt x n))) in Hadd. revert Hadd.
           unfold of_Z, to_Z. simpl.
           destruct (Nat.eq_dec (proj1_sig v1) 0) as [Heq |].
           -- rewrite Heq. simpl Z.of_nat.
              rewrite <- (Z.mod_same (Z.of_nat n)), Zdiv.Zminus_mod_idemp_l, Z.mod_small; try lia; [].
              change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Nat2Z.id; lia.
           -- assert (proj1_sig v1 < n) by apply proj2_sig.
              rewrite Z.mod_small; try lia; [].
              change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Nat2Z.id; lia.
  * rewrite find_edge_None in Hcase. simpl. intuition. now apply (Hcase e).
  Admitted.

  Lemma find_some_edge : forall e : E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof. intro. now rewrite find_edge_Some. Qed.

End MakeRing.


Module LocG (Def : DiscreteSpace.RingDef)(Ring : FiniteGraphDef) : LocationAFiniteDef (Ring).
  Definition t := Ring.V.
  Definition eq := Ring.Veq.
  Definition eq_equiv : Equivalence eq := Ring.Veq_equiv.
  Definition eq_dec : forall l l' : t, {eq l l'} + {~eq l l'} := Ring.Veq_dec.
End LocG.

(*  
Module N : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End N.

Module Names := Robots.Make (N).

Module ConfigA := Configurations.Make (LocationA)(N)(Names).
 *)
