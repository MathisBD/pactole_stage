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
  Definition to_Z (v : V): Z := ((Z.of_nat (proj1_sig v)) mod Z.of_nat n)%Z.

  Definition dir := direction.

  Definition E := (V * dir)%type.
  Definition Veq v1 v2 := Z.eq (to_Z v1) (to_Z v2).

  Instance to_Z_compat : Proper (Veq ==> Z.eq) to_Z.
  Proof. repeat intro. assumption. Qed.
  
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
  Proof. intros ? ? Heq. apply Heq. Qed.

  (* a function to pass a integer to a finit set *)
  Definition of_Z (l : Z) : V := exist _ (Z.to_nat (l mod Z.of_nat n)) (to_Z_inf_n l).

  Lemma Z2Z : forall l, (to_Z (of_Z l) = l mod Z.of_nat n)%Z.
  Proof.
  intros.
  unfold to_Z, of_Z. simpl.
  rewrite Z2Nat.id, Z.mod_mod.
  - reflexivity.
  - generalize n_sup_1; unfold n; omega.
  - apply Zdiv.Z_mod_lt.
    generalize n_sup_1; unfold n; omega.
  Qed.

  Instance of_Z_compat : Proper (Z.eq ==> Veq) of_Z.
  Proof. intros l1 l2 Hl. hnf. now rewrite 2 Z2Z, Hl. Qed.

  Lemma V2V : forall v, Veq (of_Z (to_Z v)) v.
  Proof.
  intros [k Hk]. hnf.
  rewrite Z2Z, Z.mod_small; trivial; [].
  apply Zdiv.Z_mod_lt.
  generalize n_sup_1; unfold n; omega.
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

  Lemma Veq_equiv : Equivalence Veq.
  Proof.
    unfold Veq.
    split.
    - now intro v.
    - now intros v1 v2 Hv.
    - intros v1 v2 v3 Hv1 Hv3. now transitivity (to_Z v2).
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
    unfold Eeq, tgt, Veq in *.
    destruct He as (Ht, Hd).
    rewrite 2 Z2Z. hnf. f_equal.
    rewrite Hd; destruct (snd e2); now rewrite Ht.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof. intros e1 e2 He. apply He. Qed.


  Lemma Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Proof.
    unfold V, Veq. intros. apply Z.eq_dec.
  Qed.

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
      unfold Veq, Z.eq, src, tgt in *.
      rewrite Z2Z in *.
      destruct (snd e); rewrite Hsrc in Htgt.
      + contradiction.
      + elim Hneq_a. rewrite <- Htgt.
        rewrite <- (Z.mod_1_l (Z.of_nat n)), <- Z.add_mod, Z.mod_1_l; try omega; [].
        replace (to_Z a - 1 + 1)%Z with (to_Z a) by ring. rewrite Z.mod_small; try omega; [].
        apply Z.mod_pos_bound. omega.
      + unfold to_Z in *. rewrite Z.mod_mod in *; omega.
    - intros Hedge. elim (Hedge (a, Backward)).
      split; unfold Veq, src, tgt; simpl; try reflexivity; [].
      rewrite Z2Z, Heq_a, Z2Z.
      unfold Z.sub. rewrite Zdiv.Zplus_mod_idemp_l.
      replace (to_Z b + 1 + - (1))%Z with (to_Z b) by omega.
      rewrite Z.mod_small; try reflexivity; [].
      apply Z.mod_pos_bound. omega.
    - intro Hedge. destruct (Veq_dec (of_Z (to_Z a + 1)) b) as [Heq_b | Hneq_b].
      + elim (Hedge (a, Forward)).
        split; unfold Veq, src, tgt; simpl; try reflexivity; [].
        now rewrite Z2Z, <- Heq_b, Z2Z.
      + destruct (Veq_dec a b) as [Heq |]; trivial; [].
        elim (Hedge (a, AutoLoop)).
        split; unfold Veq, src, tgt; simpl; try reflexivity; [].
        rewrite Z2Z, Heq. apply Z.mod_small.
        apply Z.mod_pos_bound. omega.
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
        revert_all. intro Heq. rewrite Heq, Z2Z.
        unfold Veq, Z.sub. rewrite Z2Z, Zdiv.Zplus_mod_idemp_l.
        ring_simplify (to_Z v2 + 1 + - (1))%Z.
        symmetry. apply Z.mod_small, Z.mod_pos_bound. omega.
      - unfold tgt. simpl. now split.
      - unfold tgt. simpl. split; try reflexivity; [].
        revert_all. intro Heq. now rewrite Heq, V2V.
    + unfold find_edge in *.
      revert Hcase. repeat destruct_match; intro Hcase; inv Hcase.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd. destruct Heq as [Heq1 Heq2].
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ rewrite Heq2, <- Heq1 in Hadd. hnf in Hadd. rewrite Z2Z in Hadd.
           revert Hadd. clear. (* wrong if n=2 *) admit.
        ++ rewrite Heq2, <- Heq1 in Hadd. hnf in Hadd. rewrite Z2Z in Hadd.
           revert Hadd. clear -Hn. rewrite Z2Z, Zdiv.Zplus_mod_idemp_l.
           destruct v1 as [k Hk]. unfold to_Z. simpl.
           destruct (Zincr_mod (Z.of_nat k mod Z.of_nat n) (Z.of_nat n)) as [Heq | [Heq Heq']]; try omega; [|].
           -- rewrite Heq, Z.mod_mod; lia. (* BUG: omega says not a quantifier-free goal *)
           -- rewrite Z.mod_mod in Heq'; lia.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd.
        destruct Heq as [Heq1 Heq2]. rewrite Heq2 in Hadd.
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ hnf in Hadd. rewrite <- Heq1, 2 Z2Z in Hadd. revert Hadd. (* wrong if n=2 *) admit.
        ++ hnf in Hadd. rewrite <- Heq1, 2 Z2Z in Hadd. revert Hadd.
           destruct (Zincr_mod (to_Z v1) (Z.of_nat n)) as [Heq | [Heq Heq']]; try omega; [|].
           -- unfold to_Z in *. rewrite Heq, Z.mod_mod; lia.
           -- unfold to_Z in *. rewrite Z.mod_mod; try lia. rewrite Z.mod_mod in Heq'; lia.
      - split; simpl; try easy; []. revert_one Veq. intro Hadd.
        destruct Heq as [Heq1 Heq2]. rewrite Heq2 in Hadd.
        unfold src, tgt in *. destruct (snd e); trivial; exfalso; [|].
        ++ hnf in Hadd. rewrite <- Heq1, Z2Z in Hadd. revert Hadd.
           unfold to_Z. destruct v1 as [k Hk]. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
           destruct (Zincr_mod (Z.of_nat k) (Z.of_nat n)) as [Heq | [Heq Heq']]; lia.
        ++ hnf in Hadd. rewrite <- Heq1, Z2Z in Hadd. revert Hadd.
           destruct v1 as [k Hk]. unfold to_Z. simpl.
           destruct (Zincr_mod (Z.of_nat k - 1) (Z.of_nat n)) as [Heq | [Heq Heq']]; try omega;
           ring_simplify (Z.of_nat k - 1 + 1)%Z in Heq; [|].
           -- rewrite Heq. ring_simplify ((Z.of_nat k - 1) mod Z.of_nat n + 1 - 1)%Z.
              rewrite Z.mod_mod; lia.
           -- rewrite Heq. simpl. intro Habs. symmetry in Habs. rewrite Zdiv.Zmod_divides in Habs; try lia; [].
              destruct Habs as [[] Hx]; nia.
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
