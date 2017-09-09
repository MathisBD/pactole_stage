(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import Rbase.
Require Import Omega.
Require Import Psatz.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Set Implicit Arguments.


Class Graph (V E : Type) := {
  V_Setoid :> Setoid V;
  E_Setoid :> Setoid E;
  V_EqDec :> EqDec V_Setoid;
  E_EqDec :> EqDec E_Setoid;

  src : E -> V; (* source and target of an edge *)
  tgt : E -> V;
  threshold : E -> R;
  threshold_pos : forall e, (0 < threshold e < 1)%R;
  src_compat : Proper (equiv ==> equiv) src;
  tgt_compat : Proper (equiv ==> equiv) tgt;
  threshold_compat : Proper (equiv ==> Logic.eq) threshold;

  find_edge : V -> V -> option E;
  find_edge_compat : Proper (equiv ==> equiv ==> opt_eq equiv) find_edge;
  find_edge_None : forall a b : V, find_edge a b = None <-> forall e : E, ~(src e == a /\ tgt e == b);
  find_edge_Some : forall v1 v2 e, find_edge v1 v2 == Some e <-> v1 == src e /\ v2 == tgt e }.

Global Opaque threshold_pos src_compat tgt_compat threshold_compat find_edge_compat find_edge_None find_edge_Some.

(** A finite graph ia a graph where the set [V] of vertices is a prefix of N. *)
(* FIXME: nothing prevents E from being infinite! *)
(* TODO: Maybe we should reuse the type used for robot names *)
Definition finite_node n := {m : nat | m < n}.

Instance finite_node_EqDec n : EqDec (eq_setoid (finite_node n)) := @subset_dec n.

Definition FiniteGraph (n : nat) E := Graph (finite_node n) E.
Existing Class FiniteGraph.


(** A ring. *)

Section Ring.
Context {n : nat}.

Inductive direction := Forward | Backward | AutoLoop.
Definition ring_edge := (finite_node n * direction)%type.

Instance ring_edge_Setoid : Setoid ring_edge := {
  equiv := fun e1 e2 => fst e1 == fst e2 /\ if (Nat.eq_dec n 2)
                                            then match snd e1, snd e2 with
                                                   | AutoLoop, AutoLoop => True
                                                   | AutoLoop, _ | _, AutoLoop  => False
                                                   | _, _ => True
                                                 end
                                            else snd e1 = snd e2 }.
Proof. split.
+ intro. split; repeat destruct_match; reflexivity.
+ intros ? ? []. split; repeat destruct_match; auto; now symmetry.
+ intros ? ? ? [? Heq] [? Heq']. split; try (now etransitivity; eauto); [].
  revert Heq Heq'. repeat destruct_match; auto; congruence.
Defined.

Lemma direction_eq_dec : forall d d': direction, {d = d'} + {d <> d'}.
Proof. intros. destruct d, d'; intuition; right; discriminate. Qed.

Instance ring_edge_EqDec : EqDec ring_edge_Setoid.
Proof.
intros e e'. unfold complement. simpl.
destruct (Nat.eq_dec n 2).
- destruct (snd e), (snd e'), (fst e =?= fst e'); intuition.
- destruct (fst e =?= fst e'), (direction_eq_dec (snd e) (snd e')); intuition.
Defined.

Hypothesis n_sup_1 : n > 1.
(* the following lemmas are used to easily prove that 
         (Z.to_nat (l mod Z.of_nat n)) = (l mod Z.of_nat n) *)
Lemma to_Z_sup_0 : forall l : Z, (0 <= l mod Z.of_nat n)%Z.
Proof. intros. apply Zdiv.Z_mod_lt. lia. Qed.

Lemma to_Z_inf_n (x : Z): Z.to_nat (x mod Z.of_nat n)%Z < n.
Proof. intros. rewrite <- Nat2Z.id, <- Z2Nat.inj_lt; try apply Zdiv.Z_mod_lt; omega. Qed.

Definition to_Z (v : finite_node n) : Z := Z.of_nat (proj1_sig v).
Definition of_Z (x : Z) : finite_node n := exist _ (Z.to_nat (x mod Z.of_nat n)) (to_Z_inf_n x).

Instance to_Z_compat : Proper (equiv ==> Z.eq) to_Z.
Proof. repeat intro. hnf in *. now subst. Qed.

Instance of_Z_compat : Proper (Z.eq ==> equiv) of_Z.
Proof. intros ? ? Heq. now rewrite Heq. Qed.

Lemma to_Z_injective : injective equiv Z.eq to_Z.
Proof.
intros [x Hx] [y Hy] Heq.
unfold to_Z in Heq. hnf in Heq |- *. simpl in Heq.
apply Nat2Z.inj in Heq. subst. f_equal. apply le_unique.
Qed.

Lemma Z2Z : forall l, (to_Z (of_Z l) = l mod Z.of_nat n)%Z.
Proof.
intros. unfold to_Z, of_Z. simpl.
rewrite Z2Nat.id; trivial; [].
apply Z.mod_pos_bound. generalize n_sup_1; lia.
Qed.

Lemma V2V : forall v, of_Z (to_Z v) == v.
Proof.
intros [k Hk]. hnf. unfold to_Z, of_Z. apply eq_proj1. simpl.
rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; omega.
Qed.


Definition Ring (Hn : (1 < n)%nat) (thd : ring_edge -> R)
                    (thd_pos : forall e, (0 < thd e < 1)%R) (thd_compat : Proper (equiv ==> Logic.eq) thd)
  : FiniteGraph n (ring_edge).
Proof.
refine ({|
  src := fst;
  tgt := fun e => of_Z (match snd e with
                          | Forward => (to_Z (fst e) + 1)%Z
                          | Backward => (to_Z (fst e) - 1)%Z
                          | AutoLoop => to_Z (fst e)
                        end);
  threshold := thd;
  find_edge := fun v1 v2 : finite_node n => if v1 =?= of_Z (to_Z v2 + 1) then Some (v1, Backward) else
                                            if of_Z (to_Z v1 + 1) =?= v2 then Some (v1, Forward)  else
                                            if v1 =?= v2 then Some (v1, AutoLoop) else None;
  V_EqDec := @finite_node_EqDec n;
  E_EqDec := ring_edge_EqDec |}).
* exact thd_pos.
* (* src_compat *)
  intros e1 e2 He. apply He.
* (* tgt_compat *)
  intros e1 e2 He. apply eq_proj1. unfold of_Z in *.
  destruct He as (Ht, Hd). rewrite Ht. clear Ht. revert Hd.
  repeat destruct_match; simpl; intro; try tauto || discriminate; [|];
  destruct (fst e2) as [k ?]; unfold to_Z; simpl;
  match goal with H : n = 2 |- _ => try rewrite H in *; clear H end;
  destruct k as [| [| k]]; simpl; try omega.
(* * (* find_edge_compat *)
  intros v1 v2 Hv12 v3 v4 Hv34. hnf in *. subst.
  repeat destruct_match; hnf in *; simpl in *; try easy || congruence; [| |];
  (split; trivial; []); now destruct_match. *)
* (* find_edge_None *)
  intros a b; split; unfold find_edge;
  destruct (a =?= of_Z (to_Z b + 1)) as [Heq_a | Hneq_a].
  + discriminate.
  + destruct (of_Z (to_Z a + 1) =?= b) as [Heq_b | Hneq_b], (a =?= b); try discriminate; [].
    intros _ e (Hsrc, Htgt).
    destruct (snd e); rewrite Hsrc in Htgt.
    - hnf in *. subst b. intuition.
    - elim Hneq_a. rewrite <- Htgt. rewrite Z2Z. apply eq_proj1.
      unfold of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
      replace (to_Z a - 1 + 1)%Z with (to_Z a) by ring.
      unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; try omega; [].
      apply proj2_sig.
    - now rewrite V2V in Htgt.
  + intros Hedge. elim (Hedge (a, Backward)).
    split; simpl; try reflexivity; [].
    rewrite Heq_a, Z2Z. apply eq_proj1.
    unfold Z.sub, of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
    replace (to_Z b + 1 + -1)%Z with (to_Z b) by omega.
    unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; omega || apply proj2_sig.
  + intro Hedge. destruct (of_Z (to_Z a + 1) =?= b) as [Heq_b | Hneq_b].
    - elim (Hedge (a, Forward)).
      split; simpl; try reflexivity; []. now rewrite <- Heq_b.
    - destruct (a =?= b) as [Heq |]; trivial; [].
      elim (Hedge (a, AutoLoop)).
      split; simpl; try reflexivity; []. now rewrite V2V, Heq.
* (* find_edge_Some *)
  clear dependent thd.
  intros v1 v2 e. simpl.
  repeat (destruct_match; simpl); hnf in * |-;
  intuition; try discriminate; simpl in *; try subst v1; try subst v2.
  + match goal with H : of_Z _ = ?x |- _ => subst x end.
    rewrite Z2Z. apply eq_proj1. destruct v2 as [k Hk]. unfold of_Z, to_Z. simpl. subst.
    destruct k as [| [| k]]; simpl; omega || reflexivity.
  + match goal with H : of_Z _ = ?x |- _ => subst x end.
    rewrite Z2Z. apply eq_proj1. destruct v2 as [k Hk]. unfold of_Z, to_Z. simpl. subst.
    destruct k as [| [| k]]; simpl; omega || reflexivity.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    rewrite V2V in *. unfold of_Z, to_Z in *. simpl in *.
    repeat revert_one @eq. intros Heq Heq'.
    (injection Heq; clear Heq) || (injection Heq'; clear Heq'). subst.
    destruct k as [| [| k]]; simpl; omega || discriminate.
  + reflexivity.
  + match goal with H : ?a = _ -> False |- _ => elim H; clear H; destruct a as [k Hk] end.
    rewrite Z2Z in *. unfold to_Z, of_Z. apply eq_proj1. simpl. subst.
    destruct k as [| [| k]]; simpl; omega || reflexivity.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    repeat revert_one @eq. clear. unfold of_Z, to_Z. simpl.
    intros Heq Heq'. (injection Heq; clear Heq) || (injection Heq'; clear Heq').
    subst. destruct k as [| [| k]]; simpl; omega || discriminate.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    repeat revert_one @eq. clear. unfold of_Z, to_Z. simpl.
    intros Heq Heq'. (injection Heq; clear Heq) || (injection Heq'; clear Heq').
    subst. destruct k as [| [| k]]; simpl; omega || discriminate.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    repeat revert_one @eq. clear. unfold to_Z, of_Z. simpl. intros Heq Heq'.
    (injection Heq; clear Heq) || (injection Heq'; clear Heq'). simpl. subst.
    destruct k as [| [| k]]; simpl; omega || discriminate.
  + now rewrite V2V.
  + congruence.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end. rewrite Z2Z in *.
    match goal with H : context[Z.modulo _ _] |- _ => apply H end. revert_one @eq. clear. intro.
    apply eq_proj1. unfold to_Z. simpl. subst.
    destruct k as [| [| k]]; simpl; omega || reflexivity.
  + rewrite V2V in *. congruence.
  + exfalso. rewrite Z2Z in *.
    match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    revert_one @eq. unfold of_Z, to_Z. intro Heq. injection Heq. simpl.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod, <- Nat2Z.inj_add; try lia; [].
    destruct (k =?= n - 1); [| destruct (k =?= n - 2)]; simpl in *; subst.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same, Z.mod_1_l; try lia; [].
      change (Z.to_nat 1) with 1%nat. lia.
    - replace (n - 2 + 1) with (n - 1) by omega. rewrite Nat.mod_small; try lia; [].
      replace (n - 1 + 1) with n by omega. rewrite Z.mod_same; simpl; lia.
    - rewrite Nat.mod_small, Z.mod_small, Nat2Z.id; try omega; [].
      split; try apply Zle_0_nat; []. apply Nat2Z.inj_lt. omega.
  + subst. rewrite Z2Z. apply eq_proj1.
    destruct v2 as [k Hk]. unfold to_Z, of_Z. simpl.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod; try lia; [].
    destruct (k =?= n - 1); simpl in *; subst.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; try lia; []. simpl.
      change (-1)%Z with (- (1))%Z. rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; try lia; [].
      change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Nat2Z.id; lia.
    - change 1%Z with (Z.of_nat 1). rewrite Nat.mod_small, <- Nat2Z.inj_sub, Z.mod_small, Nat2Z.id; lia.
  + exfalso. rewrite V2V in *.
    match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    revert_one @eq. intro Heq. injection Heq. unfold of_Z, to_Z. simpl.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod, Nat2Z.id; try lia; [].
    destruct (k =?= n - 1); simpl in *; subst.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; lia.
    - rewrite Nat.mod_small; omega.
  + reflexivity.
  + exfalso. rewrite Z2Z in *.
    match goal with x : finite_node n |- _ => destruct x as [k Hk] end. 
    revert_one @eq. unfold to_Z, of_Z. simpl. intro Heq. injection Heq. clear Heq.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod, Nat2Z.id; try lia; [].
    destruct (k =?= 0); [| destruct (k =?= n - 1)]; simpl in *; subst.
    - simpl. rewrite Nat.mod_1_l; try lia; [].
      change (-1)%Z with (- (1))%Z. rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; try lia; [].
      change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Nat2Z.id; omega.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; try lia; [].
      change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Z.mod_small, Nat2Z.id; lia.
    - change 1%Z with (Z.of_nat 1). rewrite Nat.mod_small, <- Nat2Z.inj_sub, Z.mod_small, Nat2Z.id; try omega; [].
      split; try apply Zle_0_nat; []. apply Nat2Z.inj_lt. omega.
  + exfalso. rewrite Z2Z in *.
    match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    revert_one @eq. unfold of_Z, to_Z. simpl. intro Heq. injection Heq.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- 2 Zdiv.mod_Zmod, 2 Nat2Z.id; try lia; [].
    destruct (k =?= n - 1); simpl in *; subst.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same, Nat.mod_small; omega.
    - rewrite 2 Nat.mod_small; omega.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    exfalso. revert_one @eq. intro Heq. injection Heq. unfold to_Z. simpl.
    change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_add, <- Zdiv.mod_Zmod, Nat2Z.id; try lia; [].
    destruct (k =?= n - 1); simpl in *; subst.
    - replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; omega.
    - rewrite Nat.mod_small; omega.
  + match goal with x : finite_node n |- _ => destruct x as [k Hk] end.
    exfalso. revert_one @eq. unfold of_Z, to_Z. simpl. intro Heq. injection Heq.
    destruct (k =?= 0); simpl in *; subst; simpl.
    - change (-1)%Z with (- (1))%Z. rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; try lia; [].
      change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Nat2Z.id; omega.
    - change 1%Z with (Z.of_nat 1). rewrite <- Nat2Z.inj_sub, Z.mod_small, Nat2Z.id; try lia; [].
      split; try apply Zle_0_nat; []. apply Nat2Z.inj_lt. omega.
  + now rewrite V2V.
  + congruence.
  + match goal with H : ?x = of_Z (to_Z (of_Z (to_Z ?x - 1)) + 1) -> False |- _ =>
      apply H; destruct x as [k Hk] end.
    apply eq_proj1. unfold to_Z, of_Z. simpl.
    destruct (k =?= 0); simpl in *; subst; simpl.
    - change (-1)%Z with (- (1))%Z. rewrite Z.mod_opp_l_nz; rewrite ?Nat.mod_1_l, ?Z.mod_1_l; try lia; [].
      change 1%Z with (Z.of_nat 1).
      rewrite <- Nat2Z.inj_sub,  <- Nat2Z.inj_add, <- Zdiv.mod_Zmod, 2 Nat2Z.id; try lia; [].
      replace (n - 1 + 1) with n by omega. rewrite Nat.mod_same; omega.
    - change 1%Z with (Z.of_nat 1).
      rewrite <- Nat2Z.inj_sub, <- Zdiv.mod_Zmod, Nat.mod_small; try omega; [].
      rewrite <- Nat2Z.inj_add, Nat2Z.id. replace (k - 1 + 1) with k by omega.
      rewrite <- Zdiv.mod_Zmod, Nat.mod_small, Nat2Z.id; omega.
  + rewrite V2V in *. congruence.
Defined.

End Ring.

(* To avoid passing the proof of [n > 1] around. *)
Arguments of_Z {n} [_] _.
