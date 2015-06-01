(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega.
Require Import Rbase Rbasic_fun.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
Require Import Robots.
Require Import Positions.
Require Import FormalismRd.
Require Import SortingR.
Require Import MultisetSpectrum.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.


Set Implicit Arguments.
Close Scope R_scope.


(** R as a vector space over itself. *)

Module Rdef : MetricSpaceDef with Definition t := R
                             with Definition eq := @Logic.eq R
                             with Definition eq_dec := Rdec
                             with Definition origin := 0%R
                             with Definition dist := fun x y => Rabs (x - y)
                             with Definition add := Rplus
                             with Definition mul := Rmult
                             with Definition opp := Ropp.
  
  Definition t := R.
  Definition origin := 0%R.
  Definition eq := @Logic.eq R.
  Definition dist x y := Rabs (x - y).
  
  Definition add := Rplus.
  Definition mul := Rmult.
  Definition opp := Ropp.
  
  Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance opp_compat : Proper (eq ==> eq) opp.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Definition eq_equiv := @eq_equivalence R.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := Rdec.
  
  Lemma dist_defined : forall x y : t, dist x y = 0%R <-> eq x y.
  Proof.
  intros x y. unfold eq, dist. split; intro Heq.
  + apply Rminus_diag_uniq. destruct (Rcase_abs (x - y)) as [Hcase | Hcase].
    - apply Rlt_not_eq in Hcase. apply Rabs_no_R0 in Hcase. contradiction.
    - rewrite <- Heq. symmetry. now apply Rabs_pos_eq, Rge_le.
  + rewrite (Rminus_diag_eq _ _ Heq). apply Rabs_R0.
  Qed.

  Lemma dist_sym : forall y x : t, dist x y = dist y x.
  Proof. intros. unfold dist. apply Rabs_minus_sym. Qed.
  
  Lemma triang_ineq : forall x y z : t, (dist x z <= dist x y + dist y z)%R.
  Proof.
  intros. unfold dist. replace (x - z)%R with (x - y + (y - z))%R by lra. apply Rabs_triang.
  Qed.
  
  Lemma plus_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. unfold eq, add, origin. intros. lra. Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. unfold eq, add, opp, origin. intros. lra. Qed.
  
  Lemma mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. unfold eq, mul. intros. lra. Qed.
  
  Lemma add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  Lemma plus_distr : forall a b u, eq (mul (a + b) u) (add (mul a u) (mul b u)).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  (** The multiplicative identity is omitted. *)
End Rdef.


Module R := MakeMetricSpace(Rdef).

Transparent R.origin Rdef.origin R.eq_dec Rdef.eq_dec.


(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := unfold R.eq_dec, Rdef.eq_dec; repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] =>
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | |- context[Rdec 0 1] =>
        let Heq := fresh "Heq" in destruct (Rdec 0 1) as [Heq | Heq];
        [now symmetry in Heq; elim R1_neq_R0 | clear Heq]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ?x <> ?x |- _ => elim H; reflexivity
  end.

Ltac Rdec_full :=
  unfold R.eq_dec, Rdef.eq_dec;
  match goal with
    | |- context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.


Ltac Rdec_aux H :=
  match type of H with
    | context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot. We
    call a [configuration] a function from robots to position. An
    [execution] is an infinite (coinductive) stream of [configuration]s. A
    [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR.

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter nG: nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0.
  Definition nG := nG.
  Definition nB := 0.
End N.


(** The spectrum is a multiset of positions *)
Module Spect := MultisetSpectrum.Make(R)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Formalism := Formalism(R)(N)(Spect).
Close Scope R_scope.

(** [gathered_at pos pt] means that in position [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather (pt: R) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive WillGather (pt : R) (e : execution) : Prop :=
  | Now : Gather pt e -> WillGather pt e
  | Later : WillGather pt (execution_tail e) -> WillGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these positions as [forbidden]. *)
Definition forbidden (config : Pos.t) :=
  Nat.Even N.nG /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : R.t, WillGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R.t, WillGather pt (execute r d config).


(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(* A location is determined by distances to 2 points. *)
Lemma dist_case : forall x y, R.dist x y = x - y \/ R.dist x y = y - x.
Proof.
unfold R.dist, Rdef.dist. intros x y. destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. lra.
- apply Rabs_left in Hlt. lra.
Qed.

Lemma dist_locate : forall x y k, R.dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.

Lemma GPS : forall x y z1 z2, x <> y -> R.dist z1 x = R.dist z2 x -> R.dist z1 y = R.dist z2 y -> z1 = z2.
Proof.
intros x y z1 z2 Hneq Hx Hy.
assert (Hcase1 := dist_case z1 x). assert (Hcase2 := dist_case z2 x).
assert (Hcase3 := dist_case z1 y). assert (Hcase4 := dist_case z2 y).
admit.
Admitted.
Arguments GPS x y z1 z2 _ _ _ : clear implicits.

Lemma sim_ratio_non_null : forall sim, sim.(ratio) <> 0%R.
Proof. apply (sim_ratio_non_null R1_neq_R0). Qed.

(* Not true when the metric space has dimension 0, we need at least 2 different points. *)
Lemma sim_ratio_pos : forall sim, (0 < sim.(ratio))%R.
Proof. apply (sim_ratio_pos R1_neq_R0). Qed.

Lemma similarity_injective : forall sim : similarity, injective eq eq sim.
Proof. apply (similarity_injective R1_neq_R0). Qed.

(* A similarity in R is described by its ratio and its center. *)
Theorem similarity_in_R_case : forall sim,
  (forall x, sim.(f) x = sim.(ratio) * (x - sim.(center))) \/
  (forall x, sim.(f) x = - sim.(ratio) * (x - sim.(center))).
Proof.
intro sim. assert (Hkpos : 0 < sim.(ratio)) by apply sim_ratio_pos.
destruct sim as [f k c Hc Hk]. simpl in *. unfold R.origin, Rdef.origin in Hc.
destruct (Rdec k 0) as [Hk0 | Hk0].
* (* if the ratio is 0, the similarity is a constant function. *)
  left. intro x. subst k. rewrite Rmult_0_l.
  rewrite <- R.dist_defined. rewrite <- Hc, Hk at 1. ring.
* assert (Hc1 : f (c + 1) = k \/ f (c + 1) = - k).
  { specialize (Hk (c + 1) c). rewrite Hc in Hk.
    assert (H1 : R.dist (c + 1) c = 1). { replace 1 with (c+1 - c) at 2 by ring. apply Rabs_pos_eq. lra. }
    rewrite H1 in Hk. destruct (dist_case (f (c + 1)) 0) as [Heq | Heq]; rewrite Heq in Hk.
    - ring_simplify in Hk. now left.
    - ring_simplify in Hk. right. now rewrite <- Hk, Ropp_involutive. }
  destruct Hc1 as [Hc1 | Hc1].
  + left. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - 0) with (k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq k); trivial. lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - k) with (k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq k); trivial. lra.
  + right. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - 0) with (- k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - - k) with (- k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
Qed.

Corollary similarity_in_R : forall sim, exists k, (k = sim.(ratio) \/ k = - sim.(ratio))
  /\ forall x, sim.(f) x = k * (x - sim.(center)).
Proof. intro sim. destruct (similarity_in_R_case sim); eauto. Qed.


Corollary inverse_similarity_in_R : forall (sim : similarity) k, k <> 0 ->
  (forall x, sim x = k * (x - sim.(center))) -> forall x, (sim ⁻¹) x = x / k + sim.(center).
Proof. intros sim k Hk Hdirect x. rewrite <- sim.(Inversion), Hdirect. hnf. now field. Qed.

Lemma sim_compat (sim:similarity) : Proper (R.eq ==> R.eq) sim.
Proof.
  repeat intro.
  rewrite H.
  reflexivity.
Qed.

Lemma sim_Minjective : forall (sim : similarity), MMultiset.Preliminary.injective R.eq R.eq sim.
Proof. apply similarity_injective. Qed.

Hint Immediate sim_compat similarity_injective sim_Minjective.


Coercion is_true : bool >-> Sortclass.

Definition monotonic {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  Proper (RA ==> RB) f \/ Proper (RA --> RB) f.

Lemma similarity_increasing : forall k t, 0 <= k -> Proper (Rleb ==> Rleb) (fun x => k * (x - t)).
Proof. repeat intro. hnf in *. rewrite Rleb_spec in *. apply Rmult_le_compat_l; lra. Qed.

Lemma similarity_decreasing : forall k t, k <= 0 -> Proper (Rleb --> Rleb) (fun x => k * (x - t)).
Proof.
repeat intro. hnf in *. unfold flip in *. rewrite Rleb_spec in *. apply Ropp_le_cancel.
replace (- (k * (y - t))) with ((- k) * (y - t)) by ring.
replace (- (k * (x - t))) with ((- k) * (x - t)) by ring.
apply Rmult_le_compat_l; lra.
Qed.

Corollary similarity_monotonic : forall sim, monotonic Rleb Rleb sim.(f).
Proof.
intro sim. destruct (similarity_in_R_case sim) as [Hinc | Hdec].
+ left. intros x y Hxy. do 2 rewrite Hinc. apply similarity_increasing; trivial.
  pose (Hratio := sim_ratio_pos sim). lra.
+ right. intros x y Hxy. do 2 rewrite Hdec. apply similarity_decreasing; trivial.
  assert (Hratio := sim_ratio_pos sim). lra.
Qed.

Instance forbidden_compat : Proper (Pos.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [pt1 [pt2 [Hneq Hpt]]]]; split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.


End GatheringinR.

(* Other results *)

Lemma even_div2 : forall n, Nat.Even n -> Nat.div2 n + Nat.div2 n = n.
Proof.
intros n Hn. replace (Nat.div2 n + Nat.div2 n) with (2 * Nat.div2 n) by lia.
rewrite <- Nat.double_twice. symmetry. apply even_double. now rewrite Even.even_equiv.
Qed.

Global Instance Leibniz_fun_compat : forall f, Proper (R.eq ==> R.eq) f.
Proof. intros f ? ? Heq. now rewrite Heq. Qed.
