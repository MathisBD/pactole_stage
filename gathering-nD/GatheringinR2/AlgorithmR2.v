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
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Positions.
Require Pactole.CommonFormalism.
Require Pactole.RigidFormalism.
Require Import SortingR.
Require Import MultisetSpectrum.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.


Set Implicit Arguments.
Close Scope R_scope.




(** R² as a vector space over R. *)

Module R2def : RealMetricSpaceDef with Definition t := (R * R)%type
                                  with Definition eq := @Logic.eq (R * R)
(*                                  with Definition eq_dec := Rdec *)
                                  with Definition origin := (0, 0)%R
                                  with Definition dist := fun x y => sqrt ((fst x - fst y)² + (snd x - snd y)²)
                                  with Definition add := fun x y => let '(x1, x2) := x in
                                                                    let '(y1, y2) := y in (x1 + y1, x2 + y2)%R
                                  with Definition mul := fun k r => let '(x, y) := r in (k * x, k * y)%R
                                  with Definition opp := fun r => let '(x, y) := r in (-x, -y)%R.
  
  Definition t := (R * R)%type.
  Definition origin := (0, 0)%R.
  Definition eq := @Logic.eq (R * R).
  Definition dist x y := sqrt ((fst x - fst y)² + (snd x - snd y)²).
  
  Definition add x y := let '(x1, x2) := x in let '(y1, y2) := y in (x1 + y1, x2 + y2)%R.
  Definition mul k r := let '(x, y) := r in (k * x, k * y)%R.
  Definition opp r := let '(x, y) := r in (-x, -y)%R.
  
  Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance opp_compat : Proper (eq ==> eq) opp.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Definition eq_equiv := @eq_equivalence (R * R).
  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. unfold eq. decide equality; apply Rdec. Qed.
  
  Lemma dist_defined : forall x y : t, dist x y = 0%R <-> eq x y.
  Proof.
  intros x y. unfold eq, dist. split; intro Heq.
  +
    SearchAbout R0 sqrt "²". admit.
(* apply sqrt_eq_0 in Heq.
 apply Rminus_diag_uniq. destruct (Rcase_abs (x - y)) as [Hcase | Hcase].
    - apply Rlt_not_eq in Hcase. apply Rabs_no_R0 in Hcase. contradiction.
    - rewrite <- Heq. symmetry. now apply Rabs_pos_eq, Rge_le.*)
  + subst. do 2 rewrite (Rminus_diag_eq _ _ (reflexivity _)). rewrite Rsqr_0, Rplus_0_l. apply sqrt_0.
  Admitted.

  Lemma dist_sym : forall y x : t, dist x y = dist y x.
  Proof. intros. unfold dist. now setoid_rewrite R_sqr.Rsqr_neg_minus at 1 2. Qed.
  
  Lemma triang_ineq : forall x y z : t, (dist x z <= dist x y + dist y z)%R.
  Proof. Admitted.
  
  Lemma add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. Admitted.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. Admitted.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. Admitted.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. Admitted.
  
  Lemma mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. Admitted.
  
  Lemma add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. Admitted.
  
  Lemma plus_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  Proof. Admitted.
  
  Lemma mul_1 : forall u, eq (mul 1 u) u.
  Proof. Admitted.

  Lemma non_trivial : exists u v, ~eq u v.
  Proof. Admitted.
End R2def.


Module R2 := MakeRealMetricSpace(R2def).

Delimit Scope R2_scope with R2.
Bind Scope R2_scope with R2.t.
Notation "u + v" := (R2.add u v) : R2_scope.
Notation "k * u" := (R2.mul k u) : R2_scope.
Notation "- u" := (R2.opp u) : R2_scope.


Transparent R2.origin R2def.origin R2.eq_dec R2.eq R2def.eq R2.dist R2def.dist.

Ltac unfoldR2 := unfold R2.origin, R2def.origin, R2.eq_dec, R2.eq, R2def.eq, R2.dist, R2def.dist.

Lemma R2mul_0 : forall u, R2.eq (R2.mul 0 u) R2.origin.
Proof. intros [x y]. compute. now do 2 rewrite Rmult_0_l. Qed.


(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := repeat
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
Module Spect := MultisetSpectrum.Make(R2)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Common := CommonFormalism.Make(R2)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(R2)(N)(Spect)(Common).
Close Scope R_scope.

(** [gathered_at pos pt] means that in position [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather (pt: R2.t) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive WillGather (pt : R2.t) (e : execution) : Prop :=
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
  forall config, exists pt : R2.t, WillGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R2.t, WillGather pt (execute r d config).


(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(* A location is determined by distances to 3 points. *)
(*
Lemma dist_case : forall x y, R2.dist x y = x - y \/ R2.dist x y = y - x.
Proof.
unfold R.dist, Rdef.dist. intros x y. destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. lra.t
- apply Rabs_left in Hlt. lra.
Qed.

Lemma dist_locate : forall x y k, R.dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.
*)
Lemma GPS : forall x y z t1 t2, x <> y -> y <> z -> x <> z ->
  R2.dist t1 x = R2.dist t2 x -> R2.dist t1 y = R2.dist t2 y -> R2.dist t1 z = R2.dist t2 z -> t1 = t2.
Proof.
intros x y z t1 t2 Hxy Hyz Hxz Hx Hy Hz.
Admitted.
Arguments GPS x y z t1 t2 _ _ _ _ _ _ : clear implicits.

Lemma diff_0_1 : ~R2.eq (0, 0) (0, 1).
Proof. intro Heq. inversion Heq. now apply R1_neq_R0. Qed.

(** Definition of rotations *)

Definition rotate_bij (θ : R) : bijection R2.eq_equiv.
refine {|
  section := fun r => (cos θ * fst r - sin θ * snd r, sin θ * fst r + cos θ * snd r);
  retraction := fun r => (cos (-θ) * fst r - sin (-θ) * snd r, sin (-θ) * fst r + cos (-θ) * snd r) |}.
Proof.
unfold R2.eq, R2def.eq.
abstract (intros xy xy'; split; intro; subst; destruct xy as [x y] || destruct xy' as [x y]; simpl;
rewrite Rtrigo1.cos_neg, Rtrigo1.sin_neg; f_equal; ring_simplify ; do 2 rewrite <- Rfunctions.Rsqr_pow2;
rewrite <- (Rmult_1_l x) at 3 || rewrite <- (Rmult_1_l y) at 3; rewrite <- (Rtrigo1.sin2_cos2 θ); ring).
Defined.

Definition rotate (θ : R) : similarity.
refine {|
  f := rotate_bij θ;
  ratio := 1;
  center := (0,0) |}.
Proof.
+ simpl. unfoldR2. abstract(f_equal; field).
+ unfoldR2. intros. rewrite Rmult_1_l. f_equal. simpl.
repeat rewrite Rfunctions.Rsqr_pow2; ring_simplify; repeat rewrite <- Rfunctions.Rsqr_pow2.
(* AACtactics should help with rewriting by sin2_cos2 here *)
admit.
Admitted.



Lemma rotate_inverse : forall θ, bij_eq ((rotate θ)⁻¹) rotate (-θ).
(** A similarity in R2 is described by its ratio, center and rotation angle. *)
Theorem similarity_in_R2 : forall sim, exists θ,
  forall x, sim.(f) x = R2.mul sim.(ratio) (rotate θ (R2.add x (R2.opp sim.(center)))).
Proof.
intro sim. assert (Hkpos : 0 < sim.(ratio)) by apply sim_ratio_pos.
destruct sim as [f k c Hc Hk]. simpl in *. unfold R2.origin, R2def.origin in Hc.
destruct (Rdec k 0) as [Hk0 | Hk0].
* (* if the ratio is 0, the similarity is a constant function. *)
  exists 0. intro x. subst k. do 2 rewrite Rmult_0_l.
  rewrite <- R2.dist_defined. rewrite <- Hc, Hk at 1. ring.
* 
Admitted.

Corollary inverse_similarity_in_R2 : forall (sim : similarity) θ,
  (forall x, sim x = sim.(ratio) * (rotate θ (x + (- sim.(center)))))%R2 ->
  (forall x, (sim ⁻¹) x = (/sim.(ratio)) * (rotate (-θ) (x + (- (rotate θ sim.(center))))))%R2.
Proof.
intros sim θ Hdirect x.
rewrite <- sim.(Inversion). rewrite Hdirect.
Check surjective_pairing.
 destruct sim as [f ρ [cx cy] ? ?]. destruct x as [x y]; compute in *.
Qed.

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
