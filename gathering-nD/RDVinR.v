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

(** **  Framework of the correctness proof: a finite set with at leasts two elements  **)

Parameter nG: nat.
Axiom size_G : nG >= 2.

Corollary half_size_pos : div2 nG > 0.
Proof. apply Exp_prop.div2_not_R0. apply size_G. Qed.

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

(** [solGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed. *)
Definition solGathering (r : robogram) (d : demon) :=
  forall pos, ~forbidden pos -> exists pt : R, WillGather pt (execute r d pos).


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
lra.
Qed.
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
    rewrite H1 in Hk. destruct (dist_case (f (c + 1)) 0) as [Heq | Heq]; rewrite Heq in Hk; lra. }
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

Lemma similarity_middle : forall (sim : similarity) x y, sim ((x + y) / 2) = (sim x + sim y) / 2.
Proof.
intros sim x y. destruct (similarity_in_R_case sim) as [Hsim | Hsim];
repeat rewrite Hsim; unfold R.t, Rdef.t in *; field.
Qed.


(* Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 99, format "'⟦' k ','  t '⟧'"). *)
Close Scope R_scope.

(** **  Some simplifications due to having no byzantine robots  **)

(** [lift_function f g] lifts two renaming functions, one for good and
    one for bad robots, into a renaming function for any robot. *)
Definition lift_pos (f : Names.G -> R) : (Names.ident -> R) :=
  fun id => match id with
              | Good g => f g
              | Byz b => Fin.case0 (fun _ => R) b
            end.

(* It would be great to have it as a coercion between G → R and Pos.t,
   but I do not know how to make it work. *)

Instance lift_pos_compat : Proper ((eq ==> eq) ==> Pos.eq) lift_pos.
Proof. intros f g Hfg id. hnf. unfold lift_pos. destruct id; try reflexivity. now apply Hfg. Qed.

(** As there is no byzantine robots, a position is caracterized by the locations of good robots only. *)
Lemma lift_pos_equiv : forall pos : Pos.t, Pos.eq pos (lift_pos (fun g => pos (Good g))).
Proof. unfold lift_pos. intros pos [g | b]; hnf. reflexivity. now apply Fin.case0. Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spec_non_nil : forall conf, ~Spect.eq (!! conf) Spect.empty.
Proof.
intros conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.multiset_empty in Heq.
assert (Hlgth:= Spect.Pos.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
unfold N.nG in *.
assert (hnG:=size_G).
omega.
Qed.

Corollary sort_non_nil : forall config, sort (Spect.support (!! config)) <> nil.
Proof.
intros config Habs. apply (spec_non_nil config). rewrite <- Spect.support_nil.
apply Permutation_nil. setoid_rewrite Permuted_sort at 2. rewrite Habs. reflexivity.
Qed.

(** **  Property expressing the existence of a majority tower  **)

Definition MajTower_at x pos :=
  forall y, y <> x -> ((!! pos)[y] < (!! pos)[x]).

Instance MajTower_at_compat : Proper (Logic.eq ==> Pos.eq ==> iff) MajTower_at.
Proof. intros ? ? ? ? ? Hpos. subst. unfold MajTower_at. now setoid_rewrite Hpos. Qed.

(** Computationally, it is equivalent to having only one tower with maximum multiplicity. *)

(** ***  The maximum multiplicity of a multiset  **)

(** [Smax_mult s] returns the maximal multiplicity of configutation [s]. *)
Definition Smax_mult s := Spect.fold (fun _ => max) s 0%nat.

Instance Smax_mult_compat : Proper (Spect.eq ==> eq) Smax_mult.
Proof.
unfold Smax_mult. intros s1 s2 Heq. apply Spect.fold_compat; trivial; refine _.
intros _ _ n m p. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
Qed.

Lemma Smax_mult_map_injective_invariant : forall f, injective eq eq f ->
  forall s, Smax_mult (Spect.map f s) = Smax_mult s.
Proof.
intros f Hf. apply Spect.ind.
+ intros s1 s2 Hs. now rewrite Hs.
+ intros s x n Hout Hn Hrec. rewrite Spect.map_add; try now intros ? ? Heq; rewrite Heq.
  assert (Haux : Spect.elt -> Spect.elt ->
            forall n m a : nat, Init.Nat.max m (Init.Nat.max n a) = Init.Nat.max n (Init.Nat.max m a)).
  { intros _ _ n' m' p'. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2. }
  unfold Smax_mult in *. repeat rewrite Spect.fold_add; trivial; refine _;try now (hnf;auto).
  - intro Habs. apply Hout. apply Spect.map_In in Habs.
    * destruct Habs as [y [Heq Hin]].
      apply Hf in Heq; subst; assumption.
    * repeat intro.
      rewrite H0.
      reflexivity.
+ now rewrite Spect.map_empty.
Qed.

Corollary Smax_mult_similarity_invariant : forall (sim : similarity) s, Smax_mult (Spect.map sim s) = Smax_mult s.
Proof. intros. apply Smax_mult_map_injective_invariant. auto. Qed.

Lemma Smax_mult_add : forall s x n, (n > 0)%nat -> ~Spect.In x s ->
  Smax_mult (Spect.add x n s) = Nat.max n (Smax_mult s).
Proof.
intros s x n Hn. unfold Smax_mult. apply Spect.fold_add; trivial.
- refine _.
- repeat intro. now subst.
- repeat intro. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
Qed.

Theorem Smax_mult_spec : forall s x, (s[x] <= Smax_mult s)%nat.
Proof.
intro s. pattern s. apply Spect.ind; clear s.
* intros s1 s2 Hs. now setoid_rewrite Hs.
* intros m x n Hout Hn Hrec y. rewrite Smax_mult_add; trivial.
  assert (Hx : m[x] = 0%nat). { rewrite Spect.not_In in Hout. assumption. }
  destruct (Rdec y x) as [Hxy | Hxy].
  + subst. rewrite Spect.add_spec, Hx. rewrite Spect.eq_refl_left. apply Max.le_max_l.
  + rewrite Spect.add_other; auto. transitivity (Smax_mult m).
    - apply Hrec.
    - apply Max.le_max_r.
* intro x. rewrite Spect.empty_spec. omega.
Qed.

Lemma Smax_mult_0 : forall s, Smax_mult s = 0%nat <-> Spect.eq s Spect.empty.
Proof.
intro s. split; intro Heq.
+ destruct (Spect.empty_or_In_dec s) as [? | [x Hin]]; trivial.
  elim (lt_irrefl 0). apply lt_le_trans with s[x].
  - exact Hin.
  - rewrite <- Heq. apply Smax_mult_spec.
+ rewrite Heq. unfold Smax_mult. now rewrite Spect.fold_empty.
Qed.

(** ***  Elements of a multiset with maximal multiplciity  **)

(** [Smax s] return the configuration [s] where all non maximal positions
    have been removed. *)
Definition Smax s := Spect.filter (fun _ => beq_nat (Smax_mult s)) s.

Instance Smax_compat : Proper (Spect.eq ==> Spect.eq) Smax.
Proof.
intros s1 s2 Heq. unfold Smax. rewrite Heq. apply Spect.filter_extensionality_compat.
- repeat intro. now subst.
- intros _ n. now rewrite Heq.
Qed.

Lemma Smax_map_injective : forall f, injective eq eq f ->
  forall s, Spect.eq (Smax (Spect.map f s)) (Spect.map f (Smax s)).
Proof.
intros f Hf s. unfold Smax. rewrite Spect.map_injective_filter.
+ apply Spect.map_compat.
  - intros ? ? Heq. now rewrite Heq.
  - apply Spect.filter_extensionality_compat; repeat intro; subst; trivial.
    now rewrite Smax_mult_map_injective_invariant.
+ repeat intro. now subst.
+ intros ? ? Heq. now rewrite Heq.
+ assumption.
Qed.

Corollary Smax_similarity : forall (sim : similarity),
  forall s, Spect.eq (Smax (Spect.map sim s)) (Spect.map sim (Smax s)).
Proof. intros. apply Smax_map_injective. auto. Qed.


Instance eqb_Smax_mult_compat s:
  Proper (R.eq ==> eq ==> eq)
         (fun _ : Spect.elt => Nat.eqb (Smax_mult s)).
Proof.
  repeat intro. now subst.
Qed.

Local Hint Immediate eqb_Smax_mult_compat.

Lemma Smax_subset : forall s, Spect.Subset (Smax s) s.
Proof.
  intros s x.
  unfold Smax.
  setoid_rewrite Spect.filter_spec.
  2: apply eqb_Smax_mult_compat.
  destruct (Smax_mult s =? s[x]);auto.
  omega.
Qed.

Theorem Smax_spec1 : forall s x y, Spect.In y (Smax s) -> (s[x] <= (Smax s)[y])%nat.
Proof.
intros s x y Hy. unfold Smax in *.
(* assert (Hf := eqb_Smax_mult_compat s). *)
unfold Spect.In in Hy. rewrite Spect.filter_spec in *; auto.
destruct (Smax_mult s =? s[y]) eqn:Heq; try omega.
rewrite Nat.eqb_eq in Heq. rewrite <- Heq. apply Smax_mult_spec.
Qed.

Theorem Smax_spec_non_nil : forall s x, Spect.In x s -> exists y, Spect.In y (Smax s).
Proof.
  intro s.
  pattern s.
  apply Spect.ind.
  - intros m1 m2 Hm1m2. now setoid_rewrite Hm1m2.
  - intros m x n Hxnotinm Hpos HI x' Hx'.
    destruct (Spect.empty_or_In_dec m).
    + exists x. unfold Smax. rewrite Spect.filter_In; auto. split.
      * rewrite Spect.add_In. right. split; reflexivity || omega.
      * rewrite Nat.eqb_eq, Smax_mult_add; trivial.
        rewrite e at 2.
        rewrite Spect.add_empty, Spect.singleton_spec.
        unfold R.eq_dec,Rdef.eq_dec. Rdec.
        rewrite <- Smax_mult_0 in e. rewrite e.
        apply Max.max_0_r.
    + destruct e as [x'' Hx''].
      specialize (HI x'' Hx'').
      destruct HI as [y Hy]. unfold Smax.
      setoid_rewrite Spect.filter_In; try now repeat intro; subst.
      rewrite Smax_mult_add; trivial.
      unfold Smax in Hy. rewrite Spect.filter_In in Hy; auto.
      destruct Hy as [Hy Heq]. rewrite Nat.eqb_eq in Heq.
      destruct (le_lt_dec n (m[y])).
      * { exists y. split.
          - now rewrite Spect.add_In; auto.
          - rewrite Nat.eqb_eq, Heq, Spect.add_other, Max.max_r; trivial.
            intro Habs. apply Hxnotinm. now rewrite <- Habs. }
      * { exists x. split.
          - rewrite Spect.add_In. right. split; reflexivity || omega.
          - rewrite Nat.eqb_eq, Max.max_l; try omega.
            rewrite Spect.not_In in Hxnotinm. now rewrite Spect.add_same, Hxnotinm. }
  - intros x H. elim (Spect.In_empty H).
Qed.


Lemma Smax_empty : forall s, Spect.eq (Smax s) Spect.empty <-> Spect.eq s Spect.empty.
Proof.
intro s. split; intro H.
- destruct (Spect.empty_or_In_dec s) as [Hs | Hs].
  + intro. now rewrite Hs.
  + destruct Hs as [x Hx].
    destruct (Smax_spec_non_nil Hx) as [y Hy].
    unfold Spect.In in Hy.
    rewrite H in Hy. rewrite Spect.empty_spec in Hy. omega.
- rewrite H.
  unfold Smax.
  rewrite Spect.filter_empty.
  + reflexivity.
  + intros r1 r2 Hr1r2 x1 x2 hx1x2.
    subst.
    reflexivity.
Qed.

Lemma Smax_2_mult : forall s x, (Smax s)[x] = 0 \/ (Smax s)[x] = s[x].
Proof.
intros s x. destruct (Spect.empty_or_In_dec s) as [Hs | Hs].
+ left. rewrite <- Smax_empty in Hs. rewrite (Hs x). apply Spect.empty_spec.
+ unfold Smax. rewrite Spect.filter_spec.
  destruct (Smax_mult s =? s[x]) as [Heq | Heq]; auto.
  repeat intro. now subst.
Qed.
(*
Lemma Smax_val : forall s x, Spect.In x (Smax s) -> s[x] = Smax_mult s.
Proof.
intros s x Hin.
Qed.
*)
Lemma Smax_In_mult : forall s x, Spect.In x s -> (Spect.In x (Smax s) <-> (Smax s)[x] = s[x]).
Proof. intros s x Hin. unfold Spect.In in *. destruct (Smax_2_mult s x); omega. Qed.

Lemma Smax_spec_mult : forall s x y, Spect.In x (Smax s) -> (Spect.In y (Smax s) <-> (Smax s)[y] = (Smax s)[x]).
Proof.
intros s x y Hx. split.
+ intro Hy. destruct (Smax_2_mult s x) as [Hx' | Hx'], (Smax_2_mult s y) as [Hy' | Hy'];
  (unfold Spect.In in *; omega) || (try congruence); [].
  apply le_antisym.
  - rewrite Hy'. now apply Smax_spec1.
  - rewrite Hx'. now apply Smax_spec1.
+ intro Heq. unfold Spect.In in *. now rewrite Heq.
Qed.

Theorem Smax_spec2 : forall s x y,
  Spect.In x (Smax s) -> ~Spect.In y (Smax s) -> (s[y] < s[x])%nat.
Proof.
intros s x y Hx Hy. apply le_neq_lt.
+ assert (Hx' := Hx). rewrite Smax_In_mult in Hx.
  - rewrite <- Hx. now apply Smax_spec1.
  - now rewrite <- Smax_subset.
+ intro Habs. apply Hy. unfold Smax. rewrite Spect.filter_In; try now repeat intro; subst. split.
  - unfold Spect.In in *. rewrite Habs. apply lt_le_trans with (Smax s)[x]; trivial. apply Smax_subset.
  - rewrite Habs. unfold Smax in Hx. rewrite Spect.filter_In in Hx; try now repeat intro; subst.
Qed.

Close Scope R_scope.
  
Lemma Smax_max_mult : forall s x, ~Spect.eq s Spect.empty -> Spect.In x (Smax s) <-> s[x] = Smax_mult s.
Proof.
  intros s x hnonempty.
  split.
  - intros H.
    apply Spect.filter_In in H;auto.
    destruct H.
    symmetry.
    apply beq_nat_true.
    assumption.
  - intro H.
    unfold Smax.
    rewrite Spect.filter_In;auto.
    split.
    + assert (s[x]<>0).
      { intro abs.
        rewrite H in abs.
        rewrite Smax_mult_0 in abs.
        contradiction. }
      red.
      omega.
    + rewrite H.
      symmetry.
      apply beq_nat_refl.
Qed.

Lemma Smax_max_mult_ex : forall s, ~Spect.eq s Spect.empty -> exists x, Smax_mult s = s[x].
Proof.
  intros s.
  pattern s.
  apply Spect.ind.
  - repeat intro.
    setoid_rewrite H.
    reflexivity.
  - intros m x n H H0 H1 H2.
    clear H2.
    destruct (Spect.empty_or_In_dec m).
    exists x.
    rewrite e.
    rewrite Spect.add_empty.
    unfold Smax_mult.
    + rewrite Spect.fold_singleton;auto.
      * rewrite Max.max_0_r.
        symmetry.
        apply Spect.singleton_same.
      * repeat intro.
        subst;auto.
    + assert (~ Spect.eq m Spect.empty).
      { rewrite Spect.not_empty_In.
        assumption. }
      specialize (H1 H2).
      clear e H2.
      destruct H1 as [max_m h_max_m].
      rewrite Smax_mult_add;auto.
      destruct (Max.max_spec n (Smax_mult m)) as [[h_max1 h_max2]|[h_max1 h_max2]].
      * exists max_m.
        rewrite Spect.add_other.
        -- rewrite <- h_max_m.
           assumption.
        -- intro abs.
           rewrite abs in *.
           rewrite Spect.not_In in H.
           exfalso;omega.
      * exists x.
        rewrite h_max2.
        rewrite Spect.add_same.
        rewrite Spect.not_In in H.
        omega.
  - intro abs.
    elim abs.
    reflexivity.
Qed.


Lemma Smax_spec_max :
  forall s x,
    ~Spect.eq s Spect.empty ->
    (forall y, (s[y] <= s[x])) -> Smax_mult s = s[x].
Proof.
  intros s x hnonempty h.
  apply le_antisym.
  - destruct (@Smax_max_mult_ex s);auto.
    rewrite H.
    apply h.
  - apply Smax_mult_spec.
Qed.


Corollary Smax_spec1_iff : forall s,
    ~Spect.eq s Spect.empty ->
    forall x,
      Spect.In x (Smax s) <-> forall y, (s[y] <= s[x]).
Proof.
  intros s Hs x.
  assert (h_empty:=Hs).
  rewrite <- Smax_empty in Hs.
  rewrite Spect.not_empty_In in Hs.
  destruct Hs as [z Hz].
  split; intro Hx.
  - intro y. assert (Hx' := Hx). rewrite Smax_In_mult in Hx.
    + rewrite <- Hx. now apply Smax_spec1.
    + now rewrite <- Smax_subset.
  - assert (h:=@Smax_spec_max s x h_empty Hx).
    rewrite Smax_max_mult;auto.
Qed.


Lemma support_Smax_non_nil : forall config, Spect.support (Smax (!! config)) <> nil.
Proof. intros config Habs. rewrite Spect.support_nil, Smax_empty in Habs. apply (spec_non_nil _ Habs). Qed.

(** ***  Computational equivalent of having a majority tower  **)

Lemma Majority_MajTower_at : forall config pt,
  Spect.support (Smax (!! config)) = pt :: nil -> MajTower_at pt config.
Proof.
intros config pt Hmaj x Hx. apply Smax_spec2.
- rewrite <- Spect.support_In, Hmaj. now left.
- rewrite <- Spect.support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

Theorem MajTower_at_equiv : forall config pt, MajTower_at pt config <->
  Spect.support (Smax (!! config)) = pt :: nil.
Proof.
intros config pt. split; intro Hmaj.
* apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz.
  apply (NoDupA_equivlistA_PermutationA _).
  + apply NoDupA_singleton.
  + apply Spect.support_NoDupA.
  + intro y. rewrite InA_singleton.
    rewrite Spect.support_In, Smax_spec1_iff; try apply spec_non_nil; [].
    split; intro Hpt.
    - subst y. intro x. destruct (Rdec x pt).
      -- subst x. reflexivity.
      -- apply lt_le_weak. now apply (Hmaj x).
    - destruct (Rdec y pt) as [? | Hy]; trivial.
      exfalso. apply (Hmaj y) in Hy. elim (lt_irrefl (!! config)[pt]).
      eapply le_lt_trans; try eassumption; [].
      apply Hpt.
* intros x Hx. apply Smax_spec2.
  - rewrite <- Spect.support_In, Hmaj. now left.
  - rewrite <- Spect.support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

(** **  Some properties of [forbidden]  **)

Instance forbidden_invariant : Proper (Pos.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [pt1 [pt2 [Hneq Hpt]]]]; split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

Lemma forbidden_even : forall pos, forbidden pos -> Nat.Even nG.
Proof. now intros pos [? _]. Qed.

Lemma forbidden_support_length : forall config, forbidden config ->
  Spect.size (!! config) = 2.
Proof.
intros conf [Heven [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]].
rewrite <- (@Spect.cardinal_total_sub_eq (Spect.add pt2 (Nat.div2 N.nG) (Spect.singleton pt1 (Nat.div2 N.nG)))
                                        (!! conf)).
+ rewrite Spect.size_add; try now apply half_size_pos.
  destruct (Spect.In_dec pt2 (Spect.singleton pt1 (Nat.div2 N.nG))) as [Hin | Hin].
  - exfalso. rewrite Spect.In_singleton in Hin.
    destruct Hin. now elim Hdiff.
  - rewrite Spect.size_singleton; trivial. apply half_size_pos.
+ intro pt. destruct (Rdec pt pt2), (Rdec pt pt1); subst.
  - now elim Hdiff.
  - rewrite Spect.add_spec, Spect.singleton_spec.
    unfold R.eq_dec, Rdef.eq_dec in *. do 2 Rdec_full; contradiction || omega.
  - rewrite Spect.add_other, Spect.singleton_spec.
      now unfold R.eq_dec, Rdef.eq_dec in *; Rdec_full; contradiction || omega.
      now unfold R.eq, Rdef.eq; auto.
  - rewrite Spect.add_other, Spect.singleton_spec.
      now unfold R.eq_dec, Rdef.eq_dec in *; Rdec_full; contradiction || omega.
      now unfold R.eq, Rdef.eq; auto.
+ rewrite Spect.cardinal_add, Spect.cardinal_singleton, Spect.cardinal_from_config.
  unfold N.nB.
  replace (Nat.div2 N.nG + Nat.div2 N.nG) with (2 * Nat.div2 N.nG) by lia.
  rewrite <- Nat.double_twice, plus_0_r. symmetry. apply even_double. now rewrite Even.even_equiv.
Qed.

Lemma forbidden_injective_invariant : forall f, injective eq eq f ->
  forall pos, forbidden pos -> forbidden (Pos.map f pos).
Proof.
unfold forbidden.
intros f Hf pos [HnG [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]].
split;trivial.
exists (f pt1), (f pt2). split.
- intro Heq. apply Hdiff. now apply Hf in Heq.
- split; rewrite <- Spect.from_config_map, Spect.map_injective_spec;
  assumption || (now intros ? ? Heq; rewrite Heq) || apply Hf.
Qed.

Theorem forbidden_similarity_iff : forall (sim : similarity) pos,
  forbidden (Pos.map sim pos) <-> forbidden pos.
Proof.
intros sim pos. split.
- setoid_rewrite <- Pos.map_id at 3. rewrite <- (bij_inv_bij_id sim).
  setoid_rewrite <- Pos.map_merge at 2; try now intros ? ? Heq; rewrite Heq.
  apply forbidden_injective_invariant, injective_retraction, similarity_injective.
- apply forbidden_injective_invariant, similarity_injective.
Qed.

Lemma support_Smax_1_not_forbidden : forall config pt,
  MajTower_at pt config -> ~forbidden config.
Proof.
intros config pt Hmaj. rewrite MajTower_at_equiv in Hmaj.
assert (Hmax : forall x, Spect.In x (Smax (!! config)) <-> x = pt).
{ intro x. rewrite <- Spect.support_spec, Hmaj. split.
  - intro Hin. inversion_clear Hin. assumption. inversion H.
  - intro. subst x. now left. }
intro Hforbidden.
assert (Hsuplen := forbidden_support_length Hforbidden).
destruct Hforbidden as [Heven [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]].
assert (Hsup : Permutation (Spect.support (!! config)) (pt1 :: pt2 :: nil)).
{ assert (Hin1 : InA eq pt1 (Spect.support (!! config))).
  { rewrite Spect.support_spec. unfold Spect.In. rewrite Hpt1. apply half_size_pos. }
  assert (Hin2 : InA eq pt2 (Spect.support (!! config))).
  { rewrite Spect.support_spec. unfold Spect.In. rewrite Hpt2. apply half_size_pos. }
  apply (PermutationA_split _) in Hin1. destruct Hin1 as [l Hl]. rewrite Hl in Hin2.
  inversion_clear Hin2; try now subst; elim Hdiff.
  rewrite Spect.size_spec, Hl in Hsuplen. destruct l as [| x [| ? ?]]; simpl in Hsuplen; try omega.
  inversion_clear H; (now inversion H0) || subst. now rewrite <- PermutationA_Leibniz. }
assert (Hpt : pt = pt1 \/ pt = pt2).
{ assert (Hin : In pt (pt1 :: pt2 :: nil)).
  { rewrite <- Hsup, <- InA_Leibniz, Spect.support_spec,
            <- (Smax_subset (!! config)), <- Spect.support_spec, Hmaj.
    now left. }
inversion_clear Hin; auto. inversion_clear H; auto. inversion H0. }
apply (lt_irrefl (Nat.div2 N.nG)). destruct Hpt; subst pt.
- rewrite <- Hpt1 at 2. rewrite <- Hpt2. apply Smax_spec2; try now rewrite Hmax.
  rewrite Hmax. auto.
- rewrite <- Hpt1 at 1. rewrite <- Hpt2. apply Smax_spec2; now rewrite Hmax.
Qed.

Definition no_Majority conf := (Spect.size (Smax (!! conf)) > 1)%nat.

(* forbidden_support_length already proves the <- direction *)
Lemma forbidden_equiv : forall conf,
  forbidden conf <-> no_Majority conf /\ Spect.size (!! conf) = 2%nat.
Proof.
  intro conf. unfold no_Majority. split.
  - intro Hforbidden. split.
    + rewrite Spect.size_spec. destruct (Spect.support (Smax (!! conf))) as [| pt1 [| pt2 l]] eqn:Hmax.
      * exfalso. revert Hmax. apply support_Smax_non_nil.
      * exfalso. revert Hmax Hforbidden. rewrite <- MajTower_at_equiv. apply support_Smax_1_not_forbidden.
      * simpl. omega.
    + now apply forbidden_support_length.
  - intros [Hlen H2]. rewrite Spect.size_spec in *.
    destruct (Spect.support (!! conf)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try (now simpl in H2; omega); [].
    red.
    assert (Hlen':(Spect.size (Smax (!! conf)) = 2)%nat).
    { assert (Spect.size (Smax (!! conf)) <= 2)%nat.
      { unfold Smax.
        rewrite <- H2, <- Hsupp, <- Spect.size_spec.
        apply Spect.size_filter.
        now repeat intro; subst. }
      rewrite <- Spect.size_spec in Hlen. omega. }
    clear Hlen.
    (* let us reformulate this in a more convenient way *)
   cut (exists pt0 pt3 : Spect.elt,
      pt0 <> pt3 /\
      (!! conf)[pt0] = Nat.div2 N.nG /\ (!! conf)[pt3] = Nat.div2 N.nG /\ Nat.Even N.nG).
   { intros h.
     decompose [ex and] h; split; try assumption.
     exists x, x0; intuition. }
   exists pt1, pt2.
   split.
    * assert (hnodup:NoDupA R.eq (pt1 :: pt2 :: nil)). {
        rewrite <- Hsupp.
        apply Spect.support_NoDupA. }
      intro abs.
      subst.
      inversion hnodup;subst.
      elim H1.
      constructor.
      reflexivity.
    * assert (h:=@Spect.support_filter _ (eqb_Smax_mult_compat (!!conf)) (!! conf)).
      change (Spect.filter (fun _ : Spect.elt => Nat.eqb (Smax_mult (!! conf))) (!! conf))
      with (Smax (!!conf)) in h.
      assert (Hlen'': length (Spect.support (Smax (!! conf))) = length (Spect.support (!! conf))).
      { rewrite Spect.size_spec in Hlen'. now rewrite Hsupp. }
      assert (h2:=@NoDupA_inclA_length_PermutationA
                    _ R.eq _
                    (Spect.support (Smax (!! conf)))
                    (Spect.support (!! conf))
                    (Spect.support_NoDupA _)
                    (Spect.support_NoDupA _)
                    h Hlen'').
      assert (toto:=@Spect.cardinal_from_config conf).
      unfold N.nB in toto.
      rewrite <- plus_n_O in toto.
      assert (~ R.eq pt1 pt2). {
        intro abs.
        repeat red in abs.
        rewrite abs in Hsupp.
        assert (hnodup:=Spect.support_NoDupA (!! conf)).
        rewrite  Hsupp in hnodup.
        inversion hnodup;subst.
        match goal with
        | H: ~ InA R.eq pt2 (pt2 :: nil) |- _ => elim H
        end.
        constructor 1.
        reflexivity. }
      assert (heq_conf:Spect.eq (!!conf)
                               (Spect.add pt1 ((!! conf)[pt1])
                                         (Spect.add pt2 ((!! conf)[pt2]) Spect.empty))).
      { red.
        intros x.
        destruct (R.eq_dec x pt1) as [heqxpt1 | hneqxpt1].
        - rewrite heqxpt1.
          rewrite Spect.add_same.
          rewrite (Spect.add_other pt2 pt1).
          + rewrite Spect.empty_spec.
            omega.
          + assumption.
        - rewrite Spect.add_other;auto.
          destruct (R.eq_dec x pt2) as [heqxpt2 | hneqxpt2].
          + rewrite heqxpt2.
            rewrite Spect.add_same.
            rewrite Spect.empty_spec.
            omega.
          + rewrite Spect.add_other;auto.
            rewrite Spect.empty_spec.
            rewrite <- Spect.not_In.
            rewrite <- Spect.support_spec.
            rewrite Hsupp.
            intro abs.
            inversion abs;try contradiction;subst.
            inversion H1;try contradiction;subst.
            rewrite InA_nil in H3.
            assumption. }
      rewrite heq_conf in toto.
      rewrite Spect.cardinal_fold_elements in toto.
      assert (fold_left (fun (acc : nat) (xn : Spect.elt * nat) => snd xn + acc)
                        ((pt1, (!! conf)[pt1])
                           :: (pt2, (!! conf)[pt2])
                           :: nil) 0
              = N.nG).
      { rewrite <- toto.
        eapply MMultiset.Preliminary.fold_left_symmetry_PermutationA with (eqA := Spect.eq_pair);auto.
        - apply Spect.eq_pair_equiv.
        - apply eq_equivalence.
        - repeat intro;subst.
          rewrite H1.
          reflexivity.
        - intros x y z. omega.
        - symmetry.
          transitivity ((pt1, (!! conf)[pt1]) :: (Spect.elements (Spect.add pt2 (!! conf)[pt2] Spect.empty))).
          eapply Spect.elements_add_out;auto.
          + rewrite heq_conf, Spect.add_same. cut ((!! conf)[pt1] > 0). omega.
            change (Spect.In pt1 (!! conf)). rewrite <- Spect.support_In, Hsupp. now left.
          + rewrite Spect.add_empty.
            rewrite Spect.In_singleton.
            intros [abs _].
            contradiction.
          + apply permA_skip.
            * reflexivity.
            * transitivity ((pt2, (!! conf)[pt2]) :: Spect.elements Spect.empty).
              eapply Spect.elements_add_out;auto.
              -- change (Spect.In pt2 (!! conf)). rewrite <- Spect.support_In, Hsupp. now right; left.
              -- apply Spect.In_empty.
              -- now rewrite Spect.elements_empty. }
      simpl in H0.
      rewrite <- plus_n_O in H0.

      assert ((!! conf)[pt2] = (!! conf)[pt1]).
      { assert (hfilter:= @Spect.filter_In _ (eqb_Smax_mult_compat (!! conf))).
        transitivity (Smax_mult (!! conf)).
        + specialize (hfilter pt2 (!!conf)).
          replace (Spect.filter (fun _ : Spect.elt => Nat.eqb (Smax_mult (!! conf))) (!!conf))
          with (Smax (!!conf)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply Spect.support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 2; constructor 1.
               reflexivity.
            -- symmetry.
               rewrite <- Nat.eqb_eq.
               assumption.
          * trivial.
        + specialize (hfilter pt1 (!!conf)).
          replace (Spect.filter (fun _ : Spect.elt => Nat.eqb (Smax_mult (!! conf))) (!!conf))
          with (Smax (!!conf)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply Spect.support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 1.
               reflexivity.
            -- rewrite <- Nat.eqb_eq.
               assumption.
          * trivial. }
      rewrite H1 in *|-*.
      assert ( 0 + 2 *(!! conf)[pt1] = N.nG).
      { omega. }
      assert (Nat.even N.nG).
      { rewrite <- H3.
        rewrite (Nat.even_add_mul_2 0 ((!! conf)[pt1])).
        apply Nat.even_0. }
      split;[| split].
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl  Nat.b2n in H3.
         repeat rewrite <- plus_n_O,plus_O_n in H3.
         omega.
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl  Nat.b2n in H3.
         repeat rewrite <- plus_n_O,plus_O_n in H3.
         omega.
      -- apply Even.even_equiv.
         apply Even.even_equiv.
         apply Nat.even_spec.
         assumption.
Qed.

Lemma not_forbidden_not_majority_length : forall conf,
  no_Majority conf -> ~forbidden conf -> (Spect.size (!! conf) >= 3)%nat.
Proof.
intros conf H1 H2.
assert (Spect.size (!! conf) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption.
  do 2 rewrite Spect.size_spec. apply (NoDupA_inclA_length _).
  - apply Spect.support_NoDupA.
  - unfold Smax. apply Spect.support_filter. repeat intro. now subst. }
 destruct (Spect.size (!! conf)) as [| [| [| ?]]] eqn:Hlen; try omega.
exfalso. apply H2. now rewrite forbidden_equiv.
Qed.

(** **  Functions for the generic case  **)

Open Scope R_scope.

Definition mini s := List.hd 0 (sort (Spect.support s)).
Definition maxi s := List.last (sort (Spect.support s)) 0.
Definition middle s := nth 1 (sort (Spect.support s)) 0.

Instance mini_compat : Proper (Spect.eq ==> eq) mini.
Proof. intros s1 s2 Hs. unfold mini. now rewrite Hs. Qed.

Instance maxi_compat : Proper (Spect.eq ==> eq) maxi.
Proof. intros s1 s2 Hs. unfold maxi. now rewrite Hs. Qed.

Instance middle_compat : Proper (Spect.eq ==> eq) middle.
Proof. intros s1 s2 Hs. unfold middle. now rewrite Hs. Qed.

Definition is_extremal r (s : Spect.t) :=
  if Rdec r (mini s) then true else
  if Rdec r (maxi s) then true else false.

Instance is_extremal_compat : Proper (eq ==> Spect.eq ==> eq) is_extremal.
Proof.
intros x y ? s s' Hs. subst y. unfold is_extremal, mini, maxi.
destruct (Rdec x (hd 0 (sort (Spect.support s)))), (Rdec x (hd 0 (sort (Spect.support s'))));
try rewrite Hs in *; contradiction || trivial.
destruct (Rdec x (last (sort (Spect.support s)) 0)), (Rdec x (last (sort (Spect.support s')) 0));
try rewrite Hs in *; contradiction || reflexivity.
Qed.

Lemma is_extremal_map_monotonic_invariant : forall f, monotonic Rleb Rleb f -> injective eq eq f ->
  forall x config, is_extremal (f x) (Spect.map f (!! config)) = is_extremal x (!! config).
Proof.
intros f Hfmon Hfinj x config. unfold is_extremal, mini, maxi.
assert (Hf : Proper (R.eq ==> R.eq) f). { unfold R.eq, Rdef.eq. repeat intro. now subst. }
destruct Hfmon as [Hfinc | Hfdec].
* repeat Rdec_full; trivial; rewrite Spect.map_injective_support, (sort_map_increasing Hfinc) in *; trivial.
  + rewrite (hd_indep _ (f 0)) in Heq.
    - rewrite map_hd in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Heq.
    - rewrite map_last in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (hd_indep _ (f 0)) in Hneq.
    - elim Hneq. rewrite map_hd. now f_equal.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Hneq0.
    - elim Hneq0. rewrite map_last. now f_equal.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
* repeat Rdec_full; trivial;rewrite Spect.map_injective_support, (sort_map_decreasing Hfdec) in *; trivial.
  + rewrite (hd_indep _ (f 0)) in Heq.
    - rewrite hd_rev_last, map_last in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Heq.
    - rewrite last_rev_hd, map_hd in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Hneq0.
    - elim Hneq0. rewrite last_rev_hd, map_hd. now f_equal.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (hd_indep _ (f 0)) in Hneq.
    - elim Hneq. rewrite hd_rev_last, map_last. now f_equal.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
Qed.

Corollary is_extremal_similarity_invariant : forall (sim : similarity) config r,
  is_extremal (sim r) (Spect.map sim (!! config)) = is_extremal r (!! config).
Proof.
intros sim pos r. apply is_extremal_map_monotonic_invariant.
- apply similarity_monotonic.
- apply similarity_injective.
Qed.

(* When there is no robot (s is empty), the center is 0. *)
Definition extreme_center (s : Spect.t) := (mini s + maxi s) / 2.

Instance extreme_center_compat : Proper (Spect.eq ==> eq) extreme_center.
Proof. intros s s' Hs. unfold extreme_center, mini, maxi. now rewrite Hs. Qed.

Lemma extreme_center_similarity : forall (sim : similarity) s, ~Spect.eq s Spect.empty ->
  extreme_center (Spect.map sim s) = sim (extreme_center s).
Proof.
intros sim s Hs.
assert (Hsim1 : Proper (R.eq ==> R.eq) sim). { intros x y Hxy. now rewrite Hxy. }
assert (Hsim2 := similarity_injective sim).
unfold extreme_center, mini, maxi.
destruct (similarity_monotonic sim) as [Hinc | Hdec].
* rewrite Spect.map_injective_support, (sort_map_increasing Hinc); trivial.
  assert (Hperm := Permuted_sort (Spect.support s)). destruct (sort (Spect.support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- Spect.support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. symmetry. now apply similarity_middle.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
* rewrite Spect.map_injective_support, (sort_map_decreasing Hdec); trivial.
  rewrite last_rev_hd, hd_rev_last.
  assert (Hperm := Permuted_sort (Spect.support s)). destruct (sort (Spect.support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- Spect.support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. rewrite similarity_middle. field.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
(* Anomaly: error with no safe_id attached: Uncaught exception Stm.Vcs_aux.Expired.. *)
Qed.

Lemma extreme_center_similarity_invariant : forall (sim : similarity) config,
  extreme_center (Spect.map sim (!! config)) = sim (extreme_center (!! config)).
Proof. intros. apply extreme_center_similarity. apply spec_non_nil. Qed.


(** *  The robogram solving the gathering **)

(** I works as follows:
    1) if there is a majority stack, everyone goes there;
    2) if there are three stacks, everyone goes on the middle one;
    3) otherwise, robots located at non extremal locations go to the middle of the extremal locations.
    The last case will necessarily end into one of the first two, ensuring termination.
**)


Definition robogram_pgm (s : Spect.t) : R.t :=
  match Spect.support (Smax s) with
    | nil => 0 (* only happen with no robots *)
    | pt :: nil => pt (* case 1: one majority stack *)
    | _ => (* several majority stacks *)
           if beq_nat (Spect.size s) 3
           then middle s else
           if is_extremal 0 s then 0 else extreme_center s
  end.

(** The robogram is invariant by permutation of spectra. *)
Instance robogram_pgm_compat : Proper (Spect.eq ==> eq) robogram_pgm.
Proof.
unfold robogram_pgm. intros s s' Hs. assert (Hperm := Spect.support_compat (Smax_compat Hs)).
destruct (Spect.support (Smax s)) as [| pt [| pt2 l]].
+ now rewrite (PermutationA_nil _ Hperm).
+ symmetry in Hperm. destruct (PermutationA_length1 _ Hperm) as [pt' [Heq Hin]]. now rewrite Hin.
+ assert (Hlength := PermutationA_length _ Hperm).
  destruct (Spect.support (Smax s')) as [| pt' [| pt2' l']]; try discriminate. rewrite Hs.
  destruct (Spect.size s' =? 3); rewrite Hs; trivial.
  destruct (is_extremal 0 s'); try rewrite Hs; reflexivity.
Qed.

Definition robogram := Build_robogram robogram_pgm robogram_pgm_compat.


(** **  General simplification lemmas for [round robogram da _] **)

Lemma round_simplify : forall da pos,
  Pos.eq (round robogram da pos)
         (fun id => match da.(step) id with
                      | None => pos id
                      | Some f =>
                          let s := !! pos in
                          match Spect.support (Smax s) with
                            | nil => pos id (* only happen with no robots *)
                            | pt :: nil => pt (* case 1: one majority stack *)
                            | _ => (* several majority stacks *)
                                   if beq_nat (Spect.size s) 3
                                   then List.nth 1 (sort (Spect.support s)) 0 else
                                   if is_extremal (pos id) s then (pos id) else extreme_center s
                          end
                    end).
Proof.
intros da pos id. unfold round.
destruct (step da id) as [simc |] eqn:Hstep, id as [g | b]; try reflexivity || now eapply Fin.case0; exact b.
remember (pos (Good g)) as pt.
(* Simplify the similarity *)
assert (Hratio : (simc pt).(ratio) <> 0). { eapply da.(step_ratio). eassumption. }
destruct (similarity_in_R (simc pt)) as [k [Hk Hsim]].
assert (Hinvsim : forall x, (simc pt ⁻¹) x = x / k + center (simc pt)).
{ apply inverse_similarity_in_R; trivial. destruct Hk; lra. }
rewrite Hinvsim.
assert(Hsimccompat : Proper (R.eq ==> R.eq) (simc pt)). { intros ? ? Heq. now rewrite Heq. }
assert (Hsim_inj : injective R.eq R.eq (simc pt)) by now apply similarity_injective.
(* Unfold the robogram *)
unfold robogram, robogram_pgm. simpl.
assert (Hperm : PermutationA R.eq (Spect.support (Smax (!! (Pos.map (simc pt) pos))))
                                  (List.map (simc pt) (Spect.support (Smax (!! pos))))).
{ rewrite <- Spect.map_injective_support; trivial. f_equiv.
  rewrite <- Smax_similarity, Spect.from_config_map; auto. reflexivity. }
destruct (Spect.support (Smax (!! pos))) as [| pt' [| pt2' l']].
* (* Empty support *)
  simpl in Hperm. symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm.
  rewrite da.(step_center); try eassumption. hnf. field. lra.
* (* A majority stack *)
  simpl in Hperm. apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]]. rewrite Hperm.
  hnf in Hy |- *. subst y. rewrite Hsim. field. lra.
* (* No majority stack *)
  apply (PermutationA_length _) in Hperm.
  destruct (Spect.support (Smax (!! (Pos.map (simc pt) pos)))) as [| pt'' [| pt2'' l'']];
  try discriminate Hperm. clear Hperm pt' pt2' l' pt'' pt2'' l''.
  assert (Hlength : Spect.size (!! (Pos.map (simc pt) pos)) = Spect.size (!! pos)).
  { rewrite <- Spect.from_config_map; trivial. now apply Spect.map_injective_size. }
  rewrite Hlength. destruct (Spect.size (!! pos) =? 3) eqn:Hlen.
  + (* There are three towers *)
    unfold middle. rewrite <- Spect.from_config_map, Spect.map_injective_support; trivial.
    rewrite Spect.size_spec in Hlen.
    destruct (Spect.support (!! pos)) as [| pt1 [| pt2 [| pt3 [| ? ?]]]]; try discriminate Hlen.
    destruct (similarity_monotonic (simc pt)) as [Hinc | Hdec].
    - rewrite (sort_map_increasing Hinc), (nth_indep _ 0 (simc pt 0)),
              map_nth, <- Hinvsim, <- (simc pt).(Inversion); try reflexivity.
      rewrite map_length, <- Permuted_sort. simpl. omega.
    - { rewrite (sort_map_decreasing Hdec).
        assert (Heq1 : Nat.div2 (length (map (simc pt) (sort (pt1 :: pt2 :: pt3 :: nil)))) = 1%nat).
        { now rewrite map_length, <- Permuted_sort. }
        rewrite <- Heq1 at 1. rewrite odd_middle, (nth_indep _ 0 (simc pt 0)).
        + rewrite map_nth, <- Hinvsim, <- (simc pt).(Inversion), <- Heq1; reflexivity.
        + rewrite map_length, <- Permuted_sort. simpl. omega.
        + rewrite map_length, <- Permuted_sort. simpl. exists 1%nat. omega. }
  + (* Generic case *)
    change 0 with R.origin. rewrite <- (simc pt).(center_prop) at 1.
    rewrite <- Spect.from_config_map, is_extremal_similarity_invariant, da.(step_center); try eassumption.
    destruct (is_extremal pt (!! pos)).
    - (* The current robot is exremal *)
      hnf. unfold R.origin, Rdef.origin. field. lra.
    - (* The current robot is not exremal *)
      rewrite <- Spect.from_config_map, extreme_center_similarity; apply spec_non_nil || trivial.
      hnf. rewrite <- (da.(step_center) _ _ pt Hstep) at 2. now rewrite <- Hinvsim, <- (simc pt).(Inversion).
Qed.

(** ***  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, everyone goes there. **)
Lemma round_simplify_Majority : forall da conf pt,
  MajTower_at pt conf ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => pt
                    end).
Proof.
intros da conf pt Hmaj id. rewrite round_simplify.
rewrite MajTower_at_equiv in Hmaj.
destruct (step da id); try reflexivity. cbv zeta.
destruct (Spect.support (Smax (!! conf))) as [| ? [| ? ?]]; try discriminate Hmaj.
inversion Hmaj. reflexivity.
Qed.

(** If we have three towers, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall da conf,
  no_Majority conf ->
  (Spect.size (!! conf) = 3)%nat ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => nth 1 (sort (Spect.support (!!  conf))) 0
                    end).
Proof.
intros da pos Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
unfold no_Majority in Hmaj. rewrite Spect.size_spec in Hmaj.
destruct (Spect.support (Smax (!! pos))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in H3. rewrite H3. reflexivity.
Qed.

(** In the general case, all non extremal robots go to the middle of the extreme. *)
Lemma round_simplify_Generic : forall da conf,
  no_Majority conf ->
  (Spect.size (!! conf) <> 3)%nat ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => if is_extremal (conf id) (!! conf)
                                  then conf id else extreme_center (!! conf)
                    end).
Proof.
intros da pos Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
unfold no_Majority in Hmaj. rewrite Spect.size_spec in Hmaj.
destruct (Spect.support (Smax (!! pos))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in H3. rewrite H3. reflexivity.
Qed.


(* TODO: make a case analysis theorem about robogram *)
Close Scope R_scope.


(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Majority_grow :  forall pt config da, MajTower_at pt config ->
  (!! config)[pt] <= (!! (round robogram da config))[pt].
Proof.
intros pt pos da Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Pos.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - Rdec. Rdec_full; apply le_n_S + apply le_S; apply IHl.
  - Rdec_full; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall pt pt' pos da, pt <> pt' ->
  MajTower_at pt pos -> (!! (round robogram da pos))[pt'] <= (!! pos)[pt'].
Proof.
intros pt pt' pos da Hdiff Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Pos.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - Rdec_full; try contradiction. Rdec_full; try apply le_S; apply IHl.
  - Rdec_full; try apply le_n_S; apply IHl.
Qed.

(** Whenever there is a majority stack, it remains forever so. **)
Theorem MajTower_at_forever : forall pt pos da, MajTower_at pt pos -> MajTower_at pt (round robogram da pos).
Proof.
intros pt pos da Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! pos)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
- eapply Majority_grow; eauto.
Qed.

Theorem Majority_not_forbidden : forall pt config, MajTower_at pt config -> ~forbidden config.
Proof.
intros pt config Hmaj. rewrite forbidden_equiv. unfold no_Majority. intros [Hmaj' _].
rewrite MajTower_at_equiv in Hmaj. rewrite Spect.size_spec, Hmaj in Hmaj'. simpl in *. omega.
Qed.

(** **  Properties in the generic case  **)

Open Scope R_scope.
(** If we have no majority stack (hence more than one stack), then the extreme locations are different. **)
Lemma Generic_min_max_lt_aux : forall l, (length l > 1)%nat -> NoDupA eq l ->
  hd 0 (sort l) < last (sort l) 0.
Proof.
intros l Hl Hnodup. rewrite Permuted_sort in Hl.
apply (@PermutationA_NoDupA _ eq _ l (sort l)) in Hnodup.
+ apply Rle_neq_lt.
  - apply sort_min. setoid_rewrite Permuted_sort at 3. apply last_In.
    destruct (sort l); discriminate || simpl in Hl; omega.
  - apply (hd_last_diff _); auto.
+ rewrite PermutationA_Leibniz. apply Permuted_sort.
Qed.

Lemma Generic_min_max_lt : forall config,
  no_Majority config -> mini (!! config) < maxi (!! config).
Proof.
intros config Hmaj. apply Generic_min_max_lt_aux.
+ apply lt_le_trans with (Spect.size (Smax (!! config))); trivial.
  rewrite Spect.size_spec. apply (NoDupA_inclA_length _).
  - apply Spect.support_NoDupA.
  - apply Spect.support_filter. repeat intro. now subst.
+ apply Spect.support_NoDupA.
Qed.

Corollary Generic_min_mid_lt : forall config,
  no_Majority config -> mini (!! config) < extreme_center (!! config).
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Corollary Generic_mid_max_lt : forall config,
  no_Majority config -> extreme_center (!! config) < maxi (!! config).
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Theorem Generic_min_same : forall da conf,
  no_Majority conf -> (Spect.size (!! conf) <> 3)%nat ->
  mini (!! (round robogram da conf)) = mini (!! conf).
Proof.
intros da config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hhdin := sort_non_nil config). apply (hd_In 0%R) in Hhdin.
rewrite <- Permuted_sort in Hhdin at 2.
rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hhdin.
destruct Hhdin as [id Hid].
(* Its position before and after are the same *)
assert (config id = round robogram da config id).
{ rewrite round_simplify_Generic; trivial; [].
  destruct (step da id); trivial; [].
  unfold is_extremal. Rdec_full; try reflexivity; [].
  elim Hneq. rewrite Hid. apply hd_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_min.
  rewrite <- Hid, <- InA_Leibniz, Spect.support_In, H. apply Spect.pos_in_config.
* apply sort_min.
  rewrite <- InA_Leibniz, Spect.support_In. apply Spect.from_config_In.
  exists id. apply min_sort.
  + rewrite H, <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
  + intros y Hy. rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite round_simplify_Generic; trivial; [].
    destruct (step da id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_min. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
      -- apply sort_min. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
      -- apply Rlt_le. change (mini (!! config) < extreme_center (!! config)). now apply Generic_min_mid_lt.
    - apply sort_min. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
Qed.

Theorem Generic_max_same : forall da conf,
  no_Majority conf -> (Spect.size (!! conf) <> 3)%nat ->
  maxi (!! (round robogram da conf)) = maxi (!! conf).
Proof.
intros da config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hlastin := sort_non_nil config). apply (last_In 0%R) in Hlastin.
rewrite <- Permuted_sort in Hlastin at 2.
rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hlastin.
destruct Hlastin as [id Hid].
(* Its position before and after are the same *)
assert (config id = round robogram da config id).
{ rewrite round_simplify_Generic; trivial; [].
  destruct (step da id); trivial; [].
  unfold is_extremal. repeat Rdec_full; try reflexivity; [].
  elim Hneq0. rewrite Hid. apply last_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_max.
  rewrite <- InA_Leibniz, Spect.support_In. apply Spect.from_config_In.
  exists id. apply max_sort.
  + rewrite H, <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
  + intros y Hy. rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite round_simplify_Generic; trivial; [].
    destruct (step da id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_max. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
      -- apply sort_max. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
      -- apply Rlt_le. change (extreme_center (!! config) < maxi (!! config)). now apply Generic_mid_max_lt.
    - apply sort_max. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
* apply sort_max.
  rewrite <- Hid, <- InA_Leibniz, Spect.support_In, H. apply Spect.pos_in_config.
Qed.


Corollary Generic_extreme_center_same : forall da conf,
  no_Majority conf -> (Spect.size (!! conf) <> 3)%nat ->
  extreme_center (!! (round robogram da conf)) = extreme_center (!! conf).
Proof.
intros da conf Hmaj Hlen. unfold extreme_center.
now rewrite (Generic_min_same _ Hmaj Hlen), (Generic_max_same _ Hmaj Hlen).
Qed.

Theorem Generic_min_mult_same : forall da conf,
  no_Majority conf -> (Spect.size (!! conf) <> 3)%nat ->
  (!! (round robogram da conf))[mini (!! conf)] = (!! conf)[mini (!! conf)].
Proof. 
intros da conf Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite Spect.from_config_spec, Pos.list_spec.
induction Spect.Names.names as [| id l]; simpl.
* reflexivity.
* destruct (step da id).
  + repeat Rdec_full.
    - f_equal. apply IHl.
    - destruct (is_extremal (conf id) (!! conf)); try contradiction; [].
      elim (Rlt_irrefl (mini (!! conf))). rewrite <- Heq at 2. now apply Generic_min_mid_lt.
    - revert Hneq. rewrite Heq. unfold is_extremal. Rdec. intro Habs. now elim Habs.
    - apply IHl.
  + Rdec_full.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Theorem Generic_max_mult_same : forall da conf,
  no_Majority conf -> (Spect.size (!! conf) <> 3)%nat ->
  (!! (round robogram da conf))[maxi (!! conf)] = (!! conf)[maxi (!! conf)].
Proof. 
intros da conf Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite Spect.from_config_spec, Pos.list_spec.
induction Spect.Names.names as [| id l]; simpl.
* reflexivity.
* destruct (step da id).
  + repeat Rdec_full.
    - f_equal. apply IHl.
    - destruct (is_extremal (conf id) (!! conf)); try contradiction; [].
      elim (Rlt_irrefl (maxi (!! conf))). rewrite <- Heq at 1. now apply Generic_mid_max_lt.
    - revert Hneq. rewrite Heq. unfold is_extremal. Rdec. Rdec_full; intro Habs; now elim Habs.
    - apply IHl.
  + Rdec_full.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Close Scope R_scope.

Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= N.nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace N.nG with (N.nG + N.nB) by (unfold N.nB; omega).
rewrite <- (Spect.cardinal_from_config config).
rewrite <- (@Spect.add_remove_id pt1 _ (!! config) (reflexivity _)) at 4.
rewrite Spect.cardinal_add.
rewrite <- (@Spect.add_remove_id pt2 _ (!! config) (reflexivity _)) at 6.
rewrite Spect.remove_add_comm, Spect.cardinal_add; trivial.
rewrite <- (@Spect.add_remove_id pt3 _ (!! config) (reflexivity _)) at 8.
rewrite Spect.remove_add_comm, Spect.remove_add_comm, Spect.cardinal_add; trivial.
omega.
Qed.

Theorem same_destination : forall da config id1 id2,
  In id1 (moving robogram da config) -> In id2 (moving robogram da config) ->
  round robogram da config id1 = round robogram da config id2.
Proof.
intros da config id1 id2 Hid1 Hid2. do 2 rewrite round_simplify.
destruct (step da id1) eqn:Hmove1; [destruct (step da id2) eqn:Hmove2 |].
* (* the real case *)
  cbv zeta.
  destruct (Spect.support (Smax (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
  + (* no robots *)
    rewrite Spect.support_nil, Smax_empty in Hmaj. elim (spec_non_nil _ Hmaj).
  + (* a majority tower *)
    reflexivity.
  + destruct (Spect.size (!! config) =? 3) eqn:Hlen.
    - (* three towers *)
      reflexivity.
    - { (* generic case *)
        rewrite Nat.eqb_neq in Hlen. rename Hmaj into Hmaj'.
        assert (Hmaj : no_Majority  config).
        { unfold no_Majority. rewrite Spect.size_spec, Hmaj'. simpl. omega. } clear Hmaj'.
        destruct (is_extremal (config id1) (!! config)) eqn:Hextreme1.
        + exfalso. unfold moving in Hid1. rewrite filter_In in Hid1. destruct Hid1 as [_ Hid1].
          destruct (R.eq_dec (round robogram da config id1) (config id1)) as [_ | Hneq]; try discriminate.
          apply Hneq. rewrite round_simplify_Generic; trivial.
          destruct (step da id1); try reflexivity. now rewrite Hextreme1.
        + destruct (is_extremal (config id2) (!! config)) eqn:Hextreme2.
          - exfalso. unfold moving in Hid2. rewrite filter_In in Hid2. destruct Hid2 as [_ Hid2].
            destruct (R.eq_dec (round robogram da config id2) (config id2)) as [_ | Hneq]; try discriminate.
            apply Hneq. rewrite round_simplify_Generic; trivial.
            destruct (step da id2); try reflexivity. now rewrite Hextreme2.
          - reflexivity. }
* apply moving_active in Hid2. unfold active in Hid2.
  rewrite filter_In, Hmove2 in Hid2. destruct Hid2; discriminate.
* apply moving_active in Hid1. unfold active in Hid1.
  rewrite filter_In, Hmove1 in Hid1. destruct Hid1; discriminate.
Qed.

Lemma towers_elements_3 : forall config pt1 pt2,
  (Spect.size (!! config) >= 3)%nat ->
  Spect.In pt1 (!! config) -> Spect.In pt2 (!! config) -> pt1 <> pt2 ->
  exists pt3, pt1 <> pt3 /\ pt2 <> pt3 /\ Spect.In pt3 (!! config).
Proof.
intros config pt1 pt2 Hlen Hpt1 Hpt2 Hdiff12.
rewrite <- Spect.support_In in *. rewrite Spect.size_spec in Hlen.
apply (PermutationA_split _) in Hpt1. destruct Hpt1 as [supp1 Hperm].
rewrite Hperm in Hpt2. inversion_clear Hpt2; try (now elim Hdiff12); []. rename H into Hpt2.
apply (PermutationA_split _) in Hpt2. destruct Hpt2 as [supp2 Hperm2].
rewrite Hperm2 in Hperm. rewrite Hperm in Hlen.
destruct supp2 as [| pt3 supp]; try (now simpl in Hlen; omega); [].
exists pt3.
rewrite <- Spect.support_In. assert (Hnodup := Spect.support_NoDupA (!! config)).
rewrite Hperm in *. inversion_clear Hnodup. inversion_clear H0. repeat split.
- intro Habs. subst. apply H. now right; left.
- intro Habs. subst. apply H1. now left.
- now right; right; left.
Qed.

(* TODO: move it in FormalismRd.v *)
Lemma increase_move :
  forall r conf da pt,
    ((!! conf)[pt] < (!! (round r da conf))[pt])%nat ->
    exists id, round r da conf id = pt /\ round r da conf id <> conf id.
Proof.
  intros r conf da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (Rdec_bool ((round r da conf x))  pt)
                             (negb (Rdec_bool (conf x) pt)))) Names.names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id.
    rewrite andb_true_iff, negb_true_iff, Rdec_bool_true_iff, Rdec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, round r da conf id <> pt \/ conf id = pt).
    { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- Rdec_bool_false_iff, <- Rdec_bool_true_iff. apply Hex, Names.In_names. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt.
    do 2 rewrite Spect.from_config_spec, Spect.Pos.list_spec.
    induction Spect.Names.names as [| id l]; simpl; trivial.
    destruct (R.eq_dec (round r da conf id) pt) as [Heq | Heq].
    + destruct (R.eq_dec (conf id) pt); try omega. specialize (Hg id). intuition.
    + destruct (R.eq_dec (conf id) pt); omega.
Qed.

(* Because of same_destination, we can strengthen the previous result as a equivalence. *)
Lemma increase_move_iff :
  forall conf da pt,
    ((!! conf)[pt] < (!! (round robogram da conf))[pt])%nat <->
    exists id, round robogram da conf id = pt /\ round robogram da conf id <> conf id.
Proof.
intros conf da pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', In id' (moving robogram da conf) -> round robogram da conf id' = pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; rewrite moving_spec; auto. }
  assert (Hstay : forall id, conf id = pt -> round robogram da conf id = pt).
  { intros id' Hid'. destruct (Rdec (round robogram da conf id') pt) as [Heq | Heq]; trivial.
    assert (Habs := Heq). rewrite <- Hid', <- moving_spec in Habs. apply Hdest in Habs. contradiction. }
  do 2 rewrite Spect.from_config_spec, Spect.Pos.list_spec.
  assert (Hin : In id Spect.Names.names) by apply Names.In_names.
  induction Spect.Names.names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. destruct (R.eq_dec (conf id) pt) as [Heq | Heq].
    - rewrite <- Hid in Heq. now elim Hroundid.
    - destruct (R.eq_dec (round robogram da conf id) pt ) as [Hok | Hko]; try contradiction; [].
      apply le_n_S. induction l; simpl.
      -- reflexivity.
      -- repeat Rdec_full; try now idtac + apply le_n_S + apply le_S; apply IHl.
         elim Hneq. now apply Hstay.
  + apply IHl in H. simpl. unfold R.eq_dec, Rdef.eq_dec in *. repeat Rdec_full; try omega.
    elim Hneq. apply Hdest. now rewrite moving_spec, Heq.
Qed.


(* Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_forbidden : forall da conf, ~forbidden conf -> ~forbidden (round robogram da conf).
Proof.
intros da conf Hok.
(* Three cases for the robogram *)
destruct (Spect.support (Smax (!! conf))) as [| pt [| pt' l']] eqn:Hmaj.
{ (* Absurd case: no robot *)
  intros _. apply (support_Smax_non_nil _ Hmaj). }
{ (* There is a majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  apply Majority_not_forbidden with pt. now apply MajTower_at_forever. }
{ rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority conf). { unfold no_Majority. rewrite Spect.size_spec, Hmaj'. simpl. omega. }
  clear pt pt' l' Hmaj'.
  (* A robot has moved otherwise we have the same configuration before and it is forbidden. *)
  assert (Hnil := no_moving_same_conf robogram da conf).
  destruct (moving robogram da conf) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    assert (Hmove : In rmove (moving robogram da conf)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round robogram conf *)
    assert (Hforbidden := Habs). destruct Habs as [HnG [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ round robogram da conf rmove = pt).
    { assert (Hperm : Permutation (Spect.support (!! (round robogram da conf))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
        + rewrite <- NoDupA_Leibniz. apply Spect.support_NoDupA.
        + simpl. now rewrite <- Spect.size_spec, forbidden_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz, Spect.support_spec. unfold Spect.In. rewrite Hpt1. apply half_size_pos.
          - inversion H; (now inversion H0) || subst. rewrite <- InA_Leibniz, Spect.support_spec.
            unfold Spect.In. rewrite Hpt2. apply half_size_pos. }
      assert (Hpt : In (round robogram da conf rmove) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, In g (moving robogram da conf) -> round robogram da conf g = pt).
    { intros id Hid.
      rewrite <- Hrmove_pt.
      apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 N.nG) <= (!! conf)[pt']).
    { transitivity ((!! (round robogram da conf))[pt']).
      - decompose [and or] Hpt; subst; omega.
      - generalize (@increase_move_iff conf da pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. assumption. }
    assert (Hlt : forall p, p <> pt' -> (!! conf)[p] < div2 N.nG).
    { assert (Hpt'_in : Spect.In pt' (!! conf)).
      { unfold Spect.In. eapply lt_le_trans; try eassumption. apply half_size_pos. }
      assert (Hle := not_forbidden_not_majority_length Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl N.nG).
      destruct (@towers_elements_3 conf pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 N.nG); try assumption. apply half_size_pos.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total conf Hp Hdiff13 Hdiff23); [].
        unfold Spect.In in Hpt3_in. rewrite (even_double N.nG), Nat.double_twice. omega.
        now rewrite Even.even_equiv. }
    assert (Hmaj' : MajTower_at pt' conf).
    { intros x Hx. apply lt_le_trans with (div2 N.nG); trivial. now apply Hlt. }
    apply (MajTower_at_forever da), Majority_not_forbidden in Hmaj'. contradiction. }
Qed.

Close Scope R_scope.


Section WfLexicographic_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive lexprod : A*B -> A*B -> Prop :=
  | left_lex :
      forall (x x':A) (y y':B), leA x x' -> lexprod (x, y) (x', y')
  | right_lex :
      forall (x:A) (y y':B), leB y y' -> lexprod (x, y) (x, y').

  Notation LexProd := (lexprod leA leB).

  Lemma acc_A_B_lexprod :
    forall x:A,
      Acc leA x ->
      (forall x0:A, clos_trans A leA x0 x -> well_founded leB) ->
      forall y:B, Acc leB y -> @Acc (A*B) lexprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    cut (leA x2 x); intros.
    apply IHAcc; auto with sets.
    intros.
    eapply H2.
    apply t_trans with x2; auto with sets.
    eassumption.

    red in H2.
    eapply H2.
    eauto with sets.

    injection H1.
    destruct 2.
    injection H3.
    destruct 2; auto with sets.

    rewrite <- H1.
    injection H3; intros _ Hx1.
    subst x1.
    apply IHAcc0.
    inversion H1.
    inversion H3.
    subst.
    assumption.
  Defined.

  Theorem wf_lexprod :
    well_founded leA ->
    well_founded leB -> well_founded lexprod.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a.
    apply acc_A_B_lexprod; auto with sets; intros.
  Defined.


End WfLexicographic_Product.

Definition conf_to_NxN conf :=
  let s := !! conf in
  match Spect.support (Smax s) with
    | nil => (0,0)
    | pt :: nil => (1, N.nG - s[pt])
    | _ :: _ :: _ =>
        if beq_nat (Spect.size s) 3
        then (2, N.nG - s[nth 1 (sort (Spect.support s)) 0%R])
        else (3, N.nG - (s[extreme_center s]
                         + s[hd 0%R (sort  (Spect.support s))]
                         + s[last (sort  (Spect.support s)) 0%R]))
  end.

Require Import Inverse_Image.

Let lt_conf x y := lexprod lt lt (conf_to_NxN x) (conf_to_NxN y).

Lemma wf_lt_conf: well_founded lt_conf.
Proof.
  unfold lt_conf.
  apply wf_inverse_image.
  apply wf_lexprod;apply lt_wf.
Qed.


Instance conf_to_NxN_compat: Proper (Pos.eq ==> eq * eq) conf_to_NxN.
Proof.
intros pos1 pos2 Heq. unfold conf_to_NxN.
assert (Hperm : PermutationA R.eq (Spect.support (Smax (!! pos1)))
                                  (Spect.support (Smax (!! pos2)))) by now rewrite Heq.
destruct (Spect.support (Smax (!! pos2))) as [| pt [| ? ?]] eqn:Hsupp.
+ symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm. reflexivity.
+ apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]].
  rewrite Hperm, <- Hy, Heq. reflexivity.
+ apply (PermutationA_length _) in Hperm.
  destruct (Spect.support (Smax (!! pos1))) as [| ? [| ? ?]]; try discriminate Hperm.
  rewrite Heq. destruct (Spect.size (!! pos2) =? 3); rewrite Heq; reflexivity.
Qed.

Instance lexprod_compat: Proper (eq * eq ==> eq * eq ==> iff) (lexprod lt lt).
Proof.
  intros (a,b) (a',b') (heqa , heqb) (c,d) (c',d') (heqc , heqd) .
  hnf in *|-.
  simpl in *|-.
  subst.
  reflexivity.
Qed.

Instance lt_conf_compat: Proper (Pos.eq ==> Pos.eq ==> iff) lt_conf.
Proof.
  intros pos1 pos1' heq1 pos2 pos2' heq2.
  unfold lt_conf.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Lemma conf_to_NxN_nil_spec : forall conf,
  Spect.support (Smax (!! conf)) = nil -> conf_to_NxN conf = (0, 0).
Proof. intros conf Heq. unfold conf_to_NxN. rewrite Heq. reflexivity. Qed.

Lemma conf_to_NxN_Majority_spec : forall conf pt,
  MajTower_at pt conf ->
  conf_to_NxN conf = (1, N.nG - (!! conf)[pt]).
Proof.
  intros conf pt H.
  unfold conf_to_NxN.
  rewrite MajTower_at_equiv in H. rewrite H.
  reflexivity.
Qed.

Lemma conf_to_NxN_Three_spec : forall conf,
  no_Majority conf ->
  Spect.size (!! conf) = 3 ->
  conf_to_NxN conf = (2, N.nG - (!! conf)[nth 1 (sort (Spect.support (!! conf))) 0%R]).
Proof.
intros conf Hmaj Hlen. unfold conf_to_NxN.
unfold no_Majority in Hmaj. rewrite Spect.size_spec in Hmaj.
destruct (Spect.support (Smax (!! conf))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma conf_to_NxN_Generic_spec : forall conf,
  no_Majority conf ->
  Spect.size (!!  conf) <> 3 ->
    conf_to_NxN conf = 
    (3, N.nG - ((!! conf)[extreme_center (!! conf)]
                + (!! conf)[mini (!! conf)]
                + (!! conf)[maxi (!! conf)])).
Proof.
intros conf Hmaj Hlen. unfold conf_to_NxN.
unfold no_Majority in Hmaj. rewrite Spect.size_spec in Hmaj.
destruct (Spect.support (Smax (!! conf))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma multiplicity_le_nG : forall pt conf, (!! conf)[pt] <= N.nG.
Proof.
intros pt conf. etransitivity.
- apply Spect.cardinal_lower.
- rewrite Spect.cardinal_from_config. unfold N.nB. omega.
Qed.

(* When we only have three towers, the new configuration does not create new positions. *)
Lemma support_round_Three_incl : forall conf da,
  no_Majority conf ->
  Spect.size (!!  conf) = 3 ->
  incl (Spect.support (!! (round robogram da conf)))
       (Spect.support (!! conf)).
Proof.
intros config da Hmaj Hlen pt Hin.
rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hin.
destruct Hin as [id Hid]. rewrite round_simplify_Three in Hid; trivial.
destruct (step da id).
+ rewrite <- Hid. setoid_rewrite Permuted_sort at 3. apply nth_In.
  rewrite <- Permuted_sort, <- Spect.size_spec, Hlen. omega.
+ rewrite <- InA_Leibniz, Spect.support_In, <- Hid. apply Spect.pos_in_config.
Qed.

Corollary support_decrease : forall conf da,
  no_Majority conf ->
  Spect.size (!! conf) = 3 ->
  Spect.size (!! (round robogram da conf)) <= 3.
Proof.
intros conf da Hmaj Hlen. rewrite <- Hlen.
generalize (support_round_Three_incl da Hmaj Hlen).
rewrite <- inclA_Leibniz, Spect.size_spec, Spect.size_spec.
apply (NoDupA_inclA_length _). apply Spect.support_NoDupA.
Qed.

Theorem round_lt_conf : forall da conf,
  ~forbidden conf -> moving robogram da conf <> nil ->
  lt_conf (round robogram da conf) conf.
Proof.
intros da conf Hvalid Hmove.
apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
assert (Hstep : step da gmove <> None).
{ apply moving_active in Hmove. now rewrite active_spec in Hmove. }
rewrite moving_spec in Hmove.
destruct (Spect.support (Smax (!! conf))) as [| pt [| ? ?]] eqn:Hmaj.
* (* No robots *)
  elim (support_Smax_non_nil _ Hmaj).
* (* A majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  assert (Hmaj' : MajTower_at pt (round robogram da conf)) by now apply MajTower_at_forever.
  red.
  rewrite (conf_to_NxN_Majority_spec Hmaj), (conf_to_NxN_Majority_spec Hmaj').
  apply right_lex.
  assert (Hle : (!! (round robogram da conf))[pt] <= N.nG) by apply multiplicity_le_nG.
  cut ((!! conf)[pt] < (!! (round robogram da conf))[pt]). omega.
  assert (Hdestg : round robogram da conf gmove = pt).
  { rewrite (round_simplify_Majority _ Hmaj). destruct (step da gmove); trivial. now elim Hstep. }
  rewrite increase_move_iff. eauto.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority conf).
  { unfold no_Majority. rewrite Spect.size_spec, Hmaj'. simpl. omega. } clear Hmaj'.
  destruct (eq_nat_dec (Spect.size (!! conf)) 3) as [Hlen | Hlen].
  + (* Three towers case *)
    red. rewrite (conf_to_NxN_Three_spec Hmaj Hlen).
    destruct (Spect.support (Smax (!! (round robogram da conf)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (conf_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (conf_to_NxN_Majority_spec Hmaj'). apply left_lex. omega.
    - rename Hmaj' into Hmaj''.
      assert (Hmaj' : no_Majority (round robogram da conf)).
      { unfold no_Majority. rewrite Spect.size_spec, Hmaj''. simpl. omega. } clear Hmaj''.
      assert (Hlen' : Spect.size (!! (round robogram da conf)) = 3).
      { apply le_antisym.
        + apply (support_decrease _ Hmaj Hlen).
        + apply (not_forbidden_not_majority_length Hmaj'). now apply never_forbidden. }
      rewrite (conf_to_NxN_Three_spec Hmaj' Hlen'). apply right_lex.
      rewrite <- Hlen in Hlen'.
      assert (Hperm : Permutation (Spect.support (!! (round robogram da conf)))
                                  (Spect.support (!! conf))).
      { rewrite <- PermutationA_Leibniz. apply (NoDupA_inclA_length_PermutationA _).
        - apply Spect.support_NoDupA.
        - apply Spect.support_NoDupA.
        - rewrite inclA_Leibniz. eapply support_round_Three_incl; eassumption.
        - do 2 rewrite <- Spect.size_spec. assumption. }
      rewrite Hperm.
      assert (Hup := multiplicity_le_nG (nth 1 (sort (Spect.support (!! conf))) 0%R)
                                        (round robogram da conf)).
      cut (Spect.multiplicity
              (nth 1 (sort (Spect.support (!! conf))) 0%R)
              (!! (round robogram da conf))
            >
            Spect.multiplicity
              (nth 1 (sort (Spect.support (!! conf))) 0%R)
              (!! conf)). omega.
      unfold gt. rewrite increase_move_iff.
      exists gmove. split; trivial.
      erewrite round_simplify_Three; try eassumption.
      destruct (step da gmove) as [Habs | _]; try now elim Hstep.
      destruct gmove eqn:Hid; trivial.
  + (* Generic case *)
    red. rewrite (conf_to_NxN_Generic_spec Hmaj Hlen).
    destruct (Spect.support (Smax (!! (round robogram da conf)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (conf_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (conf_to_NxN_Majority_spec Hmaj'). apply left_lex. omega.
    - { rename Hmaj' into Hmaj''.
        assert (Hmaj' : no_Majority (round robogram da conf)).
        { unfold no_Majority. rewrite Spect.size_spec, Hmaj''. simpl. omega. } clear Hmaj''.
        destruct (eq_nat_dec (Spect.size (!! (round robogram da conf))) 3)
        as [Hlen' | Hlen'].
        + rewrite (conf_to_NxN_Three_spec Hmaj' Hlen'). apply left_lex. omega.
        + rewrite (conf_to_NxN_Generic_spec Hmaj' Hlen'). apply right_lex.
          rewrite (Generic_min_same _ Hmaj Hlen), (Generic_max_same _ Hmaj Hlen).
          rewrite (Generic_min_mult_same _ Hmaj Hlen), (Generic_max_mult_same _ Hmaj Hlen).
          rewrite (Generic_extreme_center_same _ Hmaj Hlen).
          assert ((!! (round robogram da conf))[extreme_center (!! conf)]
                  + (!! conf)[mini (!! conf)] + (!! conf)[maxi (!! conf)]
                  <= N.nG).
          { rewrite <- (Generic_min_mult_same da),  <- (Generic_max_mult_same da); trivial.
            apply sum3_le_total.
            - now apply Rgt_not_eq, Rlt_gt, Generic_min_mid_lt.
            - now apply Rlt_not_eq, Generic_min_max_lt.
            - now apply Rlt_not_eq, Generic_mid_max_lt. }
          cut ((!! conf)[extreme_center (!! conf)] < (!! (round robogram da conf))[extreme_center (!! conf)]).
          omega.
          rewrite increase_move_iff. exists gmove. split; trivial.
          rewrite round_simplify_Generic in Hmove |- *; trivial.
          destruct (step da gmove); try (now elim Hstep); [].
          destruct (is_extremal (conf gmove) (!! conf)).
          - now elim Hmove.
          - reflexivity. }
Qed.


Section HypRobots.
Variable nG : nat.
Hypothesis size_G : nG >= 2.


Definition g1' : Fin.t nG.
destruct nG eqn:HnG. abstract (omega).
apply (@Fin.F1 n).
Defined.

Definition g2' : Fin.t nG.
destruct nG as [| [| n]] eqn:HnG; try (abstract (omega)).
apply (Fin.FS Fin.F1).
Defined.

End HypRobots.

Require Import Coq.Program.Equality.
Lemma g1'_g2' : forall nG size_nG , @g1' nG size_nG <> @g2' nG size_nG.
Proof.
  intro nG.
  dependent destruction nG; intros.
  - exfalso;omega.
  - dependent destruction nG0.
    + exfalso;omega.
    + simpl.
      intro abs.
      inversion abs.
Qed.

Definition g1 : Names.G := @g1' nG size_G.
Definition g2 : Names.G := @g2' nG size_G.

Lemma g1_g2 : g1 <> g2.
Proof. apply g1'_g2'. Qed.


Instance gathered_at_compat : Proper (eq ==> Pos.eq ==> iff) gathered_at.
Proof.
intros ? pt ? config1 config2 Hconfig. subst. unfold gathered_at.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (config id) config.
Proof.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. destruct id as [? | b]. apply Hgather. apply Fin.case0. exact b.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, config id <> pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => Rdec_bool (config x) pt) Names.names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite Rdec_bool_true_iff in Hall. repeat rewrite Hall; trivial; apply Names.In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, Rdec_bool_false_iff in Hid'. now exists id'.
Qed.

Inductive FirstMove r d config : Prop :=
  | MoveNow : moving r (demon_head d) config <> nil -> FirstMove r d config
  | MoveLater : moving r (demon_head d) config = nil ->
                FirstMove r (demon_tail d) (round r (demon_head d) config) -> FirstMove r d config.

Instance FirstMove_compat : Proper (req ==> deq ==> Pos.eq ==> iff) FirstMove.
Proof.
intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst.
* revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc.
  + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc.
  + apply MoveLater.
    - rewrite <- Hr, <- Hd, <- Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
* revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc.
  + apply MoveNow. now rewrite Hr, Hd, Hc.
  + apply MoveLater.
    - rewrite Hr, Hd, Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
Qed.

Lemma not_forbidden_gathered_Majority_size : forall config id,
  ~forbidden config -> ~gathered_at (config id) config -> no_Majority config ->
  Spect.size (!! config) >= 3.
Proof.
intros config id Hforbidden Hgather Hmaj.
assert (Spect.size (!! config) > 1).
{ unfold no_Majority in Hmaj. eapply lt_le_trans; try eassumption; []. now rewrite Smax_subset. }
rewrite forbidden_equiv in Hforbidden.
destruct (Spect.size (!! config)) as [| [| [| n]]]; omega || tauto.
Qed.

(** Given a non-gathered, non forbidden position, then some robot will move some day *)
Theorem OneMustMove : forall config id, ~ forbidden config -> ~gathered_at (config id) config ->
  exists gmove, forall da, In gmove (active da) -> In gmove (moving robogram da config).
Proof.
intros config id Hforbidden Hgather.
destruct (Spect.support (Smax (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
* elim (support_Smax_non_nil _ Hmaj).
* rewrite <- MajTower_at_equiv in Hmaj.
  apply not_gathered_generalize with _ _ pt in Hgather.
  apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
  exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
  rewrite (round_simplify_Majority _ Hmaj). destruct (step da gmove); auto; now elim Hactive.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config). { unfold no_Majority. rewrite Spect.size_spec, Hmaj'. simpl. omega. }
  clear Hmaj' pt e l.
  destruct (eq_nat_dec (Spect.size (!! config)) 3) as [Hlen| Hlen].
  + apply not_gathered_generalize with _ _ (middle (!! config)) in Hgather.
    apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Three _ Hmaj Hlen). destruct (step da gmove); auto; now elim Hactive.
  + assert (Hle : Spect.size (!! config) >= 4).
    { hnf. apply le_neq_lt.
      - now apply not_forbidden_gathered_Majority_size with id.
      - auto. }
    rewrite Spect.size_spec, Permuted_sort in Hle.
    destruct (sort (Spect.support (!! config))) as [| pt1 [| pt2 [| pt3 [| pt4 l]]]] eqn:Hsup;
    simpl in Hle; omega || clear Hle.
    assert (Hex : exists pt, Spect.In pt (!! config) /\ pt <> extreme_center (!! config)
                             /\ pt <> mini (!! config) /\ pt <> maxi (!! config)).
    { assert (Hmini : mini (!! config) = pt1). { unfold mini. now rewrite Hsup. }
      assert (Hmaxi : In (maxi (!! config)) (pt4 :: l)).
      { unfold maxi. rewrite Hsup. change (In (last (pt4 :: l) 0%R) (pt4 :: l)). apply last_In. discriminate. }
      assert (Hnodup := Spect.support_NoDupA (!! config)).
      rewrite NoDupA_Leibniz, Permuted_sort, Hsup in Hnodup.
      inversion_clear Hnodup. inversion_clear H0. inversion_clear H2.
      destruct (Rdec pt2 (extreme_center (!! config))) as [Heq | Heq]; subst.
      - exists pt3. repeat split; try now intro; subst; intuition.
        rewrite <- Spect.support_In, InA_Leibniz, Permuted_sort, Hsup. intuition.
      - exists pt2. repeat split; try now intro; subst; intuition.
        rewrite <- Spect.support_In, InA_Leibniz, Permuted_sort, Hsup. intuition. }
    destruct Hex as [pt [Hin Hmove]]. rewrite Spect.from_config_In in Hin.
    destruct Hin as [gmove Heq]. rewrite <- Heq in Hmove.
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Generic _ Hmaj Hlen). destruct (step da gmove); auto.
    unfold is_extremal. repeat Rdec_full; intuition.
Qed.

(* Given a k-fair demon, in any non gathered, non forbidden position, a robot will be the first to move. *)
Theorem Fair_FirstMove : forall d, Fair d ->
  forall config id, ~forbidden config -> ~gathered_at (config id) config -> FirstMove robogram d config.
Proof.
intros d Hfair config id Hforbidden Hgathered.
destruct (OneMustMove id Hforbidden Hgathered) as [gmove Hmove].
destruct Hfair as [locallyfair Hfair].
revert config Hforbidden Hgathered Hmove Hfair.
specialize (locallyfair gmove).
induction locallyfair; intros config Hforbidden Hgathered Hmove Hfair.
+ apply MoveNow. intro Habs. rewrite <- active_spec in H. apply Hmove in H. rewrite Habs in H. inversion H.
+ destruct (moving robogram (demon_head d) config) eqn:Hnil.
  - apply MoveLater. exact Hnil.
    rewrite (no_moving_same_conf _ _ _ Hnil).
    apply (IHlocallyfair); trivial.
    now destruct Hfair.
  - apply MoveNow. rewrite Hnil. discriminate.
Qed.


Lemma gathered_at_forever : forall da conf pt, gathered_at pt conf -> gathered_at pt (round robogram da conf).
Proof.
intros da conf pt Hgather. rewrite (round_simplify_Majority).
+ intro g. destruct (step da (Good g)); reflexivity || apply Hgather.
+ intros pt' Hdiff.
  assert (H0 : (!! conf)[pt'] = 0).
  { rewrite Spect.from_config_spec, Spect.Pos.list_spec.
    induction Spect.Names.names as [| id l].
    + reflexivity.
    + unfold R.eq_dec, Rdef.eq_dec in *. simpl. Rdec_full.
      - elim Hdiff. rewrite <- Heq. destruct id as [g | b]. apply Hgather. apply Fin.case0. exact b.
      - apply IHl. }
  rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply Spect.pos_in_config.
Qed.

Lemma gathered_at_dec : forall conf pt, {gathered_at pt conf} + {~gathered_at pt conf}.
Proof.
intros conf pt.
destruct (forallb (fun id => Rdec_bool (conf id) pt) Names.names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. rewrite <- Rdec_bool_true_iff. apply Hall. apply Names.In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  destruct id as [g | b]; try now apply Fin.case0; exact b. intro Habs. specialize (Habs g).
  rewrite negb_true_iff, Rdec_bool_false_iff in Heq. contradiction.
Qed.

Lemma gathered_at_OK : forall d conf pt, gathered_at pt conf -> Gather pt (execute robogram d conf).
Proof.
cofix Hind. intros d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.

Theorem Gathering_in_R :
  forall d, Fair d -> solGathering robogram d.
Proof.
intros d Hfair conf. revert d Hfair. pattern conf.
apply (well_founded_ind wf_lt_conf). clear conf.
intros conf Hind d Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec conf (conf (Good g1))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (conf (Good g1)). apply Now. apply gathered_at_OK. assumption.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  apply (Fair_FirstMove Hfair (Good g1)) in Hmove; trivial.
  induction Hmove as [d conf Hmove | d conf Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    destruct (Hind (round robogram (demon_head d) conf)) with (demon_tail d) as [pt Hpt].
    - apply round_lt_conf; assumption.
    - now destruct Hfair.
    - now apply never_forbidden.
    - exists pt. apply Later. rewrite execute_tail. apply Hpt.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_conf in Heq.
    destruct Hrec as [pt Hpt].
    - setoid_rewrite Heq. apply Hind.
    - now destruct Hfair.
    - rewrite Heq. assumption.
    - exists pt. apply Later. rewrite execute_tail. apply Hpt.
Qed.
Print Assumptions Gathering_in_R.

End GatheringinR.
