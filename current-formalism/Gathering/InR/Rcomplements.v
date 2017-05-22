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
Require Import Sorting.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RealMetricSpace.
Require Import Pactole.Similarity.
Require Pactole.CommonRealFormalism.
Require Pactole.RigidFormalism.
(* Require Import Pactole.Gathering.InR.SortingR. *)
Require Import Pactole.Gathering.Definitions.
Require Import Pactole.MultisetSpectrum.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Open Scope R_scope.


(** R as a vector space over itself. *)

Module Rdef : RealMetricSpaceDef with Definition t := R
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
  
  Lemma add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. unfold eq, add, origin. intros. lra. Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. unfold eq, add, opp, origin. intros. lra. Qed.
  
  Lemma mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. unfold eq, mul. intros. lra. Qed.
  
  Lemma mul_distr_add : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  Lemma add_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  (** The multiplicative identity is omitted. *)
  Lemma mul_1 : forall u, eq (mul 1 u) u.
  Proof. unfold eq, mul. intros. lra. Qed.
  
  Definition unit := 1.
  Definition non_trivial : ~eq unit origin := R1_neq_R0.
End Rdef.


Module R := MakeRealMetricSpace(Rdef).

Transparent R.origin Rdef.origin R.eq_dec Rdef.eq_dec R.eq Rdef.eq.

Ltac unfoldR := unfold R.origin, Rdef.origin, R.eq_dec, Rdef.eq_dec, R.eq, Rdef.eq, R.t, Rdef.t,
                       R.add, Rdef.add, R.opp, Rdef.opp, R.mul, Rdef.mul.

Tactic Notation "unfoldR" "in" hyp(H) :=
  unfold R.origin, Rdef.origin, R.eq_dec, Rdef.eq_dec, R.eq, Rdef.eq, R.t, Rdef.t,
         R.add, Rdef.add, R.opp, Rdef.opp, R.mul, Rdef.mul in H.

(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := unfoldR; repeat
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
  unfoldR;
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

Ltac Rle_dec :=
  match goal with
    | |- context[Rle_lt_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rle_lt_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

(** Translation and homothecy similarities are well-defined on R. *)
Lemma translation_hypothesis : forall z x y, R.dist (R.add x z) (R.add y z) = R.dist x y.
Proof. intros z x y. unfoldR. unfold R.dist, Rdef.dist. now ring_simplify (x + z - (y + z))%R. Qed.

Lemma homothecy_hypothesis : forall k x y, R.dist (R.mul k x) (R.mul k y) = (Rabs k * R.dist x y)%R.
Proof. intros. unfoldR. unfold R.dist, Rdef.dist. rewrite <- Rmult_minus_distr_l. apply Rabs_mult. Qed.

Global Instance Leibniz_fun_compat : forall f, Proper (R.eq ==> R.eq) f.
Proof. intros f ? ? Heq. now rewrite Heq. Qed.

(** A location is determined by distances to 2 points. *)
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


(** *  Some result about sorting  *)

Coercion is_true : bool >-> Sortclass.

Definition Rleb (x y : R) := if Rle_lt_dec x y then true else false.

Lemma Rleb_spec : forall x y, Rleb x y = true <-> Rle x y.
Proof.
intros x y; unfold Rleb; destruct (Rle_lt_dec x y); split; intro H; trivial. inversion H. elim (Rlt_not_le _ _ r H).
Qed.

Corollary Rleb_total : forall x y, Rleb x y = true \/ Rleb y x = true.
Proof.
intros x y. unfold Rleb. destruct (Rle_lt_dec x y).
  now left.
  right. destruct (Rle_lt_dec y x). reflexivity. elim (Rlt_irrefl x). now apply Rlt_trans with y.
Qed.

Corollary Rleb_trans : Transitive Rleb.
Proof. intros ? ? ?. unfold is_true. setoid_rewrite Rleb_spec. apply Rle_trans. Qed.

Module Rletot : Orders.TotalLeBool with Definition t := R
                                   with Definition leb := Rleb.
  Definition t := R.
  Definition leb := Rleb.
  Definition leb_total := Rleb_total.
End Rletot.

Module Rsort := Mergesort.Sort(Rletot).
Export Rsort.

Theorem StronglySorted_uniq :
  forall l l', StronglySorted Rleb l -> StronglySorted Rleb l' -> Permutation l l' -> l = l'.
Proof.
intros l l' Hl. revert l Hl l'.
apply (StronglySorted_ind (fun l => forall l' : list R, StronglySorted Rleb l' -> Permutation l l' -> l = l')).
+ intros l' _ Hperm. symmetry. now apply Permutation_nil.
+ intros a l Hl IHl Hle l' Hl' Hperm. destruct l' as [| b l'].
  - apply Permutation_nil. now symmetry.
  - assert (a = b).
    { destruct (Req_dec a b); trivial. apply Rle_antisym.
      - rewrite List.Forall_forall in Hle. rewrite <- Rleb_spec. apply Hle.
        cut (List.In b (a :: l)). now intros [|].
        rewrite Hperm. now left.
      - apply StronglySorted_inv in Hl'. destruct Hl' as [_ Hl'].
        rewrite List.Forall_forall in Hl'. rewrite <- Rleb_spec. apply Hl'.
        cut (List.In a (b :: l')). now intros [Hin | Hin]; try symmetry in Hin.
        rewrite <- Hperm. now left. }
    subst. f_equal. apply IHl. now apply StronglySorted_inv in Hl'.
    now apply Permutation_cons_inv with b.
Qed.

Instance sort_uniq : Proper (@Permutation R ==> eq) sort.
Proof.
intros l l' Hl. apply StronglySorted_uniq.
- apply StronglySorted_sort. exact Rleb_trans.
- apply StronglySorted_sort. exact Rleb_trans.
- transitivity l. symmetry. apply Permuted_sort. transitivity l'. assumption. apply Permuted_sort.
Qed.

Instance sort_uniqA : Proper (PermutationA eq ==> eq) sort.
Proof. intros ? ?. rewrite PermutationA_Leibniz. apply sort_uniq. Qed.

Corollary StronglySorted_sort_identity : forall l, StronglySorted Rleb l -> sort l = l.
Proof.
intros l Hl. apply StronglySorted_uniq.
apply StronglySorted_sort. apply Rleb_trans.
assumption.
symmetry. apply Permuted_sort.
Qed.

Corollary sort_idempotent : forall l, sort (sort l) = sort l.
Proof. intros l. apply StronglySorted_sort_identity. apply StronglySorted_sort. apply Rleb_trans. Qed.

Lemma StronglySorted_alls : forall x n, StronglySorted Rleb (alls x n).
Proof.
intros x n. induction n. constructor.
apply SSorted_cons. assumption.
rewrite List.Forall_forall. intros e Hin. apply alls_In in Hin. subst.
unfold is_true. rewrite Rleb_spec. apply Rle_refl.
Qed.

Lemma sort_alls : forall pt n, sort (alls pt n) = alls pt n.
Proof. intros. apply StronglySorted_sort_identity. apply StronglySorted_alls. Qed.

Theorem sort_min : forall (l : list R) (d x : R), List.In x l ->
  (List.hd d (sort l) <= x)%R.
Proof.
intros l d x Hin.
assert (Hsort := StronglySorted_sort l Rleb_trans).
assert (Hperm := Permuted_sort l).
destruct (sort l).
- symmetry in Hperm. apply Permutation_nil in Hperm. subst. now inversion Hin.
- simpl. rewrite Hperm in Hin. destruct Hin. subst. apply Rle_refl.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort Hmin].
  rewrite List.Forall_forall in Hmin. rewrite <- Rleb_spec. now apply Hmin.
Qed.

Theorem min_sort : forall l d x, List.In x l -> (forall y, In y l -> x <= y) -> x = List.hd d (sort l).
Proof.
intros l d x Hin Hmin. apply Rle_antisym.
+ apply Hmin. setoid_rewrite Permuted_sort at 3. apply hd_In. destruct l as [| r l].
  - inversion Hin.
  - intro Habs. cut (r :: l = nil); try discriminate; [].
    apply Permutation_nil. setoid_rewrite Permuted_sort at 2. rewrite Habs. reflexivity.
+ now apply sort_min.
Qed.

Theorem sort_max : forall (s : list R) (d x : R), List.In x s ->
  (x <= List.last (sort s) d)%R.
Proof.
intros s d x Hin.
assert (Hsort := StronglySorted_sort s Rleb_trans).
assert (Hperm := Permuted_sort s).
rewrite Hperm in Hin. revert Hsort x Hin. clear Hperm. generalize (sort s).
apply (@StronglySorted_ind R _ (fun l => forall x : R, List.In x l -> x <= List.last l d)).
now intros ? [].
intros a l Hsorted HP Hle x Hin. destruct Hin.
- subst. destruct l. simpl. apply Rle_refl.
  apply Rle_trans with r. inversion_clear Hle. now rewrite <- Rleb_spec. apply HP. now left.
- destruct l. inversion H. now apply HP.
Qed.

Theorem max_sort : forall l d x, List.In x l -> (forall y, In y l -> y <= x) -> x = last (sort l) d.
Proof.
intros l d x Hin Hmax. apply Rle_antisym.
+ now apply sort_max.
+ apply Hmax. setoid_rewrite Permuted_sort at 3. apply last_In. destruct l as [| r l].
  - inversion Hin.
  - intro Habs. cut (r :: l = nil); try discriminate; [].
    apply Permutation_nil. setoid_rewrite Permuted_sort at 2. rewrite Habs. reflexivity.
Qed.

Lemma StronglySorted_map_increasing : forall A B (RA : relation A) (RB : relation B) f, Proper (RA ==> RB) f ->
  forall l, StronglySorted RA l -> StronglySorted RB (map f l).
Proof.
intros A B RA RB f Hf l Hl. induction Hl; simpl; constructor.
  assumption.
  induction H; simpl; constructor.
    now apply Hf.
    apply IHForall.
      now inversion_clear Hl.
      now inversion_clear IHHl.
Qed.

Corollary sort_map_increasing : forall f, Proper (Rleb ==> Rleb) f -> forall l, sort (map f l) = map f (sort l).
Proof.
intros f Hf l. rewrite (Permuted_sort l) at 1.
apply StronglySorted_sort_identity, (StronglySorted_map_increasing Hf), (StronglySorted_sort l Rleb_trans).
Qed.

Lemma StronglySorted_map_decreasing : forall A B (RA : relation A) (RB : relation B) f,
  Proper (RA --> RB) f -> Transitive RB ->
  forall l, StronglySorted RA l -> StronglySorted RB (rev (map f l)).
Proof.
intros A B RA RB f Hf HB l Hl. rewrite <- map_rev. induction Hl; simpl.
* now constructor.
* rewrite map_app. apply Sorted_StronglySorted. now apply HB. apply sort_app.
  + now apply StronglySorted_Sorted.
  + now repeat constructor.
  + intros x y Hx Hy. inversion_clear Hy.
    - subst y. rewrite (in_map_iff f _ _) in Hx.
        destruct Hx as [z [Heq Hin]]. subst x. rewrite <- (In_rev _) in Hin. apply Hf. unfold Basics.flip.
        rewrite Forall_forall in H. now apply H.
    - now inversion H0.
Qed.

Corollary sort_map_decreasing : forall f, Proper (Rleb --> Rleb) f ->
  forall l, sort (map f l) = rev (map f (sort l)).
Proof.
intros f Hf l. rewrite (Permuted_sort l) at 1. rewrite (Permutation_rev (map f (sort l))) at 1.
apply StronglySorted_sort_identity, (StronglySorted_map_decreasing Hf), (StronglySorted_sort l Rleb_trans).
apply Rleb_trans.
Qed.

Lemma similarity_increasing : forall k t, 0 <= k -> Proper (Rleb ==> Rleb) (fun x => k * (x - t)).
Proof. repeat intro. hnf in *. rewrite Rleb_spec in *. apply Rmult_le_compat_l; lra. Qed.

Lemma similarity_decreasing : forall k t, k <= 0 -> Proper (Rleb --> Rleb) (fun x => k * (x - t)).
Proof.
repeat intro. hnf in *. unfold flip in *. rewrite Rleb_spec in *. apply Ropp_le_cancel.
replace (- (k * (y - t))) with ((- k) * (y - t)) by ring.
replace (- (k * (x - t))) with ((- k) * (x - t)) by ring.
apply Rmult_le_compat_l; lra.
Qed.

(** **  Framework of the proofs about gathering  **)
(* TODO: Move all references to robots to each file Impossiblity.v and Algorithm.v,
         once we switch to typeclasses and can leave proofs about similarities and R here. *)

Module GatheringinR.

Parameter nG: nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.

(** We instantiate in our setting the generic definitions of the gathering problem. *)
Module Defs := Definitions.GatheringDefs(R)(N).
Export Defs.

Definition translation := Sim.translation translation_hypothesis.
Definition homothecy := Sim.homothecy translation_hypothesis homothecy_hypothesis.


(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(* A similarity in R is described by its ratio and its center. *)
Theorem similarity_in_R_case : forall sim : Sim.t,
  (forall x : R, sim x = sim.(Sim.zoom) * (x - sim.(Sim.center))) \/
  (forall x, sim x = - sim.(Sim.zoom) * (x - sim.(Sim.center))).
Proof.
intro sim. assert (Hkpos : 0 < sim.(Sim.zoom)) by apply Sim.zoom_pos.
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
    - rewrite Hc, Hc1. lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - 0) with (k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq k); trivial. lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - k) with (k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq k); trivial. lra.
  + right. intro x. apply (GPS (f c) (f (c + 1))).
    - rewrite Hc, Hc1. lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - 0) with (- k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - - k) with (- k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
Qed.

Corollary similarity_in_R : forall sim, exists k, (k = sim.(Sim.zoom) \/ k = - sim.(Sim.zoom))
  /\ forall x, sim x = k * (x - sim.(Sim.center)).
Proof. intro sim. destruct (similarity_in_R_case sim); eauto. Qed.

Corollary inverse_similarity_in_R : forall (sim : Sim.t) k, k <> 0 ->
  (forall x, sim x = k * (x - sim.(Sim.center))) -> forall x, (sim ⁻¹) x = x / k + sim.(Sim.center).
Proof. intros sim k Hk Hdirect x. simpl. rewrite <- sim.(Inversion), Hdirect. hnf. now field. Qed.

Lemma sim_Minjective : forall (sim : Sim.t), MMultiset.Preliminary.injective R.eq R.eq sim.
Proof. apply Sim.injective. Qed.

Hint Immediate Sim.injective sim_Minjective.

Corollary similarity_monotonic : forall sim : Sim.t, monotonic Rleb Rleb sim.
Proof.
intro sim. destruct (similarity_in_R_case sim) as [Hinc | Hdec].
+ left. intros x y Hxy. do 2 rewrite Hinc. apply similarity_increasing; trivial.
  pose (Hratio := Sim.zoom_pos sim). lra.
+ right. intros x y Hxy. do 2 rewrite Hdec. apply similarity_decreasing; trivial.
  assert (Hratio := Sim.zoom_pos sim). lra.
Qed.

End GatheringinR.
