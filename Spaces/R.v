(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega.
Require Export Rbase Rbasic_fun.
Require Import Sorting.
Require Import List.
Require Import Relations.
Require Import RelationPairs.
Require Import SetoidDec.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.Bijection.
Require Export Pactole.Spaces.EuclideanSpace.
Require Export Pactole.Spaces.Similarity.
Require Import Psatz.
Import Permutation.
Set Implicit Arguments.
Open Scope R_scope.


Typeclasses eauto := (bfs).


(** R as a Euclidean space over itself. *)
Instance R_VS : RealVectorSpace R.
refine {| origin := 0;
          one := 1;
          add := Rplus;
          mul := Rmult;
          opp := Ropp |}.
Proof.
all:try now intros; cbn; field.
apply R1_neq_R0.
Defined.

Instance R_ES : EuclideanSpace R.
refine {| inner_product := Rmult |}.
Proof.
* apply Rmult_comm.
* apply Rmult_plus_distr_r.
* apply Rmult_assoc.
* intro. nra.
* intro u. split; intro Heq.
  + apply Rmult_integral in Heq. now destruct Heq.
  + now rewrite Heq, Rmult_0_l.
Defined.

Lemma norm_R : forall x, norm x = Rabs x.
Proof. intro. simpl. apply sqrt_square. Qed.

Lemma dist_R : forall x y, dist x y = Rabs (x - y).
Proof. intros. cbn -[norm]. now rewrite norm_R. Qed.


(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := repeat
  match goal with
    | |- context[@equiv_dec _ _ R_EqDec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (@equiv_dec _ _ R_EqDec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[@equiv_dec _ _ R_EqDec 1 0] =>
        let Heq := fresh "Heq" in destruct (@equiv_dec _ _ R_EqDec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | |- context[@equiv_dec _ _ R_EqDec 0 1] =>
        let Heq := fresh "Heq" in destruct (@equiv_dec _ _ R_EqDec 0 1) as [Heq | Heq];
        [now symmetry in Heq; elim R1_neq_R0 | clear Heq]
    | H : context[@equiv_dec _ _ R_EqDec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (@equiv_dec _ _ R_EqDec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
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
    | |- context[@equiv_dec _ _ R_EqDec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (@equiv_dec _ _ R_EqDec x y) as [Heq | Hneq]
    | |- context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x == ?y, Hneq : ?y =/= ?x |- _ => symmetry in Heq; contradiction
    | Heq : ?x == ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | Heq : ?x = ?y, Hneq : ?y =/= ?x |- _ => symmetry in Heq; contradiction
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Ltac Rle_dec :=
  match goal with
    | |- context[Rle_lt_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rle_lt_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Global Instance Leibniz_fun_compat : forall f : R -> R, Proper (equiv ==> equiv) f.
Proof. intros f ? ? Heq. now rewrite Heq. Qed.

(** A location is determined by distances to 2 points. *)
Lemma dist_case : forall x y, dist x y = x - y \/ dist x y = y - x.
Proof.
cbn. intros x y. rewrite sqrt_square.
destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. now left.
- apply Rabs_left in Hlt. right. unfold Rminus in Hlt. rewrite Hlt. field.
Qed.

Lemma dist_locate : forall x y k, dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.

Lemma GPS : forall x y z1 z2, x <> y -> dist z1 x = dist z2 x -> dist z1 y = dist z2 y -> z1 = z2.
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
intros x y; unfold Rleb; destruct (Rle_lt_dec x y); split; intro H; trivial.
inversion H. elim (Rlt_not_le _ _ r H).
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
apply (StronglySorted_ind (fun l => forall l', StronglySorted Rleb l' -> Permutation l l' -> l = l')).
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
repeat intro. hnf in *. unfold Basics.flip in *. rewrite Rleb_spec in *. apply Ropp_le_cancel.
replace (- (k * (y - t))) with ((- k) * (y - t)) by ring.
replace (- (k * (x - t))) with ((- k) * (x - t)) by ring.
apply Rmult_le_compat_l; lra.
Qed.


(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(** A similarity in R is described by its ratio and its center. *)

Theorem similarity_in_R_case : forall sim : similarity R,
  (forall x, sim x == sim.(zoom) * (x - center sim)) \/
  (forall x, sim x == - sim.(zoom) * (x - center sim)).
Proof.
intro sim. assert (Hkpos : 0 < sim.(zoom)) by apply zoom_pos.
pose (c := sim ⁻¹ 0).
assert (Hc : sim c == 0). { unfold c. apply compose_inverse_r. }
destruct sim as [f k Hk]. simpl in Hkpos, c, Hc |- *.
destruct (equiv_dec k 0) as [Hk0 | Hk0].
* (* if the ratio is 0, the similarity is a constant function. *)
  left. intro x. cbn in Hk0. subst k. rewrite Rmult_0_l.
  change (f x == 0). rewrite <- dist_defined, <- Hc, Hk, Hc. ring.
* assert (Hc1 : f (c + 1) = k \/ f (c + 1) = - k).
  { specialize (Hk (add c 1) c). rewrite Hc in Hk.
    assert (H1 : dist (c + 1) c = 1).
    { replace 1 with (c+1 - c) at 2 by ring. simpl dist. rewrite R_sqrt.sqrt_square; lra. }
    rewrite H1 in Hk. destruct (dist_case (f (add c 1)) 0) as [Heq | Heq]; unfold origin in *;
    rewrite Heq in Hk; ring_simplify in Hk; cbn in *; lra. }
  destruct Hc1 as [Hc1 | Hc1].
  + left. intro x. apply (GPS (f c) (f (c + 1))).
    - rewrite Hc, Hc1. lra.
    - rewrite (Hk x c), Hc. cbn. rewrite 2 sqrt_square. change (retraction f origin) with c.
      replace (k * (x - c) - 0) with (k * (x - c)) by ring.
      rewrite Ropp_0, Rplus_0_r, Rabs_mult, (Rabs_pos_eq k); trivial. lra.
    - rewrite (Hk x (c+1)), Hc1. cbn. rewrite 2 sqrt_square. change (retraction f origin) with c.
      replace (k * (x - c) + - k) with (k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq k); trivial. lra.
  + right. intro x. apply (GPS (f c) (f (c + 1))).
    - rewrite Hc, Hc1. lra.
    - rewrite (Hk x c), Hc. cbn. rewrite 2 sqrt_square. change (retraction f origin) with c.
      replace (- k * (x - c) - 0) with (- k * (x - c)) by ring.
      rewrite Ropp_0, Rplus_0_r, Rabs_mult, (Rabs_left (- k)); unfold Rminus; lra.
    - rewrite (Hk x (c+1)), Hc1. cbn. rewrite 2 sqrt_square. change (retraction f origin) with c.
      replace (- k * (x - c) + - - k) with (- k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); unfold Rminus; lra.
Qed.

Corollary similarity_in_R : forall sim, exists k, (k = sim.(zoom) \/ k = - sim.(zoom))
  /\ forall x, sim x = k * (x - center sim).
Proof. intro sim. destruct (similarity_in_R_case sim); eauto. Qed.

Corollary inverse_similarity_in_R : forall (sim : similarity R) k, k <> 0 ->
  (forall x, sim x == k * (x - center sim)) -> forall x, (sim ⁻¹) x == x / k + center sim.
Proof.
intros sim k Hk Hdirect x. unfold inverse. simpl. change eq with (@equiv R _).
rewrite <- sim.(Inversion), Hdirect. hnf. now field.
Qed.

Lemma sim_Minjective : forall (sim : similarity R), Preliminary.injective equiv equiv sim.
Proof. apply injective. Qed.

Hint Immediate injective sim_Minjective.

Corollary similarity_monotonic : forall sim : similarity R, monotonic Rleb Rleb sim.
Proof.
intro sim. destruct (similarity_in_R_case sim) as [Hinc | Hdec].
+ left. intros x y Hxy. do 2 rewrite Hinc. apply similarity_increasing; trivial.
  pose (Hratio := zoom_pos sim). lra.
+ right. intros x y Hxy. do 2 rewrite Hdec. apply similarity_decreasing; trivial.
  assert (Hratio := zoom_pos sim). lra.
Qed.

(** To conclude that two similarities are equal, it is enough to show that they are equal on two points. *)
Theorem similarity_eq : forall (sim1 sim2 : similarity R) pt1 pt2,
  pt1 =/= pt2 -> sim1 pt1 == sim2 pt1 -> sim1 pt2 == sim2 pt2 -> sim1 == sim2.
Proof.
intros sim1 sim2 pt1 pt2 Hdiff H1 H2 x.
destruct (similarity_in_R sim1) as [k1 [Hk1 Hsim1]].
destruct (similarity_in_R sim2) as [k2 [Hk2 Hsim2]].
assert (Hzoom : zoom sim1 = zoom sim2).
{ assert (dist pt1 pt2 <> 0). { rewrite dist_defined. apply Hdiff. }
  apply Rmult_eq_reg_r with (dist pt1 pt2); trivial; [].
  now rewrite <- 2 dist_prop, H1, H2. }
assert (Hk : k1 = k2 \/ k1 = - k2).
{ destruct Hk1, Hk2; subst; rewrite Hzoom, ?Ropp_involutive; tauto. }
assert (k2 <> 0). { generalize (zoom_pos sim2). lra. }
rewrite Hsim1, Hsim2 in *.
destruct Hk; subst k1.
+ (* Having same factor, they also have same center *)
  apply Rmult_eq_reg_l in H1; trivial; [].
  simpl. do 2 f_equal. lra.
+ (* The equalities for [pt1] and [pt2] lead to a contradiction *)
  exfalso.
  assert (Hx : forall x, - k2 * (x - center sim1) = k2 * (center sim1 - x)) by (intro; ring).
  rewrite Hx in *. clear Hx.
  apply Rmult_eq_reg_l in H1; trivial; [].
  apply Rmult_eq_reg_l in H2; trivial; [].
  simpl in Hdiff. lra.
Qed.

(* We can build a similarity that maps any pair of distinct points to any other pair. *)
Definition build_similarity (pt1 pt2 pt3 pt4 : R) (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4) : similarity R.
simple refine {| sim_f := {| section := fun x => pt3 + (pt4 - pt3) / (pt2 - pt1) * (x - pt1);
                      retraction := fun x => pt1 + (pt2 - pt1) / (pt4 - pt3) * (x - pt3) |};
                 zoom := dist pt4 pt3 / dist pt2 pt1 |}; autoclass.
Proof.
* abstract (intros; simpl in *; split; intro; subst; field; lra).
* intros x y. cbn -[dist]. repeat rewrite dist_R. unfold Rdiv.
  rewrite <- Rabs_Rinv.
  + repeat rewrite <- Rabs_mult. f_equal. ring.
  + simpl in *. lra.
Defined.

Lemma build_similarity_compat : forall pt1 pt1' pt2 pt2' pt3 pt3' pt4 pt4'
  (H12 : pt1 =/= pt2) (H34 : pt3 =/= pt4) (H12' : pt1' =/= pt2') (H34' : pt3' =/= pt4'),
  pt1 == pt1' -> pt2 == pt2' -> pt3 == pt3' -> pt4 == pt4' ->
  build_similarity H12 H34 == build_similarity H12' H34'.
Proof. intros * Heq1 Heq2 Heq3 Heq4 x. simpl. now rewrite Heq1, Heq2, Heq3, Heq4 in *. Qed.

Lemma build_similarity_swap : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity (symmetry Hdiff12) (symmetry Hdiff34) == build_similarity Hdiff12 Hdiff34.
Proof. repeat intro. simpl in *. field. lra. Qed.

Lemma build_similarity_eq1 : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity Hdiff12 Hdiff34 pt1 == pt3.
Proof. intros. simpl in *. field. lra. Qed.

(* This is wrong without the proper orientation *)
Lemma build_similarity_eq2 : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity Hdiff12 Hdiff34 pt2 == pt4.
Proof. intros. simpl in *. field. lra. Qed.

Lemma build_similarity_inverse : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  (build_similarity Hdiff12 Hdiff34)⁻¹ == build_similarity Hdiff34 Hdiff12.
Proof. repeat intro. simpl in *. field. lra. Qed.
