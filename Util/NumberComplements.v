(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     P. Courtieu, L. Rieg, X. Urbain                                        
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence       
                                                                          *)
(**************************************************************************)


Require Import SetoidDec.
Require Import Reals.
Require Import Omega Psatz.


(* ******************************** *)
(** *  Results about real numbers  **)
(* ******************************** *)


Set Implicit Arguments.
Open Scope R_scope.

(* Should be in Reals from the the std lib! *)
Global Instance Rle_preorder : PreOrder Rle.
Proof. split.
- intro. apply Rle_refl.
- intro. apply Rle_trans.
Qed.

Global Instance Rle_partialorder : PartialOrder eq Rle.
Proof.
intros x y. unfold Basics.flip. cbn. split; intro Hxy.
- now subst.
- destruct Hxy. now apply Rle_antisym.
Qed.

Lemma Rdec : forall x y : R, {x = y} + {x <> y}.
Proof.
intros x y. destruct (Rle_dec x y). destruct (Rle_dec y x).
  left. now apply Rle_antisym.
  right; intro; subst. contradiction.
  right; intro; subst. pose (Rle_refl y). contradiction.
Qed.

Instance R_EqDec : @EqDec R _ := Rdec.

Lemma Rdiv_le_0_compat : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof. intros a b ? ?. now apply Fourier_util.Rle_mult_inv_pos. Qed.

Lemma Rdiv_le_1 : forall a b, 0 < b -> a <= b -> a / b <= 1.
Proof.
intros a b Hb Ha. rewrite <- (Rinv_r b ltac:(lra)).
apply Rmult_le_compat_r; trivial; [].
now apply Rlt_le, Rinv_0_lt_compat.
Qed.


(* Lemma Rdiv_le_compat : forall a b c, (0 <= a -> a <= b -> 0 < c -> a / c <= b / c)%R.
Proof.
intros a b c ? ? ?. unfold Rdiv. apply Rmult_le_compat; try lra.
rewrite <- Rmult_1_l. apply Fourier_util.Rle_mult_inv_pos; lra.
Qed. *)

Lemma Zup_lt : forall x y, x <= y - 1 -> (up x < up y)%Z.
Proof.
intros x y Hle. apply lt_IZR. apply Rle_lt_trans with (x + 1).
- generalize (proj2 (archimed x)). lra.
- apply Rle_lt_trans with (y - 1 + 1); try lra; [].
  generalize (proj1 (archimed y)). lra.
Qed.

Lemma up_le_0_compat : forall x, 0 <= x -> (0 <= up x)%Z.
Proof. intros x ?. apply le_0_IZR, Rlt_le, Rle_lt_trans with x; trivial; []. now destruct (archimed x). Qed.

(** A boolean equality test. *)
Definition Rdec_bool x y := match Rdec x y with left _ => true | right _ => false end.

Global Instance Rdec_bool_compat : Proper (eq ==> eq ==> eq) Rdec_bool.
Proof. repeat intro. subst. reflexivity. Qed.

Lemma Rdec_bool_true_iff : forall x y, Rdec_bool x y = true <-> x = y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma Rdec_bool_false_iff : forall x y, Rdec_bool x y = false <-> x <> y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma if_Rdec : forall A x y (l r : A), (if Rdec x y then l else r) = if Rdec_bool x y then l else r.
Proof. intros. unfold Rdec_bool. now destruct Rdec. Qed.

Lemma Rdec_bool_plus_l : forall k r r', Rdec_bool (k + r) (k + r') = Rdec_bool r r'.
Proof.
intros k r r'.
destruct (Rdec_bool (k + r) (k + r')) eqn:Heq1, (Rdec_bool r r') eqn:Heq2; trivial;
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *.
- elim Heq2. eapply Rplus_eq_reg_l; eassumption.
- subst. auto.
Qed.

Lemma Rdec_bool_mult_l : forall k r r', (k <> 0)%R -> Rdec_bool (k * r) (k * r') = Rdec_bool r r'.
Proof.
intros k r r' Hk.
destruct (Rdec_bool r r') eqn:Heq1, (Rdec_bool (k * r) (k * r')) eqn:Heq2; trivial;
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *.
- subst. auto.
- elim Heq1. eapply Rmult_eq_reg_l; eassumption.
Qed.

Corollary Rdec_bool_plus_r : forall k r r', Rdec_bool (r + k) (r' + k) = Rdec_bool r r'.
Proof. intros. setoid_rewrite Rplus_comm. apply Rdec_bool_plus_l. Qed.

Corollary Rdec_bool_mult_r : forall k r r', (k <> 0)%R -> Rdec_bool (r * k) (r' * k) = Rdec_bool r r'.
Proof. intros. setoid_rewrite Rmult_comm. now apply Rdec_bool_mult_l. Qed.

(** A boolean inequality test. *)
Definition Rle_bool x y :=
  match Rle_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma Rle_bool_true_iff : forall x y, Rle_bool x y = true <-> Rle x y.
Proof. intros x y. unfold Rle_bool. destruct (Rle_dec x y); intuition discriminate. Qed.

Lemma Rle_bool_false_iff : forall x y, Rle_bool x y = false <-> ~Rle x y.
Proof. intros x y. unfold Rle_bool. destruct (Rle_dec x y); intuition discriminate. Qed.

Lemma Rle_bool_mult_l : forall k x y, (0 < k)%R -> Rle_bool (k * x) (k * y) = Rle_bool x y.
Proof.
intros k x y Hk. destruct (Rle_bool x y) eqn:Hle.
- rewrite Rle_bool_true_iff in *. now apply Rmult_le_compat_l; trivial; apply Rlt_le.
- rewrite Rle_bool_false_iff in *. intro Habs. apply Hle. eapply Rmult_le_reg_l; eassumption.
Qed.

Lemma Rle_bool_plus_l : forall k x y, Rle_bool (k + x) (k + y) = Rle_bool x y.
Proof.
intros k x y. destruct (Rle_bool x y) eqn:Hle.
- rewrite Rle_bool_true_iff in *. now apply Rplus_le_compat_l.
- rewrite Rle_bool_false_iff in *. intro Habs. apply Hle. eapply Rplus_le_reg_l; eassumption.
Qed.

Corollary Rle_bool_plus_r : forall k r r', Rle_bool (r + k) (r' + k) = Rle_bool r r'.
Proof. intros. setoid_rewrite Rplus_comm. apply Rle_bool_plus_l. Qed.

Corollary Rle_bool_mult_r : forall k r r', (0 < k)%R -> Rle_bool (r * k) (r' * k) = Rle_bool r r'.
Proof. intros. setoid_rewrite Rmult_comm. now apply Rle_bool_mult_l. Qed.

Lemma Rle_neq_lt : forall x y : R, x <= y -> x <> y -> x < y.
Proof. intros ? ? Hle ?. now destruct (Rle_lt_or_eq_dec _ _ Hle). Qed.

Unset Implicit Arguments.
Lemma succ_neq : forall x, x <> x+1.
Proof.
intros x Habs. assert (Heq : x = x + 0) by ring. rewrite Heq in Habs at 1. clear Heq.
apply Rplus_eq_reg_l in Habs. symmetry in Habs. revert Habs. exact R1_neq_R0.
Qed.

Lemma sqrt_square : forall x, sqrt (x * x) = Rabs x.
Proof.
intro x. unfold Rabs. destruct (Rcase_abs x).
+ replace (x * x) with ((-x) * (-x)) by lra. apply sqrt_square; lra.
+ apply sqrt_square; lra.
Qed.

(** Some results about [R]. *)
Lemma sqrt_subadditive : forall x y, 0 <= x -> 0 <= y -> sqrt (x + y) <= sqrt x + sqrt y.
Proof.
intros x y Hx Hy. apply R_sqr.Rsqr_incr_0.
- repeat rewrite Rsqr_sqrt, ?R_sqr.Rsqr_plus; try lra.
  assert (0 <= 2 * sqrt x * sqrt y).
  { repeat apply Rmult_le_pos; try lra; now apply sqrt_positivity. }
  lra.
- apply sqrt_positivity. lra.
- apply Rplus_le_le_0_compat; now apply sqrt_positivity.
Qed.

Lemma pos_Rsqr_eq : forall x y, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof. intros. setoid_rewrite <- sqrt_Rsqr; trivial. now f_equal. Qed.

Lemma pos_Rsqr_le : forall x y, 0 <= x -> 0 <= y -> (x² <= y² <-> x <= y).
Proof. intros. split; intro; try now apply R_sqr.Rsqr_incr_0 + apply R_sqr.Rsqr_incr_1. Qed.

Lemma pos_Rsqr_lt : forall x y, 0 <= x -> 0 <= y -> (x² < y² <-> x < y).
Proof. intros. split; intro; try now apply R_sqr.Rsqr_incrst_0 + apply R_sqr.Rsqr_incrst_1. Qed.

Lemma pos_Rsqr_le_impl : forall x y, 0 <= y -> x² <= y² -> x <= y.
Proof.
intros x y Hle Hsqr.
destruct (Rle_dec 0 x).
- now apply R_sqr.Rsqr_incr_0.
- transitivity 0; lra.
Qed.

Lemma Rabs_bounds : forall x y, 0 <= y -> (Rabs x <= y <-> -y <= x <= y).
Proof.
intros x y Hy. split; intro Hle.
+ split.
  - cut (-x <= y); try lra; []. etransitivity; eauto; [].
    rewrite <- Rabs_Ropp. apply Rle_abs.
  - etransitivity; eauto; []. apply Rle_abs.
+ now apply Rabs_le.
Qed.

Close Scope R_scope.


(** *  Results about integers  **)

Lemma nat_compare_Eq_comm : forall n m, Nat.compare n m = Eq <-> Nat.compare m n = Eq.
Proof. intros n m. do 2 rewrite Nat.compare_eq_iff. now split. Qed.

Lemma nat_compare_Lt_Gt : forall n m, Nat.compare n m = Lt <-> Nat.compare m n = Gt.
Proof. intros n m. rewrite <- nat_compare_lt, <- nat_compare_gt. now split. Qed.

Definition nat_ind2 P P0 P1 PSS :=
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | 0 => P0
      | S 0 => P1
      | S (S m) => PSS m (F m)
    end.

Lemma div2_le_compat : Proper (le ==> le) Nat.div2.
Proof.
intro n. induction n using nat_ind2; intros m Heq; auto with arith.
destruct m as [| [| m]]; try now inversion Heq.
simpl. do 2 apply le_S_n in Heq. apply IHn in Heq. omega.
Qed.

Lemma even_div2 : forall n, Nat.Even n -> Nat.div2 n + Nat.div2 n = n.
Proof.
intros n Hn. replace (Nat.div2 n + Nat.div2 n) with (2 * Nat.div2 n) by lia.
rewrite <- Nat.double_twice. symmetry. apply Div2.even_double. now rewrite Even.even_equiv.
Qed.

Lemma le_neq_lt : forall m n : nat, n <= m -> n <> m -> n < m.
Proof. intros n m Hle Hneq. now destruct (le_lt_or_eq _ _ Hle). Qed.

Open Scope Z.

Instance Z_EqDec : @EqDec Z _ := Z.eq_dec.

Lemma Zincr_mod : forall k n, 0 < n ->
  (k + 1) mod n = k mod n + 1 \/ (k + 1) mod n = 0 /\ k mod n = n - 1.
Proof.
intros k n Hn.
destruct (Z.eq_dec (k mod n) (n - 1)) as [Heq | Heq].
+ right. rewrite <- Zdiv.Zplus_mod_idemp_l, Heq.
  ring_simplify (n - 1 + 1). split; trivial; []. apply Z.mod_same. omega.
+ left. rewrite <- Zdiv.Zplus_mod_idemp_l. apply Z.mod_small.
  assert (Hle := Z.mod_pos_bound k n Hn). omega.
Qed.

Lemma Zopp_mod : forall k n, 0 <= k < n -> (-k) mod n = (n - (k mod n)) mod n.
Proof.
intros k n Hn. destruct (Z.eq_dec k 0).
- subst. rewrite 2 Z.mod_0_l, Z.sub_0_r, Z.mod_same; omega.
- rewrite Z.mod_opp_l_nz, Z.mod_small; try rewrite Z.mod_small; omega.
Qed.

Lemma Zadd_small_mod_non_conf : forall k n x, (0 < k < n -> (x + k) mod n <> x mod n)%Z.
Proof.
intros k n x ? Habs. assert (Hn : (0 < n)%Z) by omega.
assert (Hk : (k mod n = 0)%Z).
{ replace k with (x + k - x)%Z by ring.
  rewrite Zdiv.Zminus_mod, Habs, Zminus_diag, Z.mod_0_l; lia. }
rewrite Z.mod_small in Hk; omega.
Qed.

Lemma Zsub_mod_is_0 : forall k k' n, 0 <= k < n -> 0 <= k' < n -> ((k - k') mod n = 0 <-> k = k').
Proof.
intros k k' n Hk Hk'. split; intro Heq.
+ assert (Hbound : - n < k - k' < n) by lia.
  rewrite Zdiv.Zmod_divides in Heq; try lia; [].
  destruct Heq as [c Heq]. destruct (Z.eq_dec c 0) as [? | Hneq]; hnf in *; simpl in *; nia.
+ subst. now rewrite Z.sub_diag.
Qed.

Lemma Zmin_bounds : forall n m, n < m -> Z.min n (m - n) <= m / 2.
Proof. intros. apply Z.min_case_strong; intro; apply Zdiv.Zdiv_le_lower_bound; lia. Qed.

Close Scope Z.
