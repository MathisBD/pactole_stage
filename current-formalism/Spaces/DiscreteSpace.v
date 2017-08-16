(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import ZArith.
Require Import Psatz.
(* Require Import Morphisms. *)
Require Import Equalities.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Spaces.Graph.


Class DiscreteSpace (T : Type) `{EqDec T} := {
  origin : T;
  dist : T -> T -> nat;
  
  add : T -> T -> T;
  mul : Z -> T -> T; (* really? Does it always make sense? *)
  opp : T -> T;
  
  add_compat : Proper (equiv ==> equiv ==> equiv) add;
  mul_compat : Proper (Logic.eq ==> equiv ==> equiv) mul;
  opp_compat : Proper (equiv ==> equiv) opp;
  
  add_assoc : forall u v w, add u (add v w) == add (add u v) w;
  add_comm : forall u v, add u v == add v u;
  add_origin : forall u, add u origin == u;
  add_opp : forall u, add u (opp u) == origin;
  mul_distr_add : forall a u v, mul a (add u v) == add (mul a u) (mul a v);
  mul_morph : forall a b u, mul a (mul b u) == mul (a * b) u;
  add_morph : forall a b u, add (mul a u) (mul b u) == mul (a + b) u;
  
  dist_defined : forall x y, dist x y = 0 <-> equiv x y;
  dist_sym : forall x y, dist y x = dist x y;
  triang_ineq : forall x y z, (dist x z <= dist x y + dist y z);
  
  mul_1 : forall u, mul 1 u == u;
  unit : T; (* TODO: is it really a good name? *)
  non_trivial : unit =/= origin }.

Global Existing Instance add_compat.
Global Existing Instance mul_compat.
Global Existing Instance opp_compat.

(** ***  Proofs of derivable properties about MetricSpace  **)

Section DiscreteSpaceResults.
  Context `{DiscreteSpace}.
  
  Instance dist_compat : Proper (equiv ==> equiv ==> Logic.eq) dist.
  Proof.
  intros x x' Hx y y' Hy. apply le_antisym.
  + replace (dist x' y') with (0 + dist x' y' + 0) by omega. symmetry in Hy.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply le_trans. apply triang_ineq.
    apply plus_le_compat_r, triang_ineq.
  + replace (dist x y) with (0 + dist x y + 0) by omega. symmetry in Hx.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply le_trans. apply triang_ineq.
    apply plus_le_compat_r, triang_ineq.
  Qed.
  
  Lemma add_reg_r : forall w u v, add u w == add v w -> u == v.
  Proof.
  intros w u v Heq. setoid_rewrite <- add_origin.
  now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
  Qed.
  
  Lemma add_reg_l : forall w u v, add w u == add w v -> u == v.
  Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.
  
  Lemma opp_origin : opp origin == origin.
  Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.
  
  Lemma opp_reg : forall u v, opp u == opp v -> u == v.
  Proof. intros u v Heq. apply (add_reg_r (opp u)). rewrite add_opp, Heq, add_opp. reflexivity. Qed.
  
  Lemma opp_opp : forall u, opp (opp u) == u.
  Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.
  
  Lemma opp_distr_add : forall u v, opp (add u v) == add (opp u) (opp v).
  Proof.
  intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
  setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
  Qed.
  
  Lemma mul_0 : forall u, mul 0 u == origin.
  Proof.
  intro u. apply (add_reg_l u).
  rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
  ring_simplify (1 + 0)%Z. now rewrite mul_1.
  Qed.
  
  Lemma minus_morph : forall k u, mul (-k) u == opp (mul k u).
  Proof.
  intros k u. apply (add_reg_l (mul k u)).
  rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%Z.
  apply mul_0.
  Qed.
  
  Lemma mul_origin : forall k, mul k origin == origin.
  Proof.
  intro k. apply add_reg_l with (mul k origin).
  rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
  Qed.
  
  Lemma mul_opp : forall a u, mul a (opp u) == opp (mul a u).
  Proof.
  intros a u. apply (add_reg_l (mul a u)). rewrite <- mul_distr_add.
  setoid_rewrite add_opp. now rewrite mul_origin.
  Qed.
End DiscreteSpaceResults.

(* Wrong in Z/nZ for instance
Lemma mul_reg_l `{DiscreteSpace} : forall k u v, k <> 0%Z -> mul k u == mul k v -> u == v.
Proof.
intros k u v Hk Heq. setoid_rewrite <- mul_1.
replace 1%Z with (/k * k)%Z by now field.
setoid_rewrite <- mul_morph. rewrite Heq.
reflexivity.
Qed.

Lemma mul_reg_r `{DiscreteSpace} : forall k k' u, ~u == origin -> mul k u == mul k' u -> k = k'.
Proof.
intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
assert (Heq0 : equiv (mul (k -k') u)  origin).
{ unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
elim Hu. rewrite <- (mul_1 u). rewrite <- (Rinv_l (k - k')).
- rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
- intro Habs. apply Hneq. now apply Rminus_diag_uniq.
Qed.

Lemma mul_integral `{DiscreteSpace} : forall k u, mul k u == origin -> k = 0%R \/ u == origin.
Proof.
intros k u Heq. destruct (Rdec k 0%R).
- now left.
- right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
Qed.
*)

Open Scope Z_scope.

Axiom triang_ineq_admit :
forall n (x y z : finite_node n),
(Z.to_nat
   (Z.min ((to_Z x - to_Z z) mod Z.of_nat n)
      ((to_Z z - to_Z x) mod Z.of_nat n)) <=
 Z.to_nat
   (Z.min ((to_Z x - to_Z y) mod Z.of_nat n)
      ((to_Z y - to_Z x) mod Z.of_nat n)) +
 Z.to_nat
   (Z.min ((to_Z y - to_Z z) mod Z.of_nat n)
      ((to_Z z - to_Z y) mod Z.of_nat n)))%nat.

(* Another possiblity is to only define [eq] and [dist], the operations being inherited from [Z].
   Do not forget [dist] and the compatibility lemmas.  *)
Local Instance Ring (n : nat) (Hn : (n > 1)%nat) : DiscreteSpace (finite_node n).
refine {|
  origin := @of_Z n Hn 0;
  
  add := fun x y => @of_Z n Hn (to_Z x + to_Z y);
  mul := fun k x => @of_Z n Hn (k * to_Z x);
  opp := fun x => @of_Z n Hn (- to_Z x);
  
  dist := fun x y => Z.to_nat (Z.min ((to_Z x - to_Z y) mod Z.of_nat n)
                                     ((to_Z y - to_Z x) mod Z.of_nat n));
  
  unit := @of_Z n Hn 1 |}.
Proof.
* (* add_assoc *)
  intros u v w. rewrite 2 Z2Z. apply Robots.eq_proj1. unfold of_Z. simpl.
  now rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc.
* (* add_comm *)
  intros u v. now rewrite Z.add_comm.
* (* add_origin *)
  intro u. rewrite Z2Z, Z.mod_0_l, Z.add_0_r, V2V; reflexivity || omega.
* (* add_opp *)
  intro u. apply Robots.eq_proj1. simpl.
  destruct (to_Z u =?= 0) as [Hu | Hu].
  + rewrite Hu. simpl. reflexivity.
  + rewrite Z2Z, Zopp_mod, (Z.mod_small (to_Z u));
    try (now split; solve [ apply Zle_0_nat | unfold to_Z; rewrite <- Nat2Z.inj_lt; apply proj2_sig ]); [].
    destruct u as [k Hk]. unfold to_Z in *. simpl in*.
    rewrite (Z.mod_small (_ - _)); try lia; [].
    ring_simplify (Z.of_nat k + (Z.of_nat n - Z.of_nat k)).
    rewrite Z.mod_same; reflexivity || lia.
* (* mul_distr_add *)
  intros k u v. rewrite 3 Z2Z. apply Robots.eq_proj1.
  unfold of_Z, to_Z. destruct u as [u Hu], v as [v Hv]. simpl.
  rewrite <- Z.add_mod, Z.mul_mod_idemp_r, Z.mul_add_distr_l; lia.
* (* mul_morph *)
  intros a b [u Hu]. rewrite Z2Z. apply Robots.eq_proj1. unfold of_Z, to_Z. simpl.
  rewrite Z.mul_mod_idemp_r, Z.mul_assoc; lia.
* (* add_morph *)
  intros a b u. rewrite 2 Z2Z. apply Robots.eq_proj1. unfold of_Z. simpl.
  rewrite <- Z.add_mod, Z.mul_add_distr_r; lia.
* (* dist_defined *)
  intros x y. split; intro Heq.
  + apply Robots.eq_proj1. destruct x as [x Hx], y as [y Hy]. unfold to_Z in *. simpl in *.
    change 0%nat with (Z.to_nat 0) in Heq.
    apply Z2Nat.inj in Heq; [ revert Heq; apply Z.min_case; intro Heq | ..].
    - rewrite Zsub_mod_is_0 in Heq; lia.
    - rewrite Zsub_mod_is_0 in Heq; lia.
    - apply Z.min_glb; apply Z.mod_pos_bound; lia.
    - reflexivity.
  + now rewrite Heq, Z.min_r, Z.sub_diag.
* (* dist_sym *)
  intros u v. now rewrite Z.min_comm.
* (* triang_ineq *)
  apply triang_ineq_admit. (* TODO *)
* (* mul_1 *)
  intro. now rewrite Z.mul_1_l, V2V.
* (* non_trivial *)
  intro Habs. inv Habs. rewrite Z.mod_1_l in *; discriminate || lia.
Defined.


Section RingResults.
Variable n : nat.
Hypothesis Hn : (n > 1)%nat.

Instance RingN : DiscreteSpace (finite_node n) := Ring n Hn.

Lemma dist_upper_bound : forall u v, Z.of_nat (@dist  _ _ _ RingN u v) <= Z.of_nat n / 2.
Proof.
intros u v. simpl.
destruct (Ztrichotomy (to_Z u) (to_Z v)) as [Hcase | [Hcase | Hcase]].
* assert (to_Z v < Z.of_nat n). { unfold to_Z. rewrite <- Nat2Z.inj_lt. apply proj2_sig. }
  assert (0 <= to_Z u). { unfold to_Z. apply Zle_0_nat. }
  rewrite Z2Nat.id.
  + replace (to_Z u - to_Z v) with (- (to_Z v - to_Z u)) by ring.
    rewrite Zopp_mod, (Z.mod_small (_ - _)).
    - rewrite Z.min_comm. apply Zmin_bounds, Z.mod_pos_bound. lia.
    - rewrite Z.mod_small; lia.
    - lia.
  + apply Z.min_glb; apply Z.mod_pos_bound; lia.
* rewrite Hcase, Z.sub_diag, Z.mod_0_l; try lia; [].
  simpl. apply Zdiv.Zdiv_le_lower_bound; lia.
* assert (to_Z u < Z.of_nat n). { unfold to_Z. rewrite <- Nat2Z.inj_lt. apply proj2_sig. }
  assert (0 <= to_Z v). { unfold to_Z. apply Zle_0_nat. }
  rewrite Z2Nat.id.
  + replace (to_Z v - to_Z u) with (- (to_Z u - to_Z v)) by ring.
    rewrite Zopp_mod, (Z.mod_small (Z.of_nat n - _)).
    - apply Zmin_bounds, Z.mod_pos_bound. lia.
    - rewrite Z.mod_small; lia.
    - lia.
  + apply Z.min_glb; apply Z.mod_pos_bound; lia.
Qed.

End RingResults.

(* The rest can serve as a basis for the proof of triang_ineq
Open Scope Z_scope.

Lemma ordre_mod: forall a b, add a b <= a mod n + b mod n. 
Proof.
intros.
unfold add.
rewrite Zplus_mod.
apply Zmod_le.
apply n_pos.
assert (0 <= a mod n).
apply Z_mod_lt, Z.gt_lt_iff, n_pos. 
assert (0 <= b mod n).
apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
Qed.

Lemma Zmod_minus_n: forall x, (n-x) mod n = -x mod n. 
Proof.
intros.
rewrite Zminus_mod, Z_mod_same_full, Zminus_mod_idemp_r.
simpl.
reflexivity.
Qed.

Lemma trans_mod_z:  forall a b c, Z.lt a b -> Z.le c a -> Z.lt c b. Proof. intros. omega. Qed.

Lemma simpl_mod : forall x y z, x-y+z = x-(y-z). Proof. intros; omega. Qed.

Lemma simpl_mod_1 : forall x y z, x+y-z = x+(y-z). Proof. intros; omega. Qed.

Lemma simpl_mod_2: forall x y,(0 - (y - x)) = (x - y). Proof. intros; omega. Qed.

Lemma plus_mod_order: forall a b, 0 <= a < n -> 0 <= b < n -> 0 <= a + b < n
                                -> a mod n <= (a + b) mod n.
Proof.
intros. rewrite Zmod_small, (Zmod_small (a+b) n); omega. Qed.

Lemma add_comm: forall x y, eq (add x y) (add y x).
Proof.
intros. unfold add. apply fast_Zplus_comm. reflexivity.
Qed.

Lemma opp_eq: forall a b, -a mod n = -b mod n  -> a mod n = b mod n.
Proof.
intros.
destruct (a mod n ?= 0) eqn : Heq.
+ rewrite Z.compare_eq_iff in *.
  apply Z_mod_zero_opp_full in Heq.
  rewrite Heq in H.
  symmetry in H.
  apply Z_mod_zero_opp_full in H.
  replace (--b) with b in H by omega.
  apply Z_mod_zero_opp_full in Heq.
  replace (--a) with a in Heq by omega.
  omega.
+ rewrite Z.compare_lt_iff in *.
  exfalso.
  assert (0 <= a mod n).
  apply Z_mod_lt, Z.gt_lt_iff, n_pos.
  apply Zle_not_gt in H0.
  omega.
+ rewrite Z.compare_gt_iff in *.
  assert (a mod n <> 0) by omega.
  apply Z_mod_nz_opp_full, Zplus_minus_eq in H0.
  destruct (b mod n ?= 0) eqn : Heqb.
  - rewrite Z.compare_eq_iff in *.
    exfalso. rewrite H in H0.
    apply Z_mod_zero_opp_full in Heqb.
    rewrite Heqb in H0.
    replace (0-n) with (-n) in H0 by omega.
    apply Z.opp_inj in H0.
    assert (a mod n < n).
    apply Z_mod_lt, Z.gt_lt_iff, n_pos.
    omega.
  - rewrite Z.compare_lt_iff in *.
    exfalso.
    assert (0 <= b mod n).
    apply Z_mod_lt, Z.gt_lt_iff, n_pos.
    omega.
  - rewrite Z.compare_gt_iff in *.
    assert (b mod n <> 0) by omega.
    apply Z_mod_nz_opp_full, Zplus_minus_eq in H1.
    rewrite H, <- H1 in H0.
    omega.
Qed.

Lemma a_b_eq: forall a b, a = b -> a mod n = b mod n.
Proof.
intros. rewrite H. reflexivity.
Qed.

Lemma eq_a_b_mod: forall a b c, - (a - b) mod n = - (a - c) mod n -> b mod n = c mod n.
Proof.
intros.
apply opp_eq in H.
rewrite <- Zminus_mod_idemp_l, <- (Zminus_mod_idemp_l a c n) in H.
apply dist_defined_0.
symmetry in H.
assert (((a mod n - c) - (a mod n - b)) mod n = 0).
apply dist_defined_1; omega.
apply Z_mod_zero_opp_full in H0.
replace (b - c) with (- - (b - c)) by omega.
apply Z_mod_zero_opp_full.
rewrite <- H0. 
assert ((a mod n - c - (a mod n - b) = b - c)) by omega.
rewrite H1.
apply opp_eq.
replace (- - (b - c)) with (b-c) by omega.
reflexivity.
Qed.

Lemma mod_simp_1:
  forall x y, ((n - y) mod n + x) mod n = (x - y) mod n.
Proof.
  intros.
  rewrite Zplus_mod_idemp_l, simpl_mod, Zminus_mod, Z_mod_same_full, Zminus_mod_idemp_r, simpl_mod_2.
  reflexivity.
Qed.

Lemma add_opp_n: forall x, x mod n + (-x) mod n = 0 \/ x mod n + (-x) mod n = n.
Proof.
  intros.
  destruct (eq_dec x 0).
  - left. unfold eq in e. rewrite e, Zmod_0_l in *. simpl.
    apply Z_mod_zero_opp_full. assumption.
  - right. rewrite Z.mod_opp_l_nz. omega. generalize n_pos. omega.
    unfold eq in n0. rewrite Zmod_0_l in n0. assumption.
Qed.


Lemma dist_half_n: forall x y, (dist x y) <= n / 2.
Proof.
intros.
unfold dist, add, opp, Z.min. 
repeat rewrite Zplus_mod_idemp_l, simpl_mod.
rewrite Zminus_mod, (Zminus_mod n (x-y) n), Z_mod_same_full.
repeat rewrite Zminus_mod_idemp_r.
replace (0-(y-x)) with (x-y) by omega.
replace (0-(x-y)) with (- (x-y)) by omega.
destruct ((x - y) mod n ?= - (x - y) mod n) eqn : Heq.
 + rewrite Z.compare_eq_iff in *. 
   apply (Zmult_le_reg_r) with (p := 2).
   omega.
   do 2 rewrite <- Zplus_diag_eq_mult_2.
   rewrite Heq at 1.
   assert ((- (x - y) mod n + (x - y) mod n) = n \/ (- (x - y) mod n + (x - y) mod n) = 0).
   destruct (eq_dec x y).
    - right.
      unfold eq in e. 
      apply dist_defined_1 in e.
      omega.
    - left.
      rewrite Z.mod_opp_l_nz.
      omega.
      assert (n>0) by apply Z.gt_lt_iff, n_pos.
      omega.
      unfold eq in n0.
      assert ((x - y) mod n = 0 -> x mod n = y mod n).
      apply dist_defined_0.
      omega.
    - destruct H; rewrite H.
      assert (n mod 2 = 0).
      rewrite <- H, Heq.
      replace (- (x - y) mod n + - (x - y) mod n) with (2*(-(x-y) mod n)) by omega.
      apply fast_Zmult_comm, Z_mod_mult.
      assert (n = 2*(n/2)).
      apply Z_div_exact_2; omega. 
      omega.
      assert (n>0) by apply Z.gt_lt_iff, n_pos.
      assert (0 <= n/2).
      apply Z.div_pos; omega.
      omega.
 + rewrite Z.compare_lt_iff in *.
   assert ((- (x - y) mod n + (x - y) mod n) = n).
   rewrite Z.mod_opp_l_nz.
   omega.
   assert (n>0) by apply Z.gt_lt_iff, n_pos.
   omega.
   assert ((x - y) mod n <> - (x - y) mod n) by omega.
   destruct ((x - y) mod n ?= 0) eqn : H0.
    - assert (0 < -(x - y) mod n). 
      apply (Z.le_lt_trans 0 ((x - y) mod n) (- (x - y) mod n)).
      apply Z_mod_lt, Z.gt_lt_iff, n_pos.
      assumption.
      assert (- (x - y) mod n <> 0) by omega.
      rewrite Z.compare_eq_iff in *. 
      assert (- (x - y) mod n = 0).
      apply Z_mod_zero_opp_full.
      omega.
      exfalso.
      omega.
    - intros H1.
      assert (- (x - y) mod n = 0).
      apply Z_mod_zero_opp_full in H1.
      assumption.
      rewrite <- H2 in H1.
      apply H.
      omega. 
    - intros H1.
      assert (- (x - y) mod n = 0).
      apply Z_mod_zero_opp_full in H1.
      assumption.
      rewrite <- H2 in H1.
      apply H.
      assumption.
    - assert ((x - y) mod n + (x - y) mod n < n) by omega. 
      rewrite Zplus_diag_eq_mult_2 in H0.
      apply fast_Zmult_comm in H0. 
      apply Z.div_le_lower_bound; omega.
 + rewrite Z.compare_gt_iff in *.
   assert ((- (x - y) mod n + (x - y) mod n) = n).
   rewrite Z.mod_opp_l_nz.
   omega.
   assert (n>0) by apply Z.gt_lt_iff, n_pos.
   omega.
   assert ((x - y) mod n <> - (x - y) mod n) by omega.
   destruct (-(x - y) mod n ?= 0) eqn : H0.
    - rewrite Z.compare_eq_iff in *. 
      assert ((x - y) mod n = 0).
      apply Z_mod_zero_opp_full in H0.
      replace (- - (x - y)) with (x - y) in H0 by omega.
      omega.
      omega.
    - intros H1.
      assert (- (x - y) mod n = 0).
      apply Z_mod_zero_opp_full.
      omega.
      rewrite <- H2 in H1.
      apply H.
      assumption. 
    - intros H1.
      assert (- (x - y) mod n = 0).
      apply Z_mod_zero_opp_full in H1.
      assumption.
      rewrite <- H2 in H1.
      apply H.
      assumption.
    - assert (-(x - y) mod n + - (x - y) mod n < n) by omega. 
      rewrite Zplus_diag_eq_mult_2 in H0.
      apply fast_Zmult_comm in H0. 
      apply Z.div_le_lower_bound; omega.
Qed.

Lemma eq_nz_opp_n: forall a b,- (a - b) mod n <> 0 <->  - (a - b) mod n + - (b - a) mod n = n.
Proof.
split.
 + intros.
   replace (- (a - b)) with (b - a) in * by omega.
   assert ((b - a) mod n = n - - (b - a) mod n).
   rewrite Z_mod_nz_opp_full.
   replace (n - (n - (b - a) mod n)) with ((b - a) mod n) by omega.
   reflexivity.
   assumption.
   rewrite H0.
   omega.
 + intros.
   symmetry in H.
   rewrite Z.add_comm in H.
   apply (Zplus_minus_eq n)in H. 
   replace (-(b - a)) with (a - b) in H by omega.
   intros H0.
   apply Zeq_plus_swap in H.
   rewrite H0 in H.
   apply Z_mod_zero_opp_full in H0. 
   replace (--(a-b)) with (a-b) in H0 by omega.
   rewrite H0 in H; simpl in H.
   assert (n>0).
   apply Z.gt_lt_iff, n_pos.
   omega. 
Qed.

Lemma eq_nz_n: forall a b,(a - b) mod n <> 0 <->  (a - b) mod n + (b - a) mod n = n.
Proof.
intros.
replace (a-b) with (-(b-a)) in * by omega.
replace (b-a) with (-(a-b)) at 3 by omega.
apply eq_nz_opp_n. 
Qed.



Lemma tri_ineq_help_eq_lt_lt: forall x y z,
(x - z) mod n = (z - x) mod n -> 
0 < (x - z) mod n -> 
(x - y) mod n < (y - x) mod n -> 
(z - y) mod n < (y - z) mod n ->  
(x - y) mod n <= n / 2 -> 
(z - y) mod n <= n / 2 ->
(x - z) mod n <= n / 2 -> 
False.
Proof.
intros x y z Heq1 eq0 Heq2 Heq3 Hdxy Hdyz Hdxz.
replace (x - y) with ((x - z) + (z - y)) in Heq2 by omega.
replace (y - x) with ((y - z) + (z - x)) in Heq2 by omega.
rewrite Zplus_mod, (Zplus_mod (y - z)  (z - x) n) in Heq2.
assert (eq_div_2: (x-z) mod n = n/2).
replace (z-x) with (-(x-z)) in Heq1 by omega.
rewrite (Z_mod_nz_opp_full (x-z) n), <- Zeq_plus_swap, Zplus_diag_eq_mult_2 in Heq1.
assert (n_div_2: 2*(n/2) <= n).
apply Z_mult_div_ge.
omega.
rewrite <- Heq1 in n_div_2 at 2.
omega.
omega.
assert (lt_0_yz: 0<(y-z) mod n).
assert (0 <= (z-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_zy: 0<(z-y) mod n).
assert ((y-z) mod n <> 0) by omega. 
replace (y-z) with (-(z-y)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (z-y) with (-(y-z)) by omega.
assert (0<=-(y-z) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (n_div_2: n = 2*(n/2)).
assert ((x-z) mod n + (z-x) mod n = n).
replace (x-z) with (-(z-x)) by omega.
replace (z-x) with (-(x-z)) at 2 by omega.
rewrite <- eq_nz_opp_n.
replace (-(z-x)) with (x-z) by omega;
omega.
omega.
assert (zy_lt_n2: (z-y) mod n < n/2).
assert ((z-y) mod n <> 0) by intuition.
replace (z-y) with (-(y-z)) in H by omega.
rewrite eq_nz_opp_n in H.
apply fast_Zmult_comm in n_div_2.
rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
replace (-(y-z)) with (z-y) in H by omega;
replace (-(z-y)) with (y-z) in H by omega.
omega.
assert (n2_lt_yz: n/2 < (y-z) mod n).
assert ((z-y) mod n <> 0) by intuition.
replace (z-y) with (-(y-z)) in H by omega.
rewrite eq_nz_opp_n in H.
apply fast_Zmult_comm in n_div_2.
rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
replace (-(y-z)) with (z-y) in H by omega;
replace (-(z-y)) with (y-z) in H by omega.
omega.
assert (Hlt1: ((x - z) mod n + (z - y) mod n) < n).
rewrite eq_div_2.
apply fast_Zmult_comm in n_div_2.
rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
rewrite n_div_2 at 3; intuition.
assert (Hgt1: n/2 < (x - z) mod n + (z - y) mod n).
omega.
rewrite Zmod_small in Heq2.
Focus 2.
omega.
assert (Hgt2: n < (y - z) mod n + (z - x) mod n).
rewrite n_div_2 at 1.
apply fast_Zmult_comm.
rewrite <- Zplus_diag_eq_mult_2.
omega.
assert (Hlt2: ((y - z) mod n + (z - x) mod n) < n+n/2).
assert ((y-z) mod n < n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (Heq2': 0 < ((y - z) mod n + (z - x) mod n) - n < n/2) by omega.
assert (Hmod: 0 < ((y - z) mod n + (z - x) mod n - n) mod n < n/2).
rewrite Zmod_small; omega.
assert (Hmod_eq:((y - z) mod n + (z - x) mod n - n) mod n = ((y - z) mod n + (z - x) mod n) mod n).
rewrite <- Zminus_mod_idemp_r, Z_mod_same_full. 
replace ((y - z) mod n + (z - x) mod n - 0) with ((y - z) mod n + (z - x) mod n) by omega.
omega. 
omega.
Qed.

Lemma tri_ineq_help_eq_lt_lt2: forall x y z,
(x - z) mod n = (z - x) mod n -> 
0 < (x - z) mod n -> 
(y - x) mod n < (x - y) mod n ->
(y - z) mod n < (z - y) mod n ->
(y - x) mod n <= n / 2 ->
(y - z) mod n <= n / 2 ->
(x - z) mod n <= n / 2 ->
False.
Proof.
intros x y z Heq1 eq0 Heq2 Heq3 Hdxy Hdyz Hdxz.
replace (x - y) with ((x - z) + (z - y)) in Heq2 by omega. 
replace (y - x) with ((y - z) + (z - x)) in Heq2 by omega.
rewrite Zplus_mod, (Zplus_mod (x - z)  (z - y) n) in Heq2.
assert (eq_div_2: (x-z) mod n = n/2).
replace (z-x) with (-(x-z)) in Heq1 by omega.
rewrite (Z_mod_nz_opp_full (x-z) n), <- Zeq_plus_swap, Zplus_diag_eq_mult_2 in Heq1.
assert (n_div_2: 2*(n/2) <= n).
apply Z_mult_div_ge.
omega.
rewrite <- Heq1 in n_div_2 at 2.
omega.
omega.
assert (lt_0_yz: 0<(z-y) mod n).
assert (0 <= (y-z) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_zy: 0<(y-z) mod n).
assert ((z-y) mod n <> 0) by omega. 
replace (z-y) with (-(y-z)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (y-z) with (-(z-y)) by omega.
assert (0<=-(z-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (n_div_2: n = 2*(n/2)).
assert ((x-z) mod n + (z-x) mod n = n).
replace (x-z) with (-(z-x)) by omega.
replace (z-x) with (-(x-z)) at 2 by omega.
rewrite <- eq_nz_opp_n. 
replace (-(z-x)) with (x-z) by omega;
omega.
omega.
assert (zy_lt_n2: (y-z) mod n < n/2).
assert ((y-z) mod n <> 0) by intuition.
replace (y-z) with (-(z-y)) in H by omega.
rewrite eq_nz_opp_n in H.
apply fast_Zmult_comm in n_div_2.
rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
replace (-(y-z)) with (z-y) in H by omega;
replace (-(z-y)) with (y-z) in H by omega. 
omega.
assert (n2_lt_yz: n/2 < (y-z) mod n).
assert ((y-z) mod n <> 0) by intuition.
replace (y-z) with (-(z-y)) in H by omega.
rewrite eq_nz_opp_n in H.
apply fast_Zmult_comm in n_div_2.
rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
replace (-(y-z)) with (z-y) in H by omega;
replace (-(z-y)) with (y-z) in H by omega.
assert (Hlt1: ((x - z) mod n + (y - z) mod n) < n).
rewrite eq_div_2. 
rewrite n_div_2 at 3; omega.
assert (Hgt1: n/2 < (x - z) mod n + (y - z) mod n).
omega.
rewrite Zmod_small in Heq2.
Focus 2.
omega.  
assert (Hgt2: n < (z - y) mod n + (z - x) mod n).
rewrite n_div_2 at 1.
omega.
assert (Hlt2: ((z - y) mod n + (z - x) mod n) < n+n/2).
assert ((z-y) mod n < n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (Heq2': 0 < ((z - y) mod n + (z - x) mod n) - n < n/2).
omega.
assert (Hmod: 0 < ((z - y) mod n + (z - x) mod n - n) mod n < n/2).
rewrite Zmod_small; omega.
assert (Hmod_eq:((z - y) mod n + (z - x) mod n - n) mod n = ((z - y) mod n + (z - x) mod n) mod n).
rewrite <- Zminus_mod_idemp_r, Z_mod_same_full. 
replace ((z - y) mod n + (z - x) mod n - 0) with ((z - y) mod n + (z - x) mod n) by omega.
omega.
rewrite Heq1, (Z.add_comm ((z - x) mod n) ((z - y) mod n)), <- Hmod_eq in Heq2.
omega.
omega.
Qed.

Lemma tri_ineq_help_lt_lt_lt: forall x y z,  (x - z) mod n < (z - x) mod n ->
0 < (x - z) mod n ->
(x - y) mod n < (y - x) mod n ->
(x - y) mod n <= n / 2 -> 
(z - y) mod n < (y - z) mod n ->
(z - y) mod n <= n / 2 ->
(x - z) mod n <= n / 2 ->
(x - z) mod n = ((x - y) mod n + (z - y) mod n) mod n \/
(x - z) mod n < ((x - y) mod n + (z - y) mod n) mod n.
Proof.
intros x y z Heq1 eq0 Heq2 Hdxy Heq3 hdzy Hdxz.
assert (lt_0_xy: 0<(y-x) mod n).
assert (0 <= (x-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_yx: 0<(x-y) mod n).
assert ((y-x) mod n <> 0) by omega.
replace (y-x) with (-(x-y)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (x-y) with (-(y-x)) by omega.
assert (0<=-(y-x) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (lt_0_xz: 0<(z-x) mod n).
assert (0 <= (x-z) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_zx: 0<(x-z) mod n).
assert ((z-x) mod n <> 0) by omega.
replace (z-x) with (-(x-z)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (x-z) with (-(z-x)) by omega.
assert (0<=-(z-x) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert ((x - y) mod n + (z - y) mod n < n).
destruct (Z.odd n) eqn: Hpar.
rewrite Zodd_mod in Hpar.
apply Zeq_bool_eq in Hpar.
rewrite Z_div_mod_eq with (b := 2);
omega.
rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool, Zmod_eq_full in Hpar.
apply Zminus_eq in Hpar.
rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
assert (xy_lt_n2: (x-y) mod n < n/2).
assert ((x-y) mod n <> 0) by omega.
replace (x-y) with (-(y-x)) in H by omega.
rewrite eq_nz_opp_n in H.
replace (-(y-x)) with (x-y) in H by omega;
replace (-(x-y)) with (y-x) in H by omega.
omega. omega. omega.
assert (0<=(x-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
assert (0<=(z-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
rewrite (Zmod_small ((x - y) mod n + (z - y) mod n) n); try omega.
replace (x-y) with (x-z+(z-y)) by omega.
assert ((x - z) mod n + (z - y) mod n < n).
destruct (Z.odd n) eqn: Hpar.
rewrite Zodd_mod in Hpar.
apply Zeq_bool_eq in Hpar.
rewrite Z_div_mod_eq with (b := 2);
omega.
rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool, Zmod_eq_full in Hpar.
apply Zminus_eq in Hpar.
rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
assert (xz_lt_n2: (x-z) mod n < n/2).
assert ((x-z) mod n <> 0) by intuition.
replace (x-z) with (-(z-x)) in H2 by omega.
rewrite eq_nz_opp_n in H2.
replace (-(z-x)) with (x-z) in H2 by omega;
replace (-(x-z)) with (z-x) in H2 by omega.
omega. omega. omega.
rewrite Zplus_mod, (Zmod_small ((x - z) mod n + (z - y) mod n) n); try omega.
Qed.

Lemma tri_ineq_help_lt_lt_lt2: forall x y z,  (x - z) mod n < (z - x) mod n ->
0 < (x - z) mod n ->
(y - x) mod n < (x - y) mod n ->
(y - x) mod n <= n / 2 -> 
(y - z) mod n < (z - y) mod n ->
(y - z) mod n <= n / 2 ->
(x - z) mod n <= n / 2 ->
(x - z) mod n = ((y - x) mod n + (y - z) mod n) mod n \/
(x - z) mod n < ((y - x) mod n + (y - z) mod n) mod n.
Proof.
intros x y z Heq1 eq0 Heq2 Hdxy Heq3 hdzy Hdxz.
assert (lt_0_xy: 0<(x-y) mod n).
assert (0 <= (y-x) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_yx: 0<(y-x) mod n).
assert ((x-y) mod n <> 0) by omega.
replace (x-y) with (-(y-x)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (y-x) with (-(x-y)) by omega.
assert (0<=-(x-y) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert (lt_0_xz: 0<(x-z) mod n).
assert (0 <= (z-x) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos; omega.
assert (lt_0_zx: 0<(z-x) mod n).
assert ((x-z) mod n <> 0) by omega.
replace (x-z) with (-(z-x)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (z-x) with (-(x-z)) by omega.
assert (0<=-(x-z) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
omega.
assert ((y - x) mod n + (y - z) mod n < n).
destruct (Z.odd n) eqn: Hpar.
rewrite Zodd_mod in Hpar.
apply Zeq_bool_eq in Hpar.
rewrite Z_div_mod_eq with (b := 2);
omega.
rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool, Zmod_eq_full in Hpar.
apply Zminus_eq in Hpar.
rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
assert (xy_lt_n2: (y-x) mod n < n/2).
assert ((y-x) mod n <> 0) by omega.
replace (y-x) with (-(x-y)) in H by omega.
rewrite eq_nz_opp_n in H.
replace (-(x-y)) with (y-x) in H by omega;
replace (-(y-x)) with (x-y) in H by omega.
omega. omega. omega.
assert (0<=(y-x) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
assert (0<=(y-z) mod n) by apply Z_mod_lt, Z.gt_lt_iff, n_pos.
rewrite (Zmod_small ((y - x) mod n + (y - z) mod n) n); try omega.
replace (y-z) with (y-x+(x-z)) by omega.
assert ((y - x) mod n + (x - z) mod n < n).
destruct (Z.odd n) eqn: Hpar.
rewrite Zodd_mod in Hpar.
apply Zeq_bool_eq in Hpar.
rewrite Z_div_mod_eq with (b := 2);
omega.
rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool, Zmod_eq_full in Hpar.
apply Zminus_eq in Hpar.
rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
assert (xz_lt_n2: (x-z) mod n < n/2).
assert ((x-z) mod n <> 0) by omega.
replace (x-z) with (-(z-x)) in H2 by omega.
rewrite eq_nz_opp_n in H2.
replace (-(z-x)) with (x-z) in H2 by omega;
replace (-(x-z)) with (z-x) in H2 by omega.
omega. omega. omega.
rewrite Zplus_mod, (Zmod_small ((y - x) mod n + (x - z) mod n) n); omega.
Qed.



Lemma triang_ineq_t : forall x y z, dist x z <= add (dist x y) (dist y z).
Proof.
intros. 
destruct (dist x z ?= 0) eqn:eq0.
unfold add.
rewrite Z.compare_eq_iff, eq0 in *.
apply Z_mod_lt, Z.gt_lt_iff, n_pos.
rewrite Z.compare_lt_iff in *.
exfalso.
assert (0 <= dist x z).
apply dist_pos.
intuition.
rewrite Z.compare_gt_iff in *.
assert (dist x z <= add (dist x y) (dist y z) 
        <-> (dist x z = add (dist x y) (dist y z))
        \/ (dist x z < add (dist x y) (dist y z))).
omega.
apply H.
clear H.
assert (Hdxy: dist x y <= n/2) by apply dist_half_n.
assert (Hdyz: dist y z <= n/2) by apply dist_half_n.
assert (Hdxz: dist x z <= n/2) by apply dist_half_n.
unfold add, dist, opp, add. 
repeat rewrite Zplus_mod_idemp_l in *.
rewrite <- (Zplus_mod_idemp_r x (n-y) n).
replace (n - x + y) with (n + y - x) by omega.
rewrite <- (Zminus_mod_idemp_r (n+y) x n).
rewrite Zplus_mod_idemp_r, Zminus_mod_idemp_r.
unfold dist, add, opp in *.
repeat rewrite Zplus_mod_idemp_l in *.
repeat rewrite simpl_mod in *.
replace (n+y-x) with (n-(x-y)) in * by omega.
rewrite Zminus_mod, (Zminus_mod n (x-z) n), (Zminus_mod n (y-x) n), (Zminus_mod n (x-y) n) in *;
rewrite (Zminus_mod n (z-y) n), (Zminus_mod n (y-z) n), Z_mod_same_full in *.
repeat rewrite Zminus_mod_idemp_r in *.
repeat rewrite simpl_mod_2 in *.
unfold Z.min in *. 
destruct ( (x - z) mod n ?= (z - x) mod n) eqn:Heq1;
destruct ( (x - y) mod n ?= (y - x) mod n) eqn:Heq2;
destruct ( (y - z) mod n ?= (z - y) mod n) eqn:Heq3;
try rewrite Z.compare_eq_iff in *;
try rewrite Z.compare_lt_iff in *;
try rewrite Z.compare_gt_iff in *. 
  + rewrite <- Zplus_mod; replace (x-y + (y - z)) with (x-z) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y + (y - z)) with (x-z) by omega; omega.
  + rewrite Heq1, Heq2, <- Zplus_mod; replace ((y-x)+(z-y)) with (z-x) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y + (y - z)) with (x-z) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y + (y - z)) with (x-z) by omega; omega.
  
  + exfalso; apply tri_ineq_help_eq_lt_lt with (x :=x) (y:=y) (z:=z); assumption. 
  + rewrite Heq3, <- Zplus_mod; replace (y - x + (z - y)) with (z-x) by omega; omega.
  + exfalso; apply tri_ineq_help_eq_lt_lt2 with (x:=x) (y:=y) (z:=z); assumption.
  + rewrite <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.

  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + rewrite Heq2, <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + apply tri_ineq_help_lt_lt_lt; assumption.

  + rewrite Heq3, <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
  + apply tri_ineq_help_lt_lt_lt2; assumption.
  + rewrite <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.

  + rewrite Heq2, <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + rewrite <- Zplus_mod; replace (x-y+(y-z)) with (x-z) by omega; omega.
  + rewrite Z.add_comm; apply tri_ineq_help_lt_lt_lt with (x:=z) (z:= x); assumption.
  + rewrite Heq3, <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.

  + rewrite Z.add_comm; apply tri_ineq_help_lt_lt_lt2 with (x:=z) (z:=x); assumption.
  + rewrite <- Zplus_mod; replace (y-x+(z-y)) with (z-x) by omega; omega.
Qed.

Lemma add_mod_to_add : forall a b, 0<= a -> 0 <= b -> add a b <= a + b.
Proof.
intros.
unfold add.
apply Zmod_le. apply n_pos.
omega.
Qed.

Lemma triang_ineq : forall x y z, dist x z <= (dist x y) + (dist y z).
Proof.
intros.
transitivity (add (dist x y) (dist y z)).
apply triang_ineq_t.
apply add_mod_to_add;
apply dist_pos.
Qed.
*)
