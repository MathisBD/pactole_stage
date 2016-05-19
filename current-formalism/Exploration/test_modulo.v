(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.
Require Import Ensembles.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
(* Require Import Pactole.Similarity. *)

Local Open Scope Z_scope. 

Parameter n : Z.
Axiom n_pos : (n > 0)%Z.

Axiom n_sup_1: (1 < n)%Z. (* at first, it was 0 < n, but for the "non_trivial" definition,
there was a probleme: 1 mod n have to be different to 0 mod n, so n ~= 1*)



Definition origin := 0 mod n. 

Definition add (x y : Z) : Z :=  (Zmod (x + y) n).

Definition mul (x y : Z): Z :=  (Zmod (Z.mul x y) n).

Definition eq (x y : Z): Prop := Zmod x n = Zmod y n.

Lemma eq_equiv_lemme : Equivalence eq.
Proof.
split.
 - split.
 - intros x y Hxy. unfold eq in *. symmetry. assumption.
 - intros x y z Hxy Hyz. unfold eq in *. transitivity (y mod n); assumption.
Qed.

Definition eq_equiv := eq_equiv_lemme.

Lemma eq_dec_lem : forall x y, {~eq x y} + {eq x y}.
Proof.
intros. unfold eq. apply Z_noteq_dec.
Qed.


Definition eq_dec : forall x y, {~ eq x y} + {eq x y}:= eq_dec_lem.

Lemma n_not_0: n <> 0.
Proof.
  assert (n>0) by apply n_pos. intuition.
Qed.
  
Lemma mod_pos_z : forall (x:Z), ( 0 <= (Zmod x n) < n ).
Proof.
intros. apply Z_mod_lt. apply n_pos.
Qed. 



Instance add_compat : Proper (eq ==> eq ==> eq) add.
Proof.
 intros x x' Hx y y' Hy.
 unfold add, eq.
 do 2 rewrite Zmod_mod.
 unfold eq in *.
 rewrite Zplus_mod, Hx, Hy, <- Zplus_mod.
 reflexivity.
Qed.

Lemma mul_proper : Proper (eq ==> eq ==> eq) mul.
Proof.
intros x x' Hx y y' Hy. 
unfold mul, eq in *. 
repeat rewrite Zmod_mod.
rewrite Zmult_mod, Hx, Hy, <- Zmult_mod.
reflexivity.
Qed.

Definition opp (x: Z): Z := (n - x) mod n. 

Lemma opp_proper : Proper (eq ==> eq) opp.
Proof.
intros x x' Hx.
unfold opp, eq in *.
repeat rewrite Zmod_mod.
rewrite Zminus_mod, Hx, <- Zminus_mod.
reflexivity.
Qed.

Definition dist (x y : Z) : Z := Z.min (add (opp y) x) (add (opp x) y) .




Module Ddef : DiscreteSpaceDef with Definition t := Z
                                 with Definition eq := eq
                                 with Definition origin := origin
                                 with Definition dist := dist
                                 with Definition add := add
                                 with Definition mul := mul
                                 with Definition opp := opp.

Definition t := Z.

Definition origin := 0 mod n.

Definition add (x y : Z) : Z :=  (Zmod (x + y) n).

Definition mul (x y : Z): Z :=  (Zmod (Z.mul x y) n).

Definition eq (x y : Z): Prop := Zmod x n = Zmod y n.

Lemma eq_equiv_lemme : Equivalence eq.
Proof.
split.
 - split.
 - intros x y Hxy. unfold eq in *. symmetry. assumption.
 - intros x y z Hxy Hyz. unfold eq in *. transitivity (y mod n); assumption.
Qed.

Definition eq_equiv := eq_equiv_lemme.

Lemma eq_dec_lem : forall x y, {eq x y} + {~ eq x y}.
Proof.
intros. apply Sumbool.sumbool_not. unfold eq. apply Z_noteq_dec.
Qed.


Definition eq_dec : forall x y, {eq x y} + {~ eq x y}:= eq_dec_lem.

Lemma n_not_0: n <> 0.
Proof.
  assert (n>0) by apply n_pos. intuition.
Qed.
  
Lemma mod_pos_z : forall (x:Z), ( 0 <= (Zmod x n) < n ).
Proof.
intros. apply Z_mod_lt. apply n_pos.
Qed. 



Instance add_compat : Proper (eq ==> eq ==> eq) add.
Proof.
 intros x x' Hx y y' Hy.
 unfold add, eq.
 do 2 rewrite Zmod_mod.
 unfold eq in *.
 rewrite Zplus_mod, Hx, Hy, <- Zplus_mod.
 reflexivity.
Qed.

Lemma mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
Proof.
intros x x' Hx y y' Hy. 
unfold mul, eq in *. 
repeat rewrite Zmod_mod.
rewrite Zmult_mod, Hx, Hy, <- Zmult_mod.
reflexivity.
Qed.

Definition opp (x: Z): Z := (n - x) mod n. 

Lemma opp_compat : Proper (eq ==> eq) opp.
Proof.
intros x x' Hx.
unfold opp, eq in *.
repeat rewrite Zmod_mod.
rewrite Zminus_mod, Hx, <- Zminus_mod.
reflexivity.
Qed.

Definition dist (x y : Z) : Z := Z.min (add (opp y) x) (add (opp x) y) .

Lemma dist_pos : forall x y, (0 <= dist x y).
Proof.
intros.
unfold dist, Z.min. 
destruct (Z.compare (add (opp y) x) (add (opp x) y) ); 
unfold add;
apply mod_pos_z.
Qed.

Lemma dist_proper: Proper (eq ==> eq ==> eq) dist.
Proof.
intros x x' Hx y y' Hy.
unfold dist, eq in *; unfold add, opp. 
rewrite Zminus_mod, Zplus_mod, (Zminus_mod n x), (Zplus_mod ((n mod n - x mod n) mod n) y).
rewrite Hx, Hy, <- Zminus_mod, <- Zplus_mod, <- Zminus_mod, <- Zplus_mod.
reflexivity.
Qed.


Lemma dist_defined_0 : forall a b, (a - b) mod n = 0 -> a mod n = b mod n.
Proof.
intros.
assert (Hdiv1:let (q1, r1) := Z.div_eucl a n in a = n * q1 + r1 /\ 0 <= r1 < n).
apply Z_div_mod, n_pos.
assert (Hdiv2:let (q2, r2) := Z.div_eucl b n in b = n * q2 + r2 /\ 0 <= r2 < n).
apply Z_div_mod, n_pos.
destruct (Z.div_eucl a n), (Z.div_eucl b n).
destruct Hdiv1 as (Ha, Hr1) , Hdiv2 as (Hb, Hr2).
assert (Hab: (a-b) mod n = (z0 - z2) mod n).
rewrite Ha, Hb, Zminus_mod, Zplus_mod, (Zplus_mod (n*z1) z2).
apply fast_Zmult_comm, (fast_Zmult_comm n z1).
do 2 rewrite Z_mod_mult.
simpl.
do 2 rewrite Zmod_mod.
symmetry; apply Zminus_mod. 
rewrite Hab, Zmod_divides in H.
destruct H.
assert (Hz_lt_n: z0 - z2 < n * 1) by omega.
rewrite H in Hz_lt_n.
assert (axiom: n > 0) by apply n_pos.
assert (Hz_gt_mn: n*(-1)  < z0 - z2 ) by omega.
rewrite H in Hz_gt_mn.
assert (Hgt1:x < 1).
apply (Zmult_lt_reg_r x 1 n). omega.
apply fast_Zmult_comm, (fast_Zmult_comm 1 n).
assumption.
assert (Hltm1:-1 < x).
apply (Zmult_lt_reg_r (-1) x n).
omega.
apply fast_Zmult_comm, (fast_Zmult_comm x n).
assumption.
assert (Heq0: x = 0) by intuition.
rewrite Heq0 in H.
assert (Heqz: z0 = z2) by intuition.
rewrite Ha, Hb, Heqz, Zplus_mod, (Zplus_mod (n*z1) z2).
apply fast_Zmult_comm, (fast_Zmult_comm n z1).
do 2 rewrite Z_mod_mult.
reflexivity.
omega.
Qed. 


Lemma dist_defined_1 : forall a b, a mod n = b mod n -> (a - b) mod n = 0.
Proof.
intros;
rewrite Zminus_mod, H, <- Zminus_mod. 
assert (b-b=0) by omega; rewrite H0.
rewrite Zmod_0_l.
reflexivity.
Qed.

Lemma dist_defined : forall x y, dist x y= 0 <-> eq x y.
Proof.
intros.
unfold eq, dist, opp, add.
do 2 rewrite Zplus_mod_idemp_l.
unfold Z.min.
destruct Z.compare.
+ rewrite Zplus_mod, Zminus_mod, Z_mod_same, Zminus_mod_idemp_r.
  simpl.
  split.
 - rewrite <- Zplus_mod.
   apply fast_Zplus_comm, dist_defined_0.
 - intros Heq.
   rewrite <- Zplus_mod.
   replace (-y+x) with (x - y) by omega.
   apply dist_defined_1.
   assumption. 
 - apply n_pos.
 + rewrite Zplus_mod, Zminus_mod, Z_mod_same, Zminus_mod_idemp_r.
   simpl.
   split.
 - rewrite <- Zplus_mod.
   apply fast_Zplus_comm, dist_defined_0.
 - intros H.
   rewrite <- Zplus_mod.
   replace (-y+x) with (x - y) by omega.
   apply dist_defined_1.
   assumption. 
 - apply n_pos.
 + rewrite Zplus_mod, Zminus_mod, Z_mod_same, Zminus_mod_idemp_r.
   simpl.
   split.
 - rewrite <- Zplus_mod.
   replace (-x+y) with (y - x) by omega.
   intros.
   symmetry.
   apply dist_defined_0.
   assumption.
 - intros H.
   rewrite <- Zplus_mod.
   replace (-x+y) with (y - x) by omega.
   apply dist_defined_1.
   symmetry; assumption.
 - apply n_pos. 
Qed.


Lemma dist_sym : forall x y, dist x y = dist y x.
Proof.
intros. unfold dist. rewrite Z.min_comm. reflexivity.
Qed.


Lemma ordre_mod: forall a b, add a b <= a mod n + b mod n. 
Proof. 
intros.
unfold add.
rewrite Zplus_mod.
apply Zmod_le.
apply Z.gt_lt_iff, n_pos.
assert (0 <= a mod n).
apply Z_mod_lt, n_pos. 
assert (0 <= b mod n).
apply Z_mod_lt, n_pos.
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
  apply Z_mod_lt, n_pos.
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
    apply Z_mod_lt, n_pos.
    omega.
  - rewrite Z.compare_lt_iff in *.
    exfalso.
    assert (0 <= b mod n).
    apply Z_mod_lt, n_pos.
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
  - right. rewrite Z.mod_opp_l_nz. omega. apply n_not_0.
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
      assert (n>0) by apply n_pos.
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
      assert (n>0) by apply n_pos.
      assert (0 <= n/2).
      apply Z.div_pos; omega.
      omega.
 + rewrite Z.compare_lt_iff in *.
   assert ((- (x - y) mod n + (x - y) mod n) = n).
   rewrite Z.mod_opp_l_nz.
   omega.
   assert (n>0) by apply n_pos.
   omega.
   assert ((x - y) mod n <> - (x - y) mod n) by omega.
   destruct ((x - y) mod n ?= 0) eqn : H0.
    - assert (0 < -(x - y) mod n). 
      apply (Z.le_lt_trans 0 ((x - y) mod n) (- (x - y) mod n)).
      apply mod_pos_z.
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
   assert (n>0) by apply n_pos.
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
   apply n_pos.
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
assert (0 <= (z-y) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_zy: 0<(z-y) mod n).
assert ((y-z) mod n <> 0) by omega. 
replace (y-z) with (-(z-y)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (z-y) with (-(y-z)) by omega.
assert (0<=-(y-z) mod n) by apply Z_mod_lt, n_pos.
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
assert ((y-z) mod n < n) by apply Z_mod_lt, n_pos.
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
assert (0 <= (y-z) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_zy: 0<(y-z) mod n).
assert ((z-y) mod n <> 0) by omega. 
replace (z-y) with (-(y-z)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (y-z) with (-(z-y)) by omega.
assert (0<=-(z-y) mod n) by apply Z_mod_lt, n_pos.
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
assert ((z-y) mod n < n) by apply Z_mod_lt, n_pos.
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
assert (0 <= (x-y) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_yx: 0<(x-y) mod n).
assert ((y-x) mod n <> 0) by omega.
replace (y-x) with (-(x-y)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (x-y) with (-(y-x)) by omega.
assert (0<=-(y-x) mod n) by apply Z_mod_lt, n_pos.
omega.
assert (lt_0_xz: 0<(z-x) mod n).
assert (0 <= (x-z) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_zx: 0<(x-z) mod n).
assert ((z-x) mod n <> 0) by omega.
replace (z-x) with (-(x-z)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (x-z) with (-(z-x)) by omega.
assert (0<=-(z-x) mod n) by apply Z_mod_lt, n_pos.
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
assert (0<=(x-y) mod n) by apply Z_mod_lt, n_pos.
assert (0<=(z-y) mod n) by apply Z_mod_lt, n_pos.
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
assert (0 <= (y-x) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_yx: 0<(y-x) mod n).
assert ((x-y) mod n <> 0) by omega.
replace (x-y) with (-(y-x)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (y-x) with (-(x-y)) by omega.
assert (0<=-(x-y) mod n) by apply Z_mod_lt, n_pos.
omega.
assert (lt_0_xz: 0<(x-z) mod n).
assert (0 <= (z-x) mod n) by apply Z_mod_lt, n_pos; omega.
assert (lt_0_zx: 0<(z-x) mod n).
assert ((x-z) mod n <> 0) by omega.
replace (x-z) with (-(z-x)) in H by omega. 
rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
replace (z-x) with (-(x-z)) by omega.
assert (0<=-(x-z) mod n) by apply Z_mod_lt, n_pos.
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
assert (0<=(y-x) mod n) by apply Z_mod_lt, n_pos.
assert (0<=(y-z) mod n) by apply Z_mod_lt, n_pos.
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
apply Z_mod_lt, n_pos.
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
apply Zmod_le.
apply Z.gt_lt, n_pos.
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

Lemma add_assoc: forall x y z, eq (add x (add y z)) (add (add x y) z).
Proof.
intros.
unfold add.
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
replace(x + (y + z)) with ( x + y + z) by omega;
reflexivity.
Qed.


Lemma add_origin: forall x, eq (add x origin) x.
Proof.
intros;
unfold add, origin.
rewrite Zplus_mod_idemp_r, Zplus_0_r_reverse.
unfold eq.
apply Zmod_mod.
Qed.

Lemma add_opp: forall x, eq (add x (opp x)) origin.
Proof.
intros.
unfold add, opp.
rewrite Zplus_mod_idemp_r.
replace (x + (n - x)) with (n) by omega.
unfold origin.
rewrite Zmod_0_l, Z_mod_same_full;
reflexivity.
Qed.

Lemma mul_morph: forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
Proof.
intros.
unfold mul.
rewrite Zmult_mod_idemp_r, Zmult_assoc_reverse.
reflexivity.
Qed.

Lemma mul_distr_add: forall a u v, eq (mul a (add u v))
                                          (add (mul a u) (mul a v)).
Proof.
intros.
unfold add, mul.
rewrite Zmult_mod_idemp_r, <- Zplus_mod,Zred_factor4.
reflexivity.
Qed.

Lemma add_morph: forall a b u, eq (add (mul a u) (mul b u))
                                      (mul (a + b) u).
Proof.
intros.
unfold add, mul.
rewrite <- Zplus_mod,Z.mul_add_distr_r.
reflexivity.
Qed.

Lemma mul_1: forall x, eq (mul 1 x) x.
Proof.
intros.
unfold mul, eq.
rewrite Zmod_mod,Z.mul_1_l.
reflexivity.
Qed.

Definition unit := 1.

Lemma non_trivial_lem : ~eq unit origin.
Proof.
unfold eq, unit, origin;
rewrite Zmod_mod, Zmod_0_l, Zmod_1_l.
omega.
apply n_sup_1.
Qed.

Definition non_trivial: ~eq unit origin := non_trivial_lem.
End Ddef.

Module ring := Configurations.MakeDiscreteSpace(Ddef).

