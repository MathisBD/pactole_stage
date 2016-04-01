(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.
Require Import Ensembles.

Local Open Scope Z_scope. 

Parameter n : Z.
Axiom n_pos : (n > 0)%Z.

Axiom n_sup_1: (1 < n)%Z. (* at first, it was 0 < n, but for the "non_trivial" definition,
there was a probleme: 1 mod n have to be different to 0 mod n, so n ~= 1*)
 (*
(* Parameter N:Z. *)
Module ringDef : DiscretSpaceDef with Definition t :=   ensembles_finis(Finite Z, cardinal Z n).
Definition origin := N%Z.*)

Definition origin := 0 mod n. 

Definition add_mod (x y : Z) : Z :=  (Zmod (x + y) n).

Definition mul_mod (x y : Z): Z :=  (Zmod (Z.mul x y) n).

Definition eq_mod (x y : Z): Prop := Zmod x n = Zmod y n.

Definition eq_equiv := @eq_equivalence Z.

Lemma eq_dec_lem : forall x y, {~eq_mod x y} + {eq_mod x y}.
Proof.
intros. unfold eq_mod. apply Z_noteq_dec.
Qed.

Definition eq_dec : forall x y, {~ eq_mod x y} + {eq_mod x y}:= eq_dec_lem.

Lemma n_not_0: n <> 0.
Proof.
  assert (n>0) by apply n_pos. intuition.
Qed.
  
Lemma mod_pos_z : forall (x:Z), ( 0 <= (Zmod x n) < n ).
Proof.
intros. apply Z_mod_lt. apply n_pos.
Qed. 



Instance add_mod_compact : Proper (eq_mod ==> eq_mod ==> eq_mod) add_mod.
Proof.
   intros x x' Hx y y' Hy. unfold add_mod, eq_mod. do 2 rewrite Zmod_mod. unfold eq_mod in *.
   rewrite Zplus_mod. rewrite Hx, Hy. rewrite <- Zplus_mod. intuition.
Qed.

Lemma mul_mod_proper : Proper (eq_mod ==> eq_mod ==> eq_mod) mul_mod.
Proof.
intros x x' Hx y y' Hy. unfold mul_mod, eq_mod in *. repeat rewrite Zmod_mod.
rewrite Zmult_mod. rewrite Hx, Hy. rewrite <- Zmult_mod. intuition.
Qed.

Definition opp_mod (x: Z): Z := (n - x) mod n. 

Lemma opp_mod_proper : Proper (eq_mod ==> eq_mod) opp_mod.
Proof.
intros x x' Hx. unfold opp_mod, eq_mod in *. repeat rewrite Zmod_mod. rewrite Zminus_mod. 
rewrite Hx; rewrite <- Zminus_mod; intuition.
Qed.

Definition dist (x y : Z) : Z := Z.min (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) .

Lemma dist_pos : forall x y, (0 <= dist x y).
Proof.
intros. unfold dist. unfold Z.min. 
destruct (Z.compare (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) ); 
unfold add_mod; apply mod_pos_z.
Qed.

Lemma dist_proper: Proper (eq_mod ==> eq_mod ==> eq_mod) dist.
Proof.
intros x x' Hx y y' Hy. unfold dist, eq_mod in *; unfold add_mod, opp_mod. 
rewrite Zminus_mod, Zplus_mod, (Zminus_mod n x), (Zplus_mod ((n mod n - x mod n) mod n) y).
rewrite Hx, Hy. 
rewrite <- Zminus_mod, <- Zplus_mod. rewrite <- Zminus_mod, <- Zplus_mod. intuition.
Qed.


Lemma dm0 : forall a b, (a - b) mod n = 0 -> a mod n = b mod n.
Proof.
intros. assert (let (q1, r1) := Z.div_eucl a n in a = n * q1 + r1 /\ 0 <= r1 < n).
apply Z_div_mod. apply n_pos.
assert (let (q2, r2) := Z.div_eucl b n in b = n * q2 + r2 /\ 0 <= r2 < n).
apply Z_div_mod; apply n_pos. destruct (Z.div_eucl a n). destruct (Z.div_eucl b n).
destruct H0 as (Ha, Hr1) , H1 as (Hb, Hr2). assert ((a-b) mod n = (z0 - z2) mod n).
rewrite Ha, Hb, Zminus_mod, Zplus_mod, (Zplus_mod (n*z1) z2). 
assert (n*z = z * n). ring. rewrite H0. apply (fast_Zmult_comm n z1).
do 2 rewrite Z_mod_mult. simpl. do 2 rewrite Zmod_mod. symmetry; apply Zminus_mod. 
rewrite H0 in H. rewrite Zmod_divides in H. destruct H.
assert (z0 - z2 < n * 1). omega. rewrite H in H1.
assert (n > 0). apply n_pos. assert (n*(-1)  < z0 - z2 ). omega.
rewrite H in H3. assert (x < 1). apply (Zmult_lt_reg_r x 1 n). omega.
assert (x*n = n*x). intuition. 
intuition. assert (-1 < x). apply (Zmult_lt_reg_r (-1) x n). intuition. 
assert (x*n=n*x). intuition. intuition. assert (x = 0). intuition. rewrite H6 in H.
assert ( z0 = z2). intuition. rewrite Ha, Hb, H7, Zplus_mod, (Zplus_mod (n*z1) z2).
assert (n*z = z * n). ring. rewrite H8. assert (n * z1 = z1 * n). ring. rewrite H9.
do 2 rewrite Z_mod_mult. intuition. omega.
Qed. 


Lemma dm1 : forall a b, a mod n = b mod n -> (a - b) mod n = 0.
Proof.
intros; rewrite Zminus_mod, H. rewrite <- Zminus_mod. 
assert (b-b=0) by omega; rewrite H0; intuition.
Qed.

Lemma dist_define : forall x y, dist x y= 0 <-> eq_mod x y.
Proof.
intros. unfold eq_mod, dist, opp_mod, add_mod. rewrite Zplus_mod_idemp_l.
 rewrite Zplus_mod_idemp_l. unfold Z.min.
destruct Z.compare.
+  rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 - rewrite <- Zplus_mod. apply fast_Zplus_comm. apply dm0.
 - intros H. rewrite <- Zplus_mod. replace (-y+x) with (x - y) by omega. apply dm1. intuition. 
 - apply n_pos.
 + rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 - rewrite <- Zplus_mod. apply fast_Zplus_comm. apply dm0.
 - intros H. rewrite <- Zplus_mod. replace (-y+x) with (x - y) by omega. apply dm1. intuition. 
 - apply n_pos.
 + rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 - rewrite <- Zplus_mod. replace (-x+y) with (y - x) by omega. intros. symmetry. apply dm0. auto.
 - intros H. rewrite <- Zplus_mod. replace (-x+y) with (y - x) by omega. apply dm1. intuition. 
 - apply n_pos. 
Qed.


Lemma dist_sym : forall x y, dist x y = dist y x.
Proof.
intros. unfold dist. rewrite Z.min_comm. intuition.
Qed.


Lemma ordre_mod: forall a b, add_mod a b <= a mod n + b mod n. 
Proof. 
intros. unfold add_mod. rewrite Zplus_mod. apply Zmod_le. apply Z.gt_lt_iff, n_pos.
assert (0 <= a mod n). apply Z_mod_lt. apply n_pos. 
assert (0 <= b mod n). apply Z_mod_lt. apply n_pos. omega.    
Qed.

Lemma Zmod_minus_n: forall x, (n-x) mod n = -x mod n. 
Proof. intros. rewrite Zminus_mod. rewrite Z_mod_same_full.
rewrite Zminus_mod_idemp_r. simpl. intuition.
Qed.

Lemma trans_mod_z:  forall a b c, Z.lt a b -> Z.le c a -> Z.lt c b. Proof. intros. omega. Qed.

Lemma s : forall x y z, x-y+z = x-(y-z). Proof. intros; omega. Qed.

Lemma s1 : forall x y z, x+y-z = x+(y-z). Proof. intros; omega. Qed.

Lemma s2: forall x y,(0 - (y - x)) = (x - y). Proof. intros; omega. Qed.

(* à retenir: 
Z.min (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) < add_mod (dist x y) (dist y z) -> 
Z.max (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) = add_mod (dist x y) (dist y z)   *)

(* intros. unfold dist. replace (x - z)%R with (x - y + (y - z))%R by lra. apply Rabs_triang.*)

Lemma plus_mod_order: forall a b, 0 <= a < n -> 0 <= b < n -> 0 <= a + b < n
                                -> a mod n <= (a + b) mod n.
Proof. intros. rewrite Zmod_small. rewrite (Zmod_small (a+b) n); intuition. intuition. Qed.

Lemma add_comm: forall x y, eq_mod (add_mod x y) (add_mod y x).
Proof.
intros. unfold add_mod. apply fast_Zplus_comm. intuition.
Qed.

Lemma opp_mod_eq: forall a b, -a mod n = -b mod n  -> a mod n = b mod n.
Proof.
intros. destruct (a mod n ?= 0) eqn : Heq.
+ rewrite Z.compare_eq_iff in *. apply Z_mod_zero_opp_full in Heq. rewrite Heq in H.
symmetry in H. apply Z_mod_zero_opp_full in H. replace (--b) with b in H by omega.
apply Z_mod_zero_opp_full in Heq. replace (--a) with a in Heq by omega.
intuition.
+ rewrite Z.compare_lt_iff in *. exfalso. assert (0 <= a mod n). apply Z_mod_lt, n_pos.
  apply Zle_not_gt in H0. intuition.
+ rewrite Z.compare_gt_iff in *.
  assert (a mod n <> 0) by intuition. apply Z_mod_nz_opp_full in H0. apply Zplus_minus_eq in H0.
 destruct (b mod n ?= 0) eqn : Heqb.
  - rewrite Z.compare_eq_iff in *. exfalso. rewrite H in H0. apply Z_mod_zero_opp_full in Heqb.
    rewrite Heqb in H0. replace (0-n) with (-n) in H0 by omega. apply Z.opp_inj in H0.
    assert (a mod n < n). apply Z_mod_lt.
    apply n_pos. assert (a mod n <> n). intuition. auto.
  - rewrite Z.compare_lt_iff in *. exfalso. assert (0 <= b mod n). apply Z_mod_lt, n_pos.
    apply Zle_not_gt in H1. intuition.
  - rewrite Z.compare_gt_iff in *.
    assert (b mod n <> 0) by intuition. apply Z_mod_nz_opp_full in H1. apply Zplus_minus_eq in H1.
    rewrite H in H0. rewrite <- H1 in H0. intuition.
Qed.

Lemma a_b_eq_mod: forall a b, a = b -> a mod n = b mod n.
Proof.
intros. rewrite H; intuition.
Qed.

 (* - (z - x) mod n <= (- (y - x) mod n + - (y - z) mod n) mod n*)
Lemma eq_a_b_mod: forall a b c, - (a - b) mod n = - (a - c) mod n -> b mod n = c mod n.
Proof.
intros. apply opp_mod_eq in H. rewrite <- Zminus_mod_idemp_l in H.
rewrite <- (Zminus_mod_idemp_l a c n) in H. apply dm0. symmetry in H.
assert (((a mod n - c) - (a mod n - b)) mod n = 0). apply dm1; intuition.
apply Z_mod_zero_opp_full in H0. replace (b - c) with (- - (b - c)) by omega.
apply Z_mod_zero_opp_full. rewrite <- H0. 
assert ((a mod n - c - (a mod n - b) = b - c)) by omega. rewrite H1. apply opp_mod_eq.
replace (- - (b - c)) with (b-c) by omega. intuition.
Qed.

Lemma mod_simp_1:
  forall x y, ((n - y) mod n + x) mod n = (x - y) mod n.
Proof.
  intros.
  rewrite Zplus_mod_idemp_l, s, Zminus_mod, Z_mod_same_full, Zminus_mod_idemp_r, s2.
  reflexivity.
Qed.

Lemma add_opp_mod_n: forall x, x mod n + (-x) mod n = 0 \/ x mod n + (-x) mod n = n.
Proof.
  intros.
  destruct (eq_dec x 0).
  - right. rewrite Z.mod_opp_l_nz. intuition. apply n_not_0.
    unfold eq_mod in n0. rewrite Zmod_0_l in n0. assumption.
  - left. unfold eq_mod in e. rewrite e, Zmod_0_l in *. simpl.
    apply Z_mod_zero_opp_full. assumption.
Qed.


Lemma dist_half_n: forall x y, (dist x y) <= n / 2.
Proof.
  intros. unfold dist, add_mod, opp_mod, Z.min.
  (*
  repeat rewrite mod_simp_1.
  destruct ((x - y) mod n ?= (y - x) mod n) eqn : Heq.
  + rewrite Z.compare_eq_iff in *. 
   apply (Zmult_le_reg_r) with (p := 2). omega. do 2 rewrite <- Zplus_diag_eq_mult_2.
   rewrite Heq at 1. 

   assert (((y - x) mod n + (x - y) mod n) = n 
                            \/ ((y - x) mod n + (x - y) mod n) = 0).
   destruct (eq_dec x y).
    - left. rewrite Z.mod_opp_l_nz. intuition.
   assert (n>0) by apply n_pos. intuition. unfold eq_mod in n0. intuition.
   assert ((x - y) mod n = 0 -> x mod n = y mod n). apply dm0. intuition.
    - right. unfold eq_mod in e. assert (x mod n = y mod n -> (x - y) mod n = 0). apply dm1.
   apply H in e. intuition.
    - destruct H; rewrite H.
   assert (n mod 2 = 0). rewrite <- H. rewrite Heq. replace (- (x - y) mod n + - (x - y) mod n)
   with (2*(-(x-y) mod n)) by omega. apply fast_Zmult_comm. apply Z_mod_mult.
   assert (n = 2*(n/2)). apply Z_div_exact_2; intuition. intuition.
   assert (n>0) by apply n_pos. assert (0 <= n/2). apply Z.div_pos; intuition. intuition.
*)
repeat rewrite Zplus_mod_idemp_l. repeat rewrite s.
rewrite Zminus_mod; rewrite ( Zminus_mod n (x-y) n). rewrite Z_mod_same_full.
repeat rewrite Zminus_mod_idemp_r. replace (0-(y-x)) with (x-y) by omega.
replace (0-(x-y)) with (- (x-y)) by omega.
destruct ((x - y) mod n ?= - (x - y) mod n) eqn : Heq.
 + rewrite Z.compare_eq_iff in *. 
   apply (Zmult_le_reg_r) with (p := 2). intuition. do 2 rewrite <- Zplus_diag_eq_mult_2.
   rewrite Heq at 1. assert ((- (x - y) mod n + (x - y) mod n) = n 
                            \/ (- (x - y) mod n + (x - y) mod n) = 0).
   destruct (eq_dec x y).
    - left. rewrite Z.mod_opp_l_nz. intuition.
   assert (n>0) by apply n_pos. intuition. unfold eq_mod in n0. intuition.
   assert ((x - y) mod n = 0 -> x mod n = y mod n). apply dm0. intuition.
    - right. unfold eq_mod in e. assert (x mod n = y mod n -> (x - y) mod n = 0). apply dm1.
   apply H in e. intuition.
    - destruct H; rewrite H.
   assert (n mod 2 = 0). rewrite <- H. rewrite Heq. replace (- (x - y) mod n + - (x - y) mod n)
   with (2*(-(x-y) mod n)) by omega. apply fast_Zmult_comm. apply Z_mod_mult.
   assert (n = 2*(n/2)). apply Z_div_exact_2; intuition. intuition.
   assert (n>0) by apply n_pos. assert (0 <= n/2). apply Z.div_pos; intuition. intuition.
 + rewrite Z.compare_lt_iff in *. intuition.
   assert ((- (x - y) mod n + (x - y) mod n) = n).
   rewrite Z.mod_opp_l_nz. intuition.
   assert (n>0) by apply n_pos. intuition. assert ((x - y) mod n <> - (x - y) mod n).
   intuition. destruct ((x - y) mod n ?= 0) eqn : H0.
    - assert (0 < -(x - y) mod n). 
   apply (Z.le_lt_trans 0 ((x - y) mod n) (- (x - y) mod n)). apply mod_pos_z. intuition.
   assert (- (x - y) mod n <> 0) by intuition. rewrite Z.compare_eq_iff in *. 
   assert (- (x - y) mod n = 0). apply Z_mod_zero_opp_full. intuition. exfalso. rewrite H3 in H2.
   auto.
    - intuition. assert (- (x - y) mod n = 0). apply Z_mod_zero_opp_full in H1. intuition.
   rewrite <- H2 in H1. apply H. intuition. 
    - intuition. assert (- (x - y) mod n = 0). apply Z_mod_zero_opp_full in H1. intuition.
   rewrite <- H2 in H1. apply H. intuition.
    - assert ((x - y) mod n + (x - y) mod n < n) by omega. 
   rewrite Zplus_diag_eq_mult_2 in H0. apply fast_Zmult_comm in H0. 
   apply Z.div_le_lower_bound; intuition.
 + rewrite Z.compare_gt_iff in *.
    assert ((- (x - y) mod n + (x - y) mod n) = n).
   rewrite Z.mod_opp_l_nz. intuition.
   assert (n>0) by apply n_pos. intuition. assert ((x - y) mod n <> - (x - y) mod n).
   intuition. destruct (-(x - y) mod n ?= 0) eqn : H0.
    - rewrite Z.compare_eq_iff in *. 
   assert ((x - y) mod n = 0). apply Z_mod_zero_opp_full in H0.
   assert (- - (x - y) = (x - y)) by omega. rewrite H1 in H0. intuition. intuition.
    - intuition. assert (- (x - y) mod n = 0). apply Z_mod_zero_opp_full. intuition.
   rewrite <- H2 in H1. apply H. intuition. 
    - intuition. assert (- (x - y) mod n = 0). apply Z_mod_zero_opp_full in H1. intuition.
   rewrite <- H2 in H1. apply H. intuition.
    - assert (-(x - y) mod n + - (x - y) mod n < n) by omega. 
   rewrite Zplus_diag_eq_mult_2 in H0. apply fast_Zmult_comm in H0. 
   apply Z.div_le_lower_bound; intuition.
Qed.

Lemma eq_nz_opp_n: forall a b,- (a - b) mod n <> 0 <->  - (a - b) mod n + - (b - a) mod n = n.
Proof.
split. intros. assert (- (a - b) = b - a ) by omega. rewrite H0 in *.
assert ((b - a) mod n = n - - (b - a) mod n). rewrite Z_mod_nz_opp_full.
replace (n - (n - (b - a) mod n)) with ((b - a) mod n) by omega. reflexivity. intuition.
rewrite H1. intuition.
intros. symmetry in H. rewrite Z.add_comm in H. apply (Zplus_minus_eq n)in H. 
replace (-(b - a)) with (a - b) in H by omega.
intuition. apply Zeq_plus_swap in H. rewrite H0 in H. apply Z_mod_zero_opp_full in H0. 
replace (--(a-b)) with (a-b) in H0 by omega. rewrite H0 in H; simpl in H. assert (n>0).
apply n_pos. intuition. 
Qed.

Lemma eq_nz_n: forall a b,(a - b) mod n <> 0 <->  (a - b) mod n + (b - a) mod n = n.
Proof.
intros. replace (a-b) with (-(b-a)) in * by omega. replace (b-a) with (-(a-b)) at 3 by omega.
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
    rewrite Zplus_mod in Heq2. rewrite (Zplus_mod (y - z)  (z - x) n) in Heq2.
    assert (eq_div_2: (x-z) mod n = n/2). replace (z-x) with (-(x-z)) in Heq1 by omega.
    rewrite (Z_mod_nz_opp_full (x-z) n) in Heq1. rewrite <- Zeq_plus_swap in Heq1.
    rewrite Zplus_diag_eq_mult_2 in Heq1. assert (n_div_2: 2*(n/2) <= n). apply Z_mult_div_ge.
    omega. rewrite <- Heq1 in n_div_2 at 2. intuition. intuition.
    assert (lt_0_yz: 0<(y-z) mod n). assert (0 <= (z-y) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_zy: 0<(z-y) mod n). assert ((y-z) mod n <> 0) by intuition. 
    replace (y-z) with (-(z-y)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (z-y) with (-(y-z)) by omega. assert (0<=-(y-z) mod n) by apply Z_mod_lt, n_pos.
    intuition.  assert (n_div_2: n = 2*(n/2)). assert ((x-z) mod n + (z-x) mod n = n).
    replace (x-z) with (-(z-x)) by omega.
    replace (z-x) with (-(x-z)) at 2 by omega. rewrite <- eq_nz_opp_n. 
    replace (-(z-x)) with (x-z) by omega;
    intuition. intuition.
    assert (zy_lt_n2: (z-y) mod n < n/2). assert ((z-y) mod n <> 0) by intuition.
    replace (z-y) with (-(y-z)) in H by omega. rewrite eq_nz_opp_n in H.
    apply fast_Zmult_comm in n_div_2. rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
    replace (-(y-z)) with (z-y) in H by omega;
    replace (-(z-y)) with (y-z) in H by omega. intuition.
    assert (n2_lt_yz: n/2 < (y-z) mod n). assert ((z-y) mod n <> 0) by intuition.
    replace (z-y) with (-(y-z)) in H by omega. rewrite eq_nz_opp_n in H.
    apply fast_Zmult_comm in n_div_2. rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
    replace (-(y-z)) with (z-y) in H by omega;
    replace (-(z-y)) with (y-z) in H by omega. intuition.
    assert (Hlt1: ((x - z) mod n + (z - y) mod n) < n). rewrite eq_div_2. 
    apply fast_Zmult_comm in n_div_2. rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
    rewrite n_div_2 at 3; intuition. assert (Hgt1: n/2 < (x - z) mod n + (z - y) mod n).
    intuition. rewrite Zmod_small in Heq2. Focus 2. intuition.  
    assert (Hgt2: n < (y - z) mod n + (z - x) mod n). rewrite n_div_2 at 1.
    apply fast_Zmult_comm. rewrite <- Zplus_diag_eq_mult_2. intuition.
    assert (Hlt2: ((y - z) mod n + (z - x) mod n) < n+n/2).
    assert ((y-z) mod n < n) by apply Z_mod_lt, n_pos. intuition.
    assert (Heq2': 0 < ((y - z) mod n + (z - x) mod n) - n < n/2). intuition.
    assert (Hmod: 0 < ((y - z) mod n + (z - x) mod n - n) mod n < n/2).
    rewrite Zmod_small; intuition.
    assert (Hmod_eq: ((y - z) mod n + (z - x) mod n - n) mod n 
                     = ((y - z) mod n + (z - x) mod n) mod n).
    rewrite <- Zminus_mod_idemp_r, Z_mod_same_full. 
    replace ((y - z) mod n + (z - x) mod n - 0) with ((y - z) mod n + (z - x) mod n) by omega.
    intuition.
    rewrite <- Hmod_eq in Heq2. 
    assert (Hfalse: n/2 < n/2). transitivity ((x - z) mod n + (z - y) mod n). intuition.
    transitivity (((y - z) mod n + (z - x) mod n - n) mod n); intuition. intuition.
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
    rewrite Zplus_mod in Heq2. rewrite (Zplus_mod (x - z)  (z - y) n) in Heq2.
    assert (eq_div_2: (x-z) mod n = n/2). replace (z-x) with (-(x-z)) in Heq1 by omega.
    rewrite (Z_mod_nz_opp_full (x-z) n) in Heq1. rewrite <- Zeq_plus_swap in Heq1.
    rewrite Zplus_diag_eq_mult_2 in Heq1. assert (n_div_2: 2*(n/2) <= n). apply Z_mult_div_ge.
    omega. rewrite <- Heq1 in n_div_2 at 2. intuition. intuition.
    assert (lt_0_yz: 0<(z-y) mod n). assert (0 <= (y-z) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_zy: 0<(y-z) mod n). assert ((z-y) mod n <> 0) by intuition. 
    replace (z-y) with (-(y-z)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (y-z) with (-(z-y)) by omega. assert (0<=-(z-y) mod n) by apply Z_mod_lt, n_pos.
    intuition.  assert (n_div_2: n = 2*(n/2)). assert ((x-z) mod n + (z-x) mod n = n).
    replace (x-z) with (-(z-x)) by omega.
    replace (z-x) with (-(x-z)) at 2 by omega. rewrite <- eq_nz_opp_n. 
    replace (-(z-x)) with (x-z) by omega;
    intuition. intuition.
    assert (zy_lt_n2: (y-z) mod n < n/2). assert ((y-z) mod n <> 0) by intuition.
    replace (y-z) with (-(z-y)) in H by omega. rewrite eq_nz_opp_n in H.
    apply fast_Zmult_comm in n_div_2. rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
    replace (-(y-z)) with (z-y) in H by omega;
    replace (-(z-y)) with (y-z) in H by omega. intuition.
    assert (n2_lt_yz: n/2 < (y-z) mod n). assert ((y-z) mod n <> 0) by intuition.
    replace (y-z) with (-(z-y)) in H by omega. rewrite eq_nz_opp_n in H.
    apply fast_Zmult_comm in n_div_2. rewrite <- Zplus_diag_eq_mult_2 in n_div_2.
    replace (-(y-z)) with (z-y) in H by omega;
    replace (-(z-y)) with (y-z) in H by omega. intuition.
    assert (Hlt1: ((x - z) mod n + (y - z) mod n) < n). rewrite eq_div_2. 
    rewrite n_div_2 at 3; intuition. assert (Hgt1: n/2 < (x - z) mod n + (y - z) mod n).
    intuition. rewrite Zmod_small in Heq2. Focus 2. intuition.  
    assert (Hgt2: n < (z - y) mod n + (z - x) mod n). rewrite n_div_2 at 1. intuition.
    assert (Hlt2: ((z - y) mod n + (z - x) mod n) < n+n/2).
    assert ((z-y) mod n < n) by apply Z_mod_lt, n_pos. intuition.
    assert (Heq2': 0 < ((z - y) mod n + (z - x) mod n) - n < n/2). intuition.
    assert (Hmod: 0 < ((z - y) mod n + (z - x) mod n - n) mod n < n/2).
    rewrite Zmod_small; intuition.
    assert (Hmod_eq: ((z - y) mod n + (z - x) mod n - n) mod n 
                     = ((z - y) mod n + (z - x) mod n) mod n).
    rewrite <- Zminus_mod_idemp_r, Z_mod_same_full. 
    replace ((z - y) mod n + (z - x) mod n - 0) with ((z - y) mod n + (z - x) mod n) by omega.
    intuition. rewrite Heq1 in Heq2. rewrite (Z.add_comm ((z - x) mod n) ((z - y) mod n))in Heq2.
    rewrite <- Hmod_eq in Heq2. 
    assert (Hfalse: n/2 < n/2). transitivity ((x - z) mod n + (y - z) mod n). intuition.
    transitivity (((z - y) mod n + (z - x) mod n - n) mod n); intuition. intuition. intuition.
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
assert (lt_0_xy: 0<(y-x) mod n). assert (0 <= (x-y) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_yx: 0<(x-y) mod n). assert ((y-x) mod n <> 0) by intuition.
    replace (y-x) with (-(x-y)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (x-y) with (-(y-x)) by omega. assert (0<=-(y-x) mod n) by apply Z_mod_lt, n_pos.
    intuition.
    assert (lt_0_xz: 0<(z-x) mod n). assert (0 <= (x-z) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_zx: 0<(x-z) mod n). assert ((z-x) mod n <> 0) by intuition.
    replace (z-x) with (-(x-z)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (x-z) with (-(z-x)) by omega. assert (0<=-(z-x) mod n) by apply Z_mod_lt, n_pos.
    intuition.
    assert ((x - y) mod n + (z - y) mod n < n). destruct (Z.odd n) eqn: Hpar.
    rewrite Zodd_mod in Hpar. apply Zeq_bool_eq in Hpar. rewrite Z_div_mod_eq with (b := 2);
    intuition. rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool in Hpar.
    rewrite Zmod_eq_full in Hpar. apply Zminus_eq in Hpar.
    rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
    assert (xy_lt_n2: (x-y) mod n < n/2). assert ((x-y) mod n <> 0) by intuition.
    replace (x-y) with (-(y-x)) in H by omega. rewrite eq_nz_opp_n in H.
    replace (-(y-x)) with (x-y) in H by omega;
    replace (-(x-y)) with (y-x) in H by omega. intuition. intuition. intuition.
    assert (0<=(x-y) mod n) by apply Z_mod_lt, n_pos.
    assert (0<=(z-y) mod n) by apply Z_mod_lt, n_pos.
    rewrite (Zmod_small ((x - y) mod n + (z - y) mod n) n); intuition.
    replace (x-y) with (x-z+(z-y)) by omega.
    assert ((x - z) mod n + (z - y) mod n < n).
    destruct (Z.odd n) eqn: Hpar.
    rewrite Zodd_mod in Hpar. apply Zeq_bool_eq in Hpar. rewrite Z_div_mod_eq with (b := 2);
    intuition. rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool in Hpar.
    rewrite Zmod_eq_full in Hpar. apply Zminus_eq in Hpar.
    rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
    assert (xz_lt_n2: (x-z) mod n < n/2). assert ((x-z) mod n <> 0) by intuition.
    replace (x-z) with (-(z-x)) in H2 by omega. rewrite eq_nz_opp_n in H2.
    replace (-(z-x)) with (x-z) in H2 by omega;
    replace (-(x-z)) with (z-x) in H2 by omega. intuition. intuition. intuition.
    rewrite Zplus_mod, (Zmod_small ((x - z) mod n + (z - y) mod n) n); intuition.
    destruct ((z-y) mod n ?= 0) eqn : eH; try rewrite Z.compare_eq_iff in *;
    try rewrite Z.compare_lt_iff in *; try rewrite Z.compare_gt_iff in *.
    rewrite eH; intuition. intuition. intuition.
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
assert (lt_0_xy: 0<(x-y) mod n). assert (0 <= (y-x) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_yx: 0<(y-x) mod n). assert ((x-y) mod n <> 0) by intuition.
    replace (x-y) with (-(y-x)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (y-x) with (-(x-y)) by omega. assert (0<=-(x-y) mod n) by apply Z_mod_lt, n_pos.
    intuition.
    assert (lt_0_xz: 0<(x-z) mod n). assert (0 <= (z-x) mod n) by apply Z_mod_lt, n_pos; intuition.
    assert (lt_0_zx: 0<(z-x) mod n). assert ((x-z) mod n <> 0) by intuition.
    replace (x-z) with (-(z-x)) in H by omega. 
    rewrite eq_nz_opp_n, Z.add_comm,<- eq_nz_opp_n in H.
    replace (z-x) with (-(x-z)) by omega. assert (0<=-(x-z) mod n) by apply Z_mod_lt, n_pos.
    intuition.
    assert ((y - x) mod n + (y - z) mod n < n). destruct (Z.odd n) eqn: Hpar.
    rewrite Zodd_mod in Hpar. apply Zeq_bool_eq in Hpar. rewrite Z_div_mod_eq with (b := 2);
    intuition. rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool in Hpar.
    rewrite Zmod_eq_full in Hpar. apply Zminus_eq in Hpar.
    rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
    assert (xy_lt_n2: (y-x) mod n < n/2). assert ((y-x) mod n <> 0) by intuition.
    replace (y-x) with (-(x-y)) in H by omega. rewrite eq_nz_opp_n in H.
    replace (-(x-y)) with (y-x) in H by omega;
    replace (-(y-x)) with (x-y) in H by omega. intuition. intuition. intuition.
    assert (0<=(y-x) mod n) by apply Z_mod_lt, n_pos.
    assert (0<=(y-z) mod n) by apply Z_mod_lt, n_pos.
    rewrite (Zmod_small ((y - x) mod n + (y - z) mod n) n); intuition.
    replace (y-z) with (y-x+(x-z)) by omega.
    assert ((y - x) mod n + (x - z) mod n < n).
    destruct (Z.odd n) eqn: Hpar.
    rewrite Zodd_mod in Hpar. apply Zeq_bool_eq in Hpar. rewrite Z_div_mod_eq with (b := 2);
    intuition. rewrite Zodd_even_bool, Bool.negb_false_iff, Zeven_mod, <- Zeq_is_eq_bool in Hpar.
    rewrite Zmod_eq_full in Hpar. apply Zminus_eq in Hpar.
    rewrite <- Zplus_diag_eq_mult_2 in Hpar. 
    assert (xz_lt_n2: (x-z) mod n < n/2). assert ((x-z) mod n <> 0) by intuition.
    replace (x-z) with (-(z-x)) in H2 by omega. rewrite eq_nz_opp_n in H2.
    replace (-(z-x)) with (x-z) in H2 by omega;
    replace (-(x-z)) with (z-x) in H2 by omega. intuition. intuition. intuition.
    rewrite Zplus_mod, (Zmod_small ((y - x) mod n + (x - z) mod n) n); intuition.
Qed.



Lemma triang_ineq : forall x y z, dist x z <= add_mod (dist x y) (dist y z).
Proof.
intros. 
destruct (dist x z ?= 0) eqn:eq0. unfold add_mod. rewrite Z.compare_eq_iff, eq0 in *.
apply Z_mod_lt, n_pos. rewrite Z.compare_lt_iff in *. exfalso. assert (0 <= dist x z).
apply dist_pos. intuition. rewrite Z.compare_gt_iff in *.
assert (dist x z <= add_mod (dist x y) (dist y z) 
        <-> (dist x z = add_mod (dist x y) (dist y z))
        \/ (dist x z < add_mod (dist x y) (dist y z))). omega.
apply H.
clear H.
assert (Hdxy: dist x y <= n/2) by apply dist_half_n.
assert (Hdyz: dist y z <= n/2) by apply dist_half_n.
assert (Hdxz: dist x z <= n/2) by apply dist_half_n.
unfold add_mod, dist, opp_mod, add_mod. 
repeat rewrite Zplus_mod_idemp_l in *. rewrite <- (Zplus_mod_idemp_r x (n-y) n).
replace (n - x + y) with (n + y - x) by omega. rewrite <- (Zminus_mod_idemp_r (n+y) x n).
rewrite Zplus_mod_idemp_r, Zminus_mod_idemp_r. unfold dist, add_mod, opp_mod in *.
repeat rewrite Zplus_mod_idemp_l in *.
repeat rewrite s in *. replace (n+y-x) with (n-(x-y)) in * by omega. rewrite Zminus_mod in *.
try rewrite (Zminus_mod n (x-z) n) in *; try rewrite (Zminus_mod n (y-x) n) in *;
try rewrite (Zminus_mod n (x-y) n) in *; try rewrite (Zminus_mod n (z-y) n) in *;
try rewrite (Zminus_mod n (y-z) n) in *. rewrite Z_mod_same_full in *.
repeat rewrite Zminus_mod_idemp_r in *. repeat rewrite s2 in *. unfold Z.min in *. 
destruct ( (x - z) mod n ?= (z - x) mod n) eqn:Heq1;
destruct ( (x - y) mod n ?= (y - x) mod n) eqn:Heq2;
destruct ( (y - z) mod n ?= (z - y) mod n) eqn:Heq3;
try rewrite Z.compare_eq_iff in *; try rewrite Z.compare_lt_iff in *;
try rewrite Z.compare_gt_iff in *. 
  + rewrite <- Zplus_mod. assert (eq: x-y + (y - z) = (x-z)). omega. rewrite eq. intuition.
  + rewrite <- Zplus_mod. assert (eq: x-y + (y - z) = (x-z)). omega. rewrite eq. intuition.
  + assert (eq:(x - y) mod n = (y - x) mod n).  trivial. rewrite Heq1, Heq2.
    rewrite <- Zplus_mod. assert (eq2: (y-x)+(z-y) = (z-x)). omega. rewrite eq2. intuition.
  + rewrite <- Zplus_mod. assert (eq: (x-y) + (y - z) = (x-z)). omega. rewrite eq. intuition.
  + rewrite <- Zplus_mod. assert (eq: (x-y) + (y - z) = (x-z)). omega. rewrite eq. intuition.
  
  + exfalso. apply tri_ineq_help_eq_lt_lt with (x :=x) (y:=y) (z:=z); intuition. 
  + rewrite Heq3. rewrite <- Zplus_mod.
     assert (eq: (y - x + (z - y)) = z-x). omega. rewrite eq. intuition.
  + exfalso; apply tri_ineq_help_eq_lt_lt2 with (x:=x) (y:=y) (z:=z); intuition.
  + rewrite <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega. intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega. intuition.

  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega. intuition.
  + rewrite Heq2, <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega. intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega; intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega. intuition.
  + apply tri_ineq_help_lt_lt_lt; intuition.

  + rewrite Heq3, <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega; intuition.
  + apply tri_ineq_help_lt_lt_lt2; intuition.
  + rewrite <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega; intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega. intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega. intuition.

  + rewrite Heq2, <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega; intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega; intuition.
  + rewrite <- Zplus_mod. replace (x-y+(y-z)) with (x-z) by omega; intuition.
  + rewrite Z.add_comm. apply tri_ineq_help_lt_lt_lt with (x:=z) (z:= x); intuition.
  + rewrite Heq3, <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega; intuition.

  + rewrite Z.add_comm. apply tri_ineq_help_lt_lt_lt2 with (x:=z) (z:=x); intuition.
  + rewrite <- Zplus_mod. replace (y-x+(z-y)) with (z-x) by omega; intuition.
Qed.


Lemma add_assoc: forall x y z, eq_mod (add_mod (add_mod x y) z) (add_mod x (add_mod y z)).  
Proof.
intros. unfold add_mod. rewrite Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
assert ((x + (y + z)) = ( x + y + z)). intuition. rewrite H; intuition.
Qed.


Lemma add_origin: forall x, eq_mod (add_mod x origin) x.
Proof.
intros; unfold add_mod. unfold origin. rewrite Zplus_mod_idemp_r. assert (x + 0 = x).
apply Zplus_0_r. rewrite H. unfold eq_mod. apply Zmod_mod.
Qed.

Lemma add_opp: forall x, eq_mod (add_mod x (opp_mod x)) origin.
Proof.
intros. unfold add_mod, opp_mod. rewrite Zplus_mod_idemp_r. assert ((x + (n - x)) = (x + n - x)).
omega. rewrite H; assert (x + n - x = n). omega. rewrite H0; unfold origin. rewrite Zmod_0_l. 
rewrite Z_mod_same_full; intuition.
Qed.

Lemma mul_morph: forall a b u, eq_mod (mul_mod a (mul_mod b u)) (mul_mod (mul_mod a b) u).
Proof.
intros. unfold mul_mod. rewrite Zmult_mod_idemp_r. rewrite Zmult_mod_idemp_l.
assert ((a * (b * u)) = (a * b * u)). intuition. rewrite H. intuition.
Qed.

Lemma mul_distr_add: forall a u v, eq_mod (mul_mod a (add_mod u v))
                                          (add_mod (mul_mod a u) (mul_mod a v)).
Proof.
intros. unfold add_mod, mul_mod. rewrite Zmult_mod_idemp_r. rewrite <- Zplus_mod.
assert ((a * (u + v)) = (a * u + a * v)). ring. rewrite H. intuition.
Qed.

Lemma add_morph: forall a b u, eq_mod (add_mod (mul_mod a u) (mul_mod b u))
                                      (mul_mod (add_mod a b) u).
Proof.
intros. unfold add_mod, mul_mod. rewrite Zmult_mod_idemp_l. rewrite <- Zplus_mod. 
assert (((a + b) * u) = (u * a + u * b)). ring.
assert ((a * u + b * u) = ( u * a + u * b)). ring. rewrite H. rewrite H0. intuition.
Qed.

Lemma mul_1: forall x, eq_mod (mul_mod 1 x) x.
Proof.
intros. unfold mul_mod. unfold eq_mod. rewrite Zmod_mod. assert (1 * x = x). omega.
rewrite H; intuition.
Qed.

Definition unit := 1.

Lemma non_trivial_lem : ~eq_mod unit origin.
Proof.
unfold eq_mod. unfold unit, origin; rewrite Zmod_mod.
rewrite Zmod_0_l, Zmod_1_l. omega. apply n_sup_1.
Qed.

Definition non_trivial: ~eq_mod unit origin := non_trivial_lem.


Module Ddef : DiscretSpaceDef with Definition t := Z
                                 with Definition eq := eq_mod
                                 with Definition eq_dec := eq_dec
                                 with Definition origin := origin
                                 with Definition dist := dist
                                 with Definition add := add_mod
                                 with Definition mul := mul_mod
                                 with Definition opp := opp_mod.
End Ddef.