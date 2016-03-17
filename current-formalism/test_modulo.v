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
+ rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 Focus 2.
 intros H. rewrite H. rewrite <- Zplus_mod. assert ((-y +y) = 0). omega.
rewrite H0. auto. 
 - rewrite <- Zplus_mod. apply fast_Zplus_comm. apply dm0. 
 - apply n_pos.
 + rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 Focus 2.
 intros H. rewrite H. rewrite <- Zplus_mod. assert ((-y +y) = 0). omega.
rewrite H0. auto. 
 - rewrite <- Zplus_mod. apply fast_Zplus_comm. apply dm0. 
 - apply n_pos.
 + rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 Focus 2.
 intros H. symmetry in H. rewrite H. rewrite <- Zplus_mod. assert ((-x +x) = 0). omega.
rewrite H0. auto. 
 - rewrite <- Zplus_mod. apply fast_Zplus_comm. intros; symmetry; revert H. apply dm0. 
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

Lemma s2: forall y,0 - - y =  y. Proof. intros; omega. Qed.

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

Lemma dist_half_n: forall x y, (dist x y) <= n / 2.
Proof.
intros. unfold dist, add_mod, opp_mod, Z.min.  
repeat rewrite Zplus_mod_idemp_l. repeat rewrite s.
rewrite Zminus_mod; rewrite ( Zminus_mod n (x-y) n). rewrite Z_mod_same_full.
repeat rewrite Zminus_mod_idemp_r. 
destruct ((0- (y - x)) mod n ?= (0- (x - y)) mod n) eqn : Heq.
 + rewrite Z.compare_eq_iff in *.  



Lemma tri_le_n: forall x y z, (dist x y) + (dist y z) + (dist z x) <= n.
Proof.
intros. unfold dist, add_mod, opp_mod, Z.min. 
repeat rewrite Zplus_mod_idemp_l. repeat rewrite s.
rewrite (Zminus_mod n (x-z) n) ; rewrite (Zminus_mod n (y-x) n); rewrite (Zminus_mod n (x-y) n);
rewrite (Zminus_mod n (z-y) n); rewrite (Zminus_mod n (y-z) n); rewrite (Zminus_mod n (z-x) n). rewrite Z_mod_same_full.
repeat rewrite Zminus_mod_idemp_r. simpl.
destruct (- (x - z) mod n ?= - (z - x) mod n) eqn:Heq1;
destruct ( - (y - x) mod n ?= - (x - y) mod n) eqn:Heq2;
destruct (- (z - y) mod n ?= - (y - z) mod n) eqn:Heq3.
+ repeat rewrite Z.compare_eq_iff in *. 

Lemma triang_ineq : forall x y z, dist x z <= add_mod (dist x y) (dist y z).
Proof.
intros. unfold add_mod. unfold dist. 
unfold add_mod, opp_mod. 
repeat rewrite Zplus_mod_idemp_l. repeat rewrite s. rewrite Zminus_mod.
rewrite (Zminus_mod n (x-z) n) ; rewrite (Zminus_mod n (y-x) n); rewrite (Zminus_mod n (x-y) n);
rewrite (Zminus_mod n (z-y) n); rewrite (Zminus_mod n (y-z) n) . rewrite Z_mod_same_full.
repeat rewrite Zminus_mod_idemp_r. simpl.  unfold Z.min.
 
destruct (- (z - x) mod n ?= - (x - z) mod n) eqn:Heq1.
* destruct ( - (y - x) mod n ?= - (x - y) mod n) eqn:Heq2.
 - destruct (- (z - y) mod n ?= - (y - z) mod n) eqn:Heq3.
   + rewrite <- Zplus_mod. assert (-(y-x) + - (z - y) = -(z-x)). omega. rewrite H. intuition.
   + rewrite <- Zplus_mod. assert (-(y-x) + - (z - y) = -(z-x)). omega. rewrite H. intuition.
   + rewrite Z.compare_eq_iff in *. assert (- (y - x) mod n = - (x - y) mod n).  trivial.
     assert (- (z - x) mod n = - (x - z) mod n). trivial. rewrite H, H0.
     rewrite <- Zplus_mod. assert (-(x-y)+-(y-z) = -(x-z)). omega. rewrite H1. intuition.
 - destruct (- (z - y) mod n ?= - (y - z) mod n) eqn:Heq3.
   + rewrite <- Zplus_mod. assert (-(y-x) + - (z - y) = -(z-x)). omega. rewrite H. intuition.
   + rewrite <- Zplus_mod. assert (-(y-x) + - (z - y) = -(z-x)). omega. rewrite H. intuition.
   + rewrite Z.compare_eq_iff, Z.compare_lt_iff, Z.compare_gt_iff in *. assert (x mod n = z mod n).
     apply dm0. 
     replace (x-z) with (-(y - x) - (- - (z - y))). rewrite Zminus_mod. apply dm1.
     repeat rewrite Zmod_mod. assert (- - (z - y) mod n < - (x - y) mod n).    
     admit.
  - destruct (- (z - y) mod n ?= - (y - z) mod n) eqn:Heq3.
   + rewrite Z.compare_eq_iff, Z.compare_gt_iff in *. rewrite Heq3. rewrite <- Zplus_mod.
     assert (-(x - y) + - (y - z) = -(x-z)). omega. rewrite H. intuition.
   + rewrite Z.compare_eq_iff, Z.compare_lt_iff, Z.compare_gt_iff in *. rewrite <- Zplus_mod.
     assert (- (x - y) + - (z - y) = - (z - x) + (- (x - y) + - (x - y))) by omega; rewrite H.
     rewrite Zplus_mod. 


  rewrite <- Zplus_mod. assert (-(y-x) + - (z - y) = -(z-x)). omega. rewrite H. intuition.
(*      apply Z.le_trans. *)
  

 apply (trans_mod_z (- (y - x) mod n + - (y - z) mod n)
      (- (y - x) mod n + - (z - y) mod n) (((x - y) mod n + - (z - y) mod n) mod n)).
     intuition.
(* ((x - y) mod n + - (z - y) mod n) mod n <= (- (y - x) mod n + - (y - z) mod n) mod n *)
omega.
 
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