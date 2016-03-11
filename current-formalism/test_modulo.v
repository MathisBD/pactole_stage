(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.
Require Import Ensembles.

Local Open Scope Z_scope. 

Parameter n : Z.
Axiom n_pos : (n > 0)%Z.
 (*
(* Parameter N:Z. *)
Module ringDef : DiscretSpaceDef with Definition t :=   ensembles_finis(Finite Z, cardinal Z n).
Definition origin := N%Z.*)

Definition origin := 0 mod n. 

Definition add_mod (x y : Z) : Z :=  (Zmod (x + y) n).

Definition mul_mod (x y : Z): Z :=  (Zmod (Z.mul x y) n).

Lemma sss : forall x y, x >= y -> x > y \/ x = y.
Proof.
intros x y. omega.
Qed.

Lemma mod_pos_z : forall (x:Z), ( 0 <= (Zmod x n) < n ).
Proof.
intros. apply Z_mod_lt. apply n_pos.
Qed. 



Instance add_mod_compact : Proper (eq ==> eq ==> eq) add_mod.
Proof.
   intros x x' Hx y y' Hy. unfold add_mod. apply Z.mod_wd. 
   rewrite Hx, Hy; intuition. intuition.
Qed.

Lemma mul_mod_proper : Proper (eq ==> eq ==> eq) mul_mod.
Proof.
intros x x' Hx y y' Hy. unfold mul_mod. apply Z.mod_wd. rewrite Hx, Hy.
intuition. intuition.
Qed.

Definition opp_mod (x: Z): Z := (n - x) mod n. 

Lemma opp_mod_proper : Proper (eq ==> eq) opp_mod.
Proof.
intros x x' Hx. unfold opp_mod. apply Z.mod_wd. rewrite Hx. intuition. intuition.
Qed.

Definition dist (x y : Z) : Z := Z.min (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) .

Lemma dist_pos : forall x y, (0 <= dist x y).
Proof.
intros. unfold dist. unfold Z.min. 
destruct (Z.compare (add_mod (opp_mod y) x) (add_mod (opp_mod x) y) ); 
unfold add_mod; apply mod_pos_z.
Qed.

Definition eq_mod ( x y : Z): Prop := Zmod x n = Zmod y n.


(*Assume n divides a-b and prove a mod n = b mod n.

We know we can write a = q1 n + r1 and b = q2 n + r2, with remainders r1 and r2 both 
between 0 and n.

Then a-b = (q1 - q2) n + (r1 - r2).

Because n goes evenly into (q1 - q2) n, the remainder when a-b is divided by n
is the same as the remainder when r1 - r2 is divided by n.

Since a-b is divisible by n, the remainder when r1 - r2 is divided by n must be 0. 
So r1 - r2 is a multiple of n.

But r1 and r2 are both numbers between 0 and n, so the only way r1 - r2 can be an even 
multiple of n is for it to equal 0 n = 0.

So r1 = r2 and a mod n = b mod n.*)

Lemma dm0 : forall a b, (a - b) mod n = 0 -> a mod n = b mod n.
intros. assert (a =  rewrite Zplus_mod in H. rewrite Zmod_eq in H. rewrite <- H. 
rewrite <- Zmod_eq, <- Zplus_mod in H. apply Zminus_eq.
assert (a mod n + b mod n - (a mod n + b mod n - (a mod n + b mod n) / n * n) = 
        a mod n + b mod n - a mod n - b mod n + (a mod n + b mod n) / n * n). omega.
rewrite H0.
assert (a mod n + b mod n - a mod n - b mod n + (a mod n + b mod n) / n * n = (a mod n + b mod n) / n * n).
omega. rewrite H1. rewrite Z_div_mod_eq. rewrite Zdiv_mod.
auto.

(* j'admets tout pour tester directement le module dans configuration, TODO à finir les preuves.*)
Lemma dist_define : forall x y, dist x y= 0 <-> eq_mod x y.
Proof.
intros. unfold eq_mod, dist, opp_mod, add_mod. rewrite Zplus_mod_idemp_l.
 rewrite Zplus_mod_idemp_l. (* rewrite Zmod_eq.  rewrite Zmod_eq.*) unfold Z.min.
destruct Z.compare.
+ rewrite Zplus_mod. rewrite Zminus_mod. 
rewrite Z_mod_same. rewrite Zminus_mod_idemp_r. simpl.
split.
 Focus 2.
 intros H. rewrite H. rewrite <- Zplus_mod. assert ((-y +y) = 0). omega.
rewrite H0. auto. 
 - rewrite <- Zplus_mod. intros. apply (Zminus_eq (x mod n) (y mod n)).
   assert ().
   
Admitted.


Lemma dist_sym : forall x y, dist x y = dist y x.
Proof.
intros. unfold dist. rewrite Min.min_comm. intuition.
Qed.

Lemma add_assoc: forall x y z, add_mod (add_mod x y) z = add_mod x (add_mod y z).  

