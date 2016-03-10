(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.
Require Import Ensembles.


(* Local Open Scope Z_scope. *)
Definition n := nat. (*
(* Parameter N:Z. *)
Module ringDef : DiscretSpaceDef with Definition t :=   ensembles_finis(Finite Z, cardinal Z n).
Definition origin := N%Z.*)

Definition add_mod (x y :Z) (n:nat): nat := Z.to_nat (Zmod (x + y) (Z.of_nat n)).

Definition mul_mod (x y : Z) n: nat := Z.to_nat (Zmod (Z.mul x y) (Z.of_nat n)).

Lemma sss : forall x y, x >= y -> x > y \/ x = y.
Proof.
intros x y. omega.
Qed.

Lemma mod_pos_z : forall (n:nat) (x:Z), (Zmod x (Z.of_nat n) >= 0)%Z.
intros. unfold Z.of_nat. destruct n0. rewrite Zmod_0_r. omega. 
rewrite Zge_left. rewrite Z.mod_pos_bound.
 
admit. 
Admitted.



Instance add_mod_compact : Proper (eq ==> eq ==> eq ==> eq) add_mod.
Proof.
   intros x x' Hx y y' Hy z z' Hz. unfold add_mod. unfold Z.to_nat.  apply mod_pos_z. apply Z.mod_wd.
   rewrite Hx, Hy; intuition. rewrite Hz. intuition.
Qed.

Lemma mul_mod_proper : Proper (Z.eq ==> Z.eq ==> eq ==> eq) mul_mod.
Proof.
intros x x' Hx y y' Hy z z' Hz. unfold mul_mod. apply Z.mod_wd. rewrite Hx, Hy.
intuition. rewrite Hz. intuition.
Qed.

Definition opp_mod (x: Z) (n:nat): Z := (Z.of_nat n) - x. 

Lemma opp_mod_proper : Proper (eq ==> eq ==> eq) opp_mod.
Proof.
intros x x' Hx z z' Hz. unfold opp_mod. rewrite Hz, Hx. intuition.
Qed.

Definition dist (x y : Z) (n:nat) : nat := min (add_mod (opp_mod y n) x n) (add_mod (opp_mod x n) y n) .

Definition eq_mod ( x y n : Z): Prop := Zmod x n = Zmod y n.



(* Lemma dist_sup : forall x y n, Z.ge (dist x y n) 0%Z.
Proof.
intros x y n. unfold dist. unfold add_mod, opp_mod.  unfold Z.min. unfold Z.eqb. 
destruct ( Z.compare ((Z.of_nat n - y + x) mod Z.of_nat n) ((Z.of_nat n - x + y) mod Z.of_nat n)).
apply Zmod_0_r. apply Z.mod_pos_bound. intuition. 
 *)

Lemma dist_define : forall x y n, dist x y n = 0 <-> eq_mod x y n.
Proof.
intros. unfold eq_mod, dist. unfold add_mod. split. unfold Z.min.
destruct (match (x + y) mod n ?= (x + - y) mod n with
     | Eq => (x + y) mod n
     | Lt => (x + y) mod n
     | Gt => (x + - y) mod n
     end ?= (- x + y) mod n)%Z.
destruct ((x + y) mod n ?= (x + - y) mod n)%Z. unfold Z.to_nat. simpl. apply Zplus_mod. simpl. intuition.
+