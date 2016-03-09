(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.

(* Local Open Scope Z_scope. *)

(* Parameter N:Z. *)
Definition origin := N%Z.

Definition add_mod (x y n: Z) : Z :=  Zmod (Z.add x y) n.

Definition mul_mod (x y n : Z): Z := Zmod (Z.mul x y) n.

Instance add_mod_compact : Proper (eq ==> eq ==> eq ==> eq) add_mod.
Proof.
  intros x x' Hx y y' Hy z z' Hz. unfold add_mod. apply Z.mod_wd. rewrite Hx, Hy.
intuition. intuition. 
Qed.

Lemma mul_mod_proper : Proper (Z.eq ==> Z.eq ==> eq ==> eq) mul_mod.
Proof.
intros x x' Hx y y' Hy z z' Hz. unfold mul_mod. apply Z.mod_wd. rewrite Hx, Hy.
intuition. intuition.
Qed.

Definition opp_mod (x n : Z) : Z := n - x. 

Lemma opp_mod_proper : Proper (Z.eq ==> Z.eq ==> eq) opp_mod.
Proof.
intros x x' Hx z z' Hz. unfold opp_mod. rewrite Hz, Hx. intuition.
Qed.

Definition dist (x y n : Z) : Z := (Zmin (Zmin (add_mod x y n) (add_mod x (Z.sub 0%Z y) n))
                                         (add_mod (Z.sub 0%Z x) y n)).


Definition eq_mod ( x y n : Z): Prop := Zmod x n = Zmod y n.

Lemma dist_sup : forall x y n, Z.ge (dist x y n) 0%Z.
Proof.
intros. unfold dist. unfold Z.min. destruct (match Z.compare (add_mod x y n)  (add_mod x (0 - y) n) with
  | Eq => add_mod x y n
  | Lt => add_mod x y n
  | Gt => add_mod x (0 - y) n
  end ?= add_mod (0 - x) y n)%Z. 
destruct (Z.compare (add_mod x y n) (add_mod x (0 - y) n)); unfold add_mod. unfold Z.modulo.
unfold Z.div_eucl. simpl.

Lemma dist_define : forall x y n, dist x y n = O <-> eq_mod x y n.
Proof.
intros. unfold eq_mod, dist. unfold add_mod. split. unfold Z.min.
destruct (match (x + y) mod n ?= (x + - y) mod n with
     | Eq => (x + y) mod n
     | Lt => (x + y) mod n
     | Gt => (x + - y) mod n
     end ?= (- x + y) mod n)%Z.
destruct ((x + y) mod n ?= (x + - y) mod n)%Z. unfold Z.to_nat. simpl. apply Zplus_mod. simpl. intuition.
+