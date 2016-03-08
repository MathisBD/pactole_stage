(* Test for the definition of an modular arithmetic by: Robin Pelle*)

Require Import ZArith.
Require Import Omega.
Require Import SetoidList.

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

Definition dist (x y n : Z) : nat := min ( Z.to_nat (x + y mod n)%Z) (Z.to_nat (Z.abs (x-y))).
(* pas besoin de mettre le mod n dans le cas de la soustraction car x et y sont dans l'anneau.*)
