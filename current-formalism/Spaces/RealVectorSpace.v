(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.


Class RealVectorSpace (T : Type) {S : Setoid T} `{@EqDec T S} := {
  origin : T;
  
  add : T -> T -> T;
  mul : R -> T -> T;
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
  
  mul_1 : forall u, mul 1 u == u;
  one : T; (* TODO: is it really a good name? *)
  non_trivial : one =/= origin}.

Global Arguments origin : simpl never.

Global Existing Instance add_compat.
Global Existing Instance mul_compat.
Global Existing Instance opp_compat.

Delimit Scope VectorSpace_scope with VS.
Arguments add T%type _ _ _ u%VS v%VS.
Arguments mul T%type _ _ _ k%R u%VS.
Arguments opp T%type _ _ _ u%VS.

Notation "0" := (origin) : VectorSpace_scope.
Notation "u + v" := (add u v) : VectorSpace_scope.
Notation "k * u" := (mul k u) : VectorSpace_scope.
Notation "- u" := (opp u) : VectorSpace_scope.
Notation "u - v" := (add u (opp v)) : VectorSpace_scope.

Ltac null x :=
  let Hnull := fresh "Hnull" in
  destruct (x =?= origin) as [Hnull | Hnull]; [try rewrite Hnull in * | change (~x == origin) in Hnull].

Open Scope VectorSpace_scope.

(** ***  Proofs of derivable properties about MetricSpace  **)

Lemma add_reg_r `{RealVectorSpace} : forall w u v, u + w == v + w -> u == v.
Proof.
intros w u v Heq. setoid_rewrite <- add_origin.
now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
Qed.

Lemma add_reg_l `{RealVectorSpace} : forall w u v, w + u == w + v -> u == v.
Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.

Lemma opp_origin `{RealVectorSpace} : - origin == origin.
Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.

Lemma opp_reg `{RealVectorSpace} : forall u v, - u == - v -> u == v.
Proof. intros u v Heq. apply (add_reg_r (opp u)). rewrite add_opp, Heq, add_opp. reflexivity. Qed.

Lemma opp_opp `{RealVectorSpace} : forall u, - (- u) == u.
Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.

Lemma opp_distr_add `{RealVectorSpace} : forall u v, - (u + v) == (- u) + (- v).
Proof.
intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
Qed.

Lemma mul_0 `{RealVectorSpace} : forall u, 0 * u == 0.
Proof.
intro u. apply (add_reg_l u).
rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
ring_simplify (1 + 0)%R. now rewrite mul_1.
Qed.

Lemma minus_morph `{RealVectorSpace} : forall k u, (-k) * u == - (k * u).
Proof.
intros k u. apply (add_reg_l (mul k u)).
rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%R.
apply mul_0.
Qed.

Lemma mul_origin `{RealVectorSpace} : forall k, k * 0 == 0.
Proof.
intro k. apply add_reg_l with (k * 0).
rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
Qed.

Lemma mul_opp `{RealVectorSpace} : forall k u, k * (- u) == - (k * u).
Proof.
intros k u. apply (add_reg_l (k * u)). rewrite <- mul_distr_add.
setoid_rewrite add_opp. now rewrite mul_origin.
Qed.

Lemma mul_reg_l `{RealVectorSpace} : forall k u v, k <> 0%R -> k * u == k * v -> u == v.
Proof.
intros k u v Hk Heq. setoid_rewrite <- mul_1.
replace 1%R with (/k * k)%R by now field.
setoid_rewrite <- mul_morph. rewrite Heq.
reflexivity.
Qed.

Lemma mul_reg_r `{RealVectorSpace} : forall k k' u, u =/= 0 -> k * u == k' * u -> k = k'.
Proof.
intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
assert (Heq0 : (k - k') * u == 0).
{ unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
elim Hu. rewrite <- (mul_1 u). rewrite <- (Rinv_l (k - k')).
- rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
- intro Habs. apply Hneq. now apply Rminus_diag_uniq.
Qed.

Definition middle `{RealVectorSpace} u v := (1/2) * (u + v).

Lemma mul_integral `{RealVectorSpace} : forall k u, k * u == 0 -> k = 0%R \/ u == 0.
Proof.
intros k u Heq. destruct (Rdec k 0%R).
- now left.
- right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
Qed.


(** In a real metric space, we can define straight paths as trajectories. *)
Require Import Pactole.Util.Ratio.
Program Definition straight_path {T} `{RealVectorSpace T} (pt pt' : T) : path T :=
  Build_path _ _ (fun x => pt + (x * (pt' - pt))) _.
Next Obligation.
abstract (intros x y Hxy; apply add_compat; auto; []; apply mul_compat; try apply Hxy; [];
          apply add_compat, opp_compat; reflexivity).
Defined.

Instance straight_path_compat {T} `{RealVectorSpace T} :
  Proper (equiv ==> equiv ==> equiv) straight_path.
Proof.
intros pt1 pt2 Heq pt1' pt2' Heq' x. simpl.
now apply add_compat, mul_compat, add_compat, opp_compat.
Qed.

(** We can simplify this definition in the local frame. *)
Definition local_straight_path {T} `{RVS : RealVectorSpace T} (pt : T) : path T.
Proof.
refine (Build_path _ _ (fun x => @mul _ _ _ RVS x pt) _).
abstract (intros x y Hxy; apply mul_compat; reflexivity || apply Hxy).
Defined.

Instance local_straight_path_compat {T} `{RealVectorSpace T} :
  Proper (equiv ==> equiv) local_straight_path.
Proof. intros pt1 pt2 Heq x. simpl. now apply mul_compat. Qed.
