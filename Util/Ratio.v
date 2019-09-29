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


Require Import Omega.
Require Import Morphisms.
Require Import Rbase.
Require Import Psatz.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Pactole.Util.Coqlib.

(** **  Ratio  **)

(** A ratio (of some quantity), as a real number between [0] and [1]. *)
Definition ratio := {x : R | 0 <= x <= 1}%R.

Instance ratio_Setoid : Setoid ratio := sig_Setoid _.
Instance ratio_EqDec : EqDec ratio_Setoid := sig_EqDec _ _.

Definition proj_ratio : ratio -> R := @proj1_sig _ _.

Instance proj_ratio_compat : Proper (equiv ==> equiv) proj_ratio.
Proof. intros ? ? Heq. apply Heq. Qed.

Coercion proj_ratio : ratio >-> R.

Lemma ratio_bounds : forall r : ratio, (0 <= r <= 1)%R.
Proof. intros [r Hr]. apply Hr. Qed.

(** Building rational ratios. *)
Lemma mk_ratio_proof : forall n m, 0 < m -> n <= m -> (0 <= INR n / INR m <= 1)%R.
Proof.
intros n m Hm Hn. apply le_INR in Hn. apply lt_0_INR in Hm. split.
+ apply Rdiv_le_0_compat; auto using pos_INR.
+ now apply Rdiv_le_1.
Qed.

(* Convenient notations.
   The first one is used to automatically provide the proofs, whereas the second one is used for display. *)
Definition mk_ratio n m Hm Hn : ratio := exist _ _ (mk_ratio_proof n m Hm Hn).
Notation "n '/r' m" := (mk_ratio n m ltac:(clear; abstract omega) ltac:(clear; abstract omega))
  (only parsing, at level 10).
Notation "n '/r' m" := (mk_ratio n m _ _) (at level 10, only printing).

(** 0 and 1 are ratios. *)
Definition ratio_0 : ratio.
Proof. refine (exist _ 0%R _). abstract lra. Defined.
Definition ratio_1 : ratio.
Proof. refine (exist _ 1%R _). abstract lra. Defined.

(** Addition between ratios *)
Definition add_ratio (r1 r2 : ratio) : ratio.
refine (if Rle_dec R1 (r1 + r2) then ratio_1
        else exist _ (r1 + r2)%R _).
Proof.
abstract (split; solve [ apply Rplus_le_le_0_compat; apply ratio_bounds
                       | now apply Rlt_le, Rnot_le_lt ]).
Defined.

Instance add_ratio_compat : Proper (equiv ==> equiv ==> equiv) add_ratio.
Proof. intros [] [] ? [] [] ?. unfold add_ratio. simpl in *. subst. destruct_match; reflexivity. Qed.

(** A strict ratio is a [ratio] that is neither [0] nor [1]. *)
Definition strict_ratio := {x : R | 0 < x < 1}%R.

Instance strict_ratio_Setoid : Setoid ratio := sig_Setoid _.
Instance strict_ratio_EqDec : EqDec strict_ratio_Setoid := sig_EqDec _ _.

Definition proj_strict_ratio (x : strict_ratio) : ratio :=
  let '(exist _ v Hv) := x in
  exist _ v (conj (Rlt_le _ _ (proj1 Hv)) (Rlt_le _ _ (proj2 Hv))).

Instance proj_strict_ratio_compat : Proper (equiv ==> equiv) proj_strict_ratio.
Proof. intros [] [] Heq. apply Heq. Qed.

Coercion proj_strict_ratio : strict_ratio >-> ratio.

Lemma strict_ratio_bounds : forall r : strict_ratio, (0 < r < 1)%R.
Proof. intros [r Hr]. apply Hr. Qed.

Lemma mk_strict_ratio_proof : forall n m, 0 < n -> n < m -> (0 < INR n / INR m < 1)%R.
Proof.
intros n m Hm Hn. apply lt_INR in Hn. apply lt_0_INR in Hm. split.
+ apply Rdiv_lt_0_compat; eauto using Rlt_trans.
+ apply Rle_neq_lt.
  - apply Rdiv_le_1; lra.
  - intro Habs. eapply Rlt_not_eq; eauto; [].
    replace (INR n) with (INR n / INR m * INR m)%R by (field; lra).
    now rewrite Habs, Rmult_1_l.
Qed.

Definition mk_strict_ratio n m Hm Hn : strict_ratio := exist _ _ (mk_strict_ratio_proof n m Hm Hn).
Notation "n '/sr' m" := (mk_strict_ratio n m ltac:(clear; abstract omega) ltac:(clear; abstract omega))
  (only parsing, at level 10).
Notation "n '/sr' m" := (mk_strict_ratio n m _ _) (at level 10, only printing).

(** **  Trajectory  **)

(** Trajectories are paths inside the space. *)
(* FIXME: I should use typeclasses to avoid the explicit parameter T.
          Otherwise, path cannot be used as a target class for coercions. *)
Record path T `{Setoid T}:= {
  path_f :> ratio -> T;
  path_compat :> Proper (equiv ==> equiv) path_f }.
Arguments path_f {T} {_} _ _.

Instance path_Setoid T {S : Setoid T} : Setoid (path T) := { equiv := fun x y => path_f x == y }.
Proof. split.
+ intro. reflexivity.
+ intros ? ? ?. now symmetry.
+ intros ? ? ? ? ?. etransitivity; eauto.
Defined.

Instance path_full_compat {T} `(Setoid T): Proper (equiv ==> equiv ==> equiv) path_f.
Proof.
intros p p' Hp x y Hxy. transitivity (path_f p y).
- now apply path_compat.
- apply Hp.
Qed.

(** Given a function [f : T -> U] compatible with the space equivalences,
    we can lift paths on [T] into paths on [U]. *)
Definition lift_path {T U} `{Setoid T, Setoid U} (f : T -> U)
                     {Hf : Proper (equiv ==> equiv) f} (p : path T) : path U.
refine (Build_path _ _ (fun x => f (p x)) _).
Proof. intros x y Hxy. now apply Hf, path_compat. Defined.
Arguments lift_path T U _ _ f _ p /.

Instance lift_path_compat {T U} {HT : Setoid T} {HU : Setoid U} :
  forall f (Hf : Proper (equiv ==> equiv) f), Proper (equiv ==> equiv) (@lift_path T U HT HU f Hf).
Proof. repeat intro. simpl. auto. Qed.

Lemma lift_path_proof_irrelevant {T U} {HT : Setoid T} {HU : Setoid U} :
  forall f (Hf Hf' : Proper (equiv ==> equiv) f), @lift_path T U HT HU f Hf == @lift_path T U HT HU f Hf'.
Proof. now repeat intro. Qed.

Lemma lift_path_extensionality_compat {T U} {HT : Setoid T} {HU : Setoid U} :
  forall (f g : T -> U) (Hf : Proper (equiv ==> equiv) f) (Hg : Proper (equiv ==> equiv) g),
  (equiv ==> equiv)%signature f g ->
  (equiv ==> equiv)%signature (lift_path f) (lift_path g).
Proof. repeat intro. simpl. auto. Qed.
