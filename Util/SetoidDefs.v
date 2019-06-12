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


Require Import Rbase.
Require Import RelationPairs.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Set Implicit Arguments.


(* To avoid infinite loops, we use a breadth-first search... *)
Typeclasses eauto := (bfs) 20.
(* but we need to remove [eq_setoid] as it matches everything... *)
Remove Hints eq_setoid : Setoid.
(* while still declaring it for the types for which we still want to use it. *)
Instance R_Setoid : Setoid R := eq_setoid R.
Instance Z_Setoid : Setoid Z := eq_setoid Z.
Instance nat_Setoid : Setoid nat := eq_setoid nat.
Instance bool_Setoid : Setoid bool := eq_setoid bool.
Instance unit_Setoid : Setoid unit := eq_setoid unit.

Notation "x == y" := (equiv x y).
Arguments complement A R x y /.
Arguments Proper {A}%type R%signature m.


(** **  Setoid Definitions  **)

Instance fun_equiv A B `(Setoid B) : Setoid (A -> B) | 4.
Proof. exists (fun f g : A -> B => forall x, f x == g x).
split.
+ repeat intro. reflexivity.
+ intros ? ? Heq ?. symmetry. apply Heq.
+ repeat intro. etransitivity; eauto.
Defined.

Instance fun_equiv_pointwise_compat A B `{Setoid B} :
  subrelation (@equiv _ (fun_equiv A _)) (pointwise_relation _ equiv).
Proof. intros f g Hfg x. apply Hfg. Qed.

Notation "x =?= y" := (equiv_dec x y) (at level 70, no associativity).

(** Lifting an equivalence relation to an option type. *)
Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
  match xo, yo with
    | None, None => True
    | None, Some _ | Some _, None => False
    | Some x, Some y => eqT x y
  end.

Instance opt_eq_refl : forall T (R : T -> T -> Prop), Reflexive R -> Reflexive (opt_eq R).
Proof. intros T R HR [x |]; simpl; auto. Qed.

Instance opt_eq_sym : forall T (R : T -> T -> Prop), Symmetric R -> Symmetric (opt_eq R).
Proof. intros T R HR [x |] [y |]; simpl; auto. Qed.

Instance opt_eq_trans : forall T (R : T -> T -> Prop), Transitive R -> Transitive (opt_eq R).
Proof. intros T R HR [x |] [y |] [z |]; simpl; intros; eauto; contradiction. Qed.

Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
Proof. split; auto with typeclass_instances. Qed.

Instance opt_Setoid T (S : Setoid T) : Setoid (option T) := {| equiv := opt_eq equiv |}.

Instance Some_compat `(Setoid) : Proper (equiv ==> @equiv _ (opt_Setoid _)) Some.
Proof. intros ? ? Heq. apply Heq. Qed.

Instance prod_Setoid : forall A B, Setoid A -> Setoid B -> Setoid (A * B) :=
  Pactole.Util.FMaps.FMapInterface.prod_Setoid.
Instance prod_EqDec A B `(EqDec A) `(EqDec B) : EqDec (@prod_Setoid A B _ _) :=
  Pactole.Util.FMaps.FMapInterface.prod_EqDec _ _.
Arguments prod_EqDec [A] [B] {_} _ {_} _.

Instance fst_compat {A B} : forall R S, Proper (R * S ==> R) (@fst A B) := fst_compat.
Instance snd_compat {A B} : forall R S, Proper (R * S ==> S) (@snd A B) := snd_compat.

Instance sig_Setoid {T} (S : Setoid T) {P : T -> Prop} : Setoid (sig P) := {|
  equiv := fun x y => proj1_sig x == proj1_sig y |}.
Proof. split.
+ intro. reflexivity.
+ intros ? ?. now symmetry.
+ intros ? ? ? ? ?. etransitivity; eauto.
Defined.

Instance sig_EqDec {T} {S : Setoid T} (E : EqDec S) (P : T -> Prop) : EqDec (@sig_Setoid T S P).
Proof. intros ? ?. simpl. apply equiv_dec. Defined.

Instance sigT_Setoid {T} (S : Setoid T) {P : T -> Type} : Setoid (sigT P) := {|
  equiv := fun x y => projT1 x == projT1 y |}.
Proof. split.
+ intro. reflexivity.
+ intros ? ?. now symmetry.
+ intros ? ? ? ? ?. etransitivity; eauto.
Defined.

Instance sigT_EqDec {T} {S : Setoid T} (E : EqDec S) (P : T -> Type) : EqDec (@sigT_Setoid T S P).
Proof. intros ? ?. simpl. apply equiv_dec. Defined.

(* The intersection of equivalence relations is still an equivalence relation. *)
Lemma inter_equivalence T R1 R2 (E1 : Equivalence R1) (E2 : Equivalence R2)
  : Equivalence (fun x y : T => R1 x y /\ R2 x y).
Proof. split.
+ split; reflexivity.
+ now split; symmetry.
+ intros ? ? ? [] []. split; etransitivity; eauto.
Qed.

(* TODO: set it as an instance and fix all the typeclass search loops that appear *)
Definition inter_Setoid {T} (S1 : Setoid T) (S2 : Setoid T) : Setoid T := {|
  equiv := fun x y => @equiv T S1 x y /\ @equiv T S2 x y;
  setoid_equiv := inter_equivalence setoid_equiv setoid_equiv |}.

Definition inter_EqDec {T} {S1 S2 : Setoid T} (E1 : EqDec S1) (E2 : EqDec S2) : EqDec (inter_Setoid S1 S2).
Proof.
intros x y. destruct (E1 x y), (E2 x y); (now left; split) || (right; intros []; contradiction).
Defined.

Definition inter_subrelation_l : forall {T} {S1 S2 : Setoid T},
  subrelation (@equiv T (inter_Setoid S1 S2)) (@equiv T S1).
Proof. now intros ? ? ? ? ? []. Qed.

Definition inter_subrelation_r : forall {T} {S1 S2 : Setoid T},
  subrelation (@equiv T (inter_Setoid S1 S2)) (@equiv T S2).
Proof. now intros ? ? ? ? ? []. Qed.

Definition inter_compat_l {T U} {S1 S2 : Setoid T} `{Setoid U} : forall f : T -> U,
  Proper (@equiv T S1 ==> equiv) f -> Proper (@equiv T (inter_Setoid S1 S2) ==> equiv) f.
Proof. intros f Hf x y Heq. apply Hf, Heq. Qed.

Definition inter_compat_r {T U} {S1 S2 : Setoid T} `{Setoid U} : forall f : T -> U,
  Proper (@equiv T S2 ==> equiv) f -> Proper (@equiv T (inter_Setoid S1 S2) ==> equiv) f.
Proof. intros f Hf x y Heq. apply Hf, Heq. Qed.

(** Setoid by precomposition *)
Definition compose_Equivalence T U R (E : @Equivalence U R) :
  forall f : T -> U, Equivalence (fun x y => R (f x) (f y)).
Proof. split.
+ intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. now transitivity (f y).
Qed.

(* TODO: set it as an instance and fix all the typeclass search loops that appear *)
Definition compose_Setoid {T U} (f : T -> U) {S : Setoid U} : Setoid T := {|
  equiv := fun x y => f x == f y;
  setoid_equiv := compose_Equivalence setoid_equiv f |}.

Definition compose_EqDec {T U} (f : T -> U) `{EqDec U}
  : EqDec (compose_Setoid f) := fun x y => f x =?= f y.

Definition compose_compat {T U} (f : T -> U) `{Setoid U} :
  Proper (@equiv T (compose_Setoid f) ==> equiv) f.
Proof. intros x y Heq. apply Heq. Qed.
