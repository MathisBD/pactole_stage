(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)

Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.


Set Implicit Arguments.


Section WfLexicographic_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive lexprod : A*B -> A*B -> Prop :=
  | left_lex :
      forall (x x':A) (y y':B), leA x x' -> lexprod (x, y) (x', y')
  | right_lex :
      forall (x:A) (y y':B), leB y y' -> lexprod (x, y) (x, y').

  Notation LexProd := (lexprod leA leB).

  Lemma acc_A_B_lexprod :
    forall x:A,
      Acc leA x ->
      (forall x0:A, clos_trans A leA x0 x -> well_founded leB) ->
      forall y:B, Acc leB y -> @Acc (A*B) lexprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    cut (leA x2 x); intros.
    apply IHAcc; auto with sets.
    intros.
    eapply H2.
    apply t_trans with x2; auto with sets.
    eassumption.

    red in H2.
    eapply H2.
    eauto with sets.

    injection H1.
    destruct 2.
    injection H3.
    destruct 2; auto with sets.

    rewrite <- H1.
    injection H3; intros _ Hx1.
    subst x1.
    apply IHAcc0.
    inversion H1.
    inversion H3.
    subst.
    assumption.
  Defined.

  Theorem wf_lexprod :
    well_founded leA ->
    well_founded leB -> well_founded lexprod.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a.
    apply acc_A_B_lexprod; auto with sets; intros.
  Defined.

End WfLexicographic_Product.

Global Arguments lexprod  [A] [B] leA leB _ _.


Instance lexprod_compat: Proper (eq * eq ==> eq * eq ==> iff) (lexprod lt lt).
Proof.
  intros (a,b) (a',b') (heqa , heqb) (c,d) (c',d') (heqc , heqd) .
  hnf in *|-.
  simpl in *|-.
  subst.
  reflexivity.
Qed.
