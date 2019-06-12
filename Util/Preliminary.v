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


Require Import Relations.
Require Import Morphisms.
Require Import SetoidClass.
Require Pactole.Util.FMaps.FMapFacts. (* for prod_Setoid and prod_EqDec *)
Set Implicit Arguments.


Ltac autoclass := eauto with typeclass_instances.
Ltac inv H := inversion H; subst; clear H.


(** **  Tactics  **)

(** A tactic simplifying coinduction proofs. *)
Global Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

(** Destruct matches from innermost to outermost, with or without keeping the associated equality. *)
Ltac destr_match_eq name A :=
  match A with | context[match ?x with | _ => _ end] =>
    destr_match_eq name x (* recursive call *)
    || (* let H := fresh name in *) destruct x eqn:name (* if innermost match, destruct it *)
  end.

Ltac destruct_match_eq name := match goal with | |- ?A => destr_match_eq name A end.

Ltac destr_match A :=
  match A with | context[match ?x with | _ => _ end] =>
    destr_match x (* recursive call *)
    || destruct x (* if innermost match, destruct it *)
  end.

Ltac destruct_match := match goal with | |- ?A => destr_match A end.

(** Tactics to revert hypotheses based on their head symbol *)
Ltac get_head_symbol term :=
  match term with
    | ?f _ => get_head_symbol f
    | _ => term
  end.

(* Revert one hypothesis whose head symbol is [sym]. *)
Ltac revert_one sym :=
  match goal with
    | H : ?A |- _ => let f := get_head_symbol A in let g := get_head_symbol sym in unify f g; revert H
    | |- _ => fail "Symbol" sym "not found"
  end.

(* Revert all hypotheses with the same head symbol as the goal. *)
Ltac revert_all :=
  match goal with
    | |- ?B => repeat revert_one B
  end.

Definition injective {A B : Type} (eqA : relation A) (eqB : relation B) (f : A -> B) : Prop :=
  forall x y, eqB (f x) (f y) -> eqA x y.

Definition monotonic {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  Proper (RA ==> RB) f \/ Proper (RA --> RB) f.

Definition full_relation {A : Type} := fun _ _ : A => True.

Global Hint Extern 0 (full_relation _ _) => exact I.

Instance relation_equivalence_subrelation {A} :
  forall R R' : relation A, relation_equivalence R R' -> subrelation R R'.
Proof. intros R R' Heq x y Hxy. now apply Heq. Qed.

Global Hint Extern 3 (relation_equivalence _ _) => symmetry.

