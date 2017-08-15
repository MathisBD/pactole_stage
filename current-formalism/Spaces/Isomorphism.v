(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import Utf8.
Require Import SetoidDec.
(* Require Import Equalities. *)
(* Require Import Morphisms. *)
Require Import Rbase Rbasic_fun.
Require Import Psatz.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Configurations.
Require Import Pactole.Spaces.Graph.
Set Implicit Arguments.


(****************************)
(** *  Grapb Isomorphisms  **)
(****************************)


Section Isomorphism.
Context (V E : Type).
Context {G : Graph V E}.

Record isomorphism := {
  iso_V :> bijection V;
  iso_E : bijection E;
  iso_T : bijection R;
  iso_morphism : forall e, iso_V (src e) == src (iso_E e)
                        /\ iso_V (tgt e) == tgt (iso_E e);
  iso_threshold : forall e, iso_T (threshold e) = threshold (iso_E e);
  iso_incr : forall a b, (a < b)%R -> (iso_T a < iso_T b)%R;
  iso_bound_T : forall r, (0 < iso_T r < 1)%R <-> (0 < r < 1)%R }.

Global Instance isomorphism_Setoid : Setoid isomorphism := {
  equiv := fun iso1 iso2 => iso1.(iso_V) == iso2.(iso_V)
                         /\ iso1.(iso_E) == iso2.(iso_E)
                         /\ iso1.(iso_T) == iso2.(iso_T) }.
Proof. simpl. split.
+ intro f. repeat split; now intro.
+ intros f g Hfg; destruct Hfg as [HV [HE HT]]. repeat split; intro; now symmetry.
+ intros f g h Hfg Hgh. destruct Hfg as [? [? ?]], Hgh as [? [? ?]].
  repeat split; intro; etransitivity; eauto.
Defined.

Instance iso_V_compat : Proper (equiv ==> equiv) iso_V.
Proof. intros ? ? Heq ?. now apply Heq. Qed.

Instance iso_E_compat : Proper (equiv ==> equiv) iso_E.
Proof. intros ? ? Heq ?. now apply Heq. Qed.

Instance iso_T_compat : Proper (equiv ==> equiv) iso_T.
Proof. intros ? ? Heq ?. now apply Heq. Qed.


Definition id : isomorphism.
refine {| iso_V := @id V _;
          iso_E := @id E _;
          iso_T := @id R _ |}.
Proof.
+ now intros.
+ now intros.
+ now intros.
+ now intros.
Defined.


Definition compose (f g : isomorphism) : isomorphism.
refine {|
    iso_V := compose f.(iso_V) g.(iso_V);
    iso_E := compose f.(iso_E) g.(iso_E);
    iso_T := compose f.(iso_T) g.(iso_T) |}.
Proof.
+ intro. simpl. split; now rewrite <- 2 (proj1 (iso_morphism _ _)) || rewrite <- 2 (proj2 (iso_morphism _ _)).
+ intro. simpl. now rewrite 2 iso_threshold.
+ intros. simpl. now do 2 apply iso_incr.
+ intro. simpl. now rewrite 2 iso_bound_T.
Defined.

Infix "∘" := compose (left associativity, at level 59).

Global Instance compose_compat : Proper (equiv ==> equiv ==> equiv) compose.
Proof. intros f1 f2 Hf g1 g2 Hg. repeat split; intro; simpl; now rewrite Hf, Hg. Qed.

Lemma compose_assoc : forall f g h, f ∘ (g ∘ h) == (f ∘ g) ∘ h.
Proof. intros f g h; repeat split; simpl; reflexivity. Qed.

Set Printing Implicit.

Definition inverse (iso : isomorphism) : isomorphism.
  refine {| iso_V := inverse iso.(iso_V);
            iso_E := inverse iso.(iso_E);
            iso_T := inverse iso.(iso_T)
         |}.
Proof.
+ intro. simpl. rewrite <- 2 Inversion, (proj1 (iso_morphism _ _)), (proj2 (iso_morphism _ _)).
  split; apply src_compat || apply tgt_compat; now rewrite Inversion.
+ intro. simpl. change eq with (@equiv R _). rewrite <- Inversion, iso_threshold.
  apply threshold_compat. now rewrite Inversion.
+ intros a b Hab.
  simpl.
  assert (Hincr := iso_incr iso).
  assert (forall x y, @retraction R _ (iso_T iso) x < @retraction R _ (iso_T iso) y -> x < y)%R.
  { intros.
    specialize (Hincr (@retraction R _ (iso_T iso) x) (@retraction R _ (iso_T iso) y) H).
    now do 2 rewrite section_retraction in Hincr. }
  assert (Hnondecr: (forall x y,  x <= y -> @retraction R _ (iso_T iso) x <= @retraction R _ (iso_T iso) y)%R).
  { intros x y Hle. apply Rnot_lt_le. apply Rle_not_lt in Hle. intuition. }
  destruct (Hnondecr a b) as [| Heq]; auto; intuition; [].
  apply (f_equal (iso_T iso)) in Heq. rewrite 2 section_retraction in Heq. lra.
+ intro. simpl.
  assert (Hbound := iso_bound_T iso). specialize (Hbound (@retraction R _ (iso_T iso) r)).
  now rewrite section_retraction in Hbound.
Defined.

Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat : Proper (equiv ==> equiv) inverse.
Proof. intros f g [? [? ?]]. repeat split; intro; simpl; change eq with (@equiv R _); f_equiv; auto. Qed.

Lemma compose_inverse_l : forall iso : isomorphism, iso ⁻¹ ∘ iso == id.
Proof. intro. repeat split; intro; simpl; try now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r : forall iso : isomorphism, iso ∘ (iso ⁻¹) == id.
Proof. intro. repeat split; intro; simpl; try now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose : forall f g : isomorphism, (f ∘ g) ⁻¹ == (g ⁻¹) ∘ (f ⁻¹).
Proof. intros f g; repeat split; intro; simpl; reflexivity. Qed.

Lemma injective : forall iso : isomorphism, Preliminary.injective equiv equiv iso.
Proof.
intros f x y Heq. transitivity (id x); try reflexivity; [].
rewrite <- (compose_inverse_l f). simpl. rewrite Heq.
now apply compose_inverse_l.
Qed.

End Isomorphism.

Arguments isomorphism {V} {E} G.
