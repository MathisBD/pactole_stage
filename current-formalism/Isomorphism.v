(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)
Require Import Utf8.
Require Import Setoid.
Require Import Equalities.
Require Import Morphisms.
Require Import Rbase Rbasic_fun.
Require Import Pactole.Preliminary.
Require Import Pactole.Configurations.
Require Import Pactole.Bijection.
Require Import Pactole.CommonGraphFormalism.
Require Import Reals.
Require Import Psatz.


Set Implicit Arguments.


(**********************)
(** *  Similarities  **)
(**********************)


Module Make (Graph : GraphDef)(Loc : LocationADef (Graph)).

  Definition Req (r1 r2: R) := Logic.eq r1 r2.
  Definition Req_equiv : Equivalence Req.
  Proof. 
    unfold Req.
    split; intuition.
    intros r s t Hrs Hst; now transitivity s.
  Qed.

  Record t :=
    {
      sim_V :> Bijection.t Loc.eq;
      sim_E : Bijection.t Graph.Eeq;
      sim_T : Bijection.t Req;
      sim_morphism : forall e, Graph.Veq (sim_V (Graph.src e)) (Graph.src (sim_E e))
                              /\ Graph.Veq (sim_V (Graph.tgt e)) (Graph.tgt (sim_E e));
      sim_threshold : forall e, sim_T (Graph.threshold e) = Graph.threshold (sim_E e);
      sim_croiss : forall a b, (a < b)%R -> (sim_T a < sim_T b)%R;
      sim_bound_T : forall r, (0 < r < 1)%R <-> (0 < sim_T r < 1)%R
  }.

  Definition eq sim1 sim2 := Bijection.eq sim1.(sim_V) sim2.(sim_V)
                          /\ Bijection.eq sim1.(sim_E) sim2.(sim_E)
                          /\ Bijection.eq sim1.(sim_T) sim2.(sim_T).
  
Global Instance eq_equiv : Equivalence eq.
Proof. unfold eq, Bijection.eq. split.
+ intros f. repeat split; intros l1 l2 Hl; rewrite Hl; reflexivity.
+ intros f g Hfg; destruct Hfg as (H, (H0, H1)); repeat split; intros x y Hxy;
  symmetry in Hxy.
  specialize (H y x Hxy).
  now symmetry.
  specialize (H0 y x Hxy).
  now symmetry.
  specialize (H1 y x Hxy).
  now symmetry.
+ intros f g h Hfg Hgh. destruct Hfg as (Hf, (Hf0, Hf1)), Hgh as (Hg , (Hg0, Hg1)).
  repeat split; intros x y Hxy.
  specialize (Hf x y Hxy); specialize (Hg y y (reflexivity y)).
  rewrite Hf, Hg.
  reflexivity.
  specialize (Hf0 x y Hxy); specialize (Hg0 y y (reflexivity y)).
  rewrite Hf0, Hg0.
  reflexivity.
  specialize (Hf1 x y Hxy); specialize (Hg1 y y (reflexivity y)).
  rewrite Hf1, Hg1.
  reflexivity.
Qed.

Instance V_compat : Proper (eq ==> @Bijection.eq _ Loc.eq) sim_V.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

Instance E_compat : Proper (eq ==> @Bijection.eq _ Graph.Eeq) sim_E.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

Instance T_compat : Proper (eq ==> @Bijection.eq _ Req) sim_T.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.



Definition id : t.
  refine {| sim_V := Bijection.id Loc.eq_equiv;
            sim_E := Bijection.id Graph.Eeq_equiv;
            sim_T := Bijection.id Req_equiv |}.
  Proof.
    + intros e. now simpl.
    + intro e; now simpl.
    + intros; now simpl.
    + intros; now simpl.
  Defined.


Definition compose (f g : t) : t.
refine {|
    sim_V := Bijection.compose _ f.(sim_V) g.(sim_V);
    sim_E := Bijection.compose _ f.(sim_E) g.(sim_E);
    sim_T := Bijection.compose _ f.(sim_T) g.(sim_T) |}.
Proof.
  + intros; simpl.
    generalize (sim_morphism g e).
    generalize (sim_morphism f (g.(sim_E) e)).
    intros.
    destruct H0;
    split.
    now rewrite H0.
    now rewrite H1.
  + intros e.
    simpl.
    generalize (sim_threshold g e).
    generalize (sim_threshold f (g.(sim_E) e)).
    intros.
    now rewrite H0, H.
  + intros a b.
    simpl.
    intros.
    now apply (sim_croiss f), (sim_croiss g).
  + intros.
    simpl.
    split; intros.
    now apply (sim_bound_T g), (sim_bound_T f) in H.
    now apply (sim_bound_T g), (sim_bound_T f).
Defined.


Global Infix "∘" := compose (left associativity, at level 59).

Global Instance compose_compat : Proper (eq ==> eq ==> eq) compose.
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold eq, Bijection.eq in *.
  repeat split; intros x y Hxy; cbn; intuition.
Qed.

Lemma compose_assoc : forall f g h, eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h; repeat split; intros x y Hxy; simpl; now rewrite Hxy. Qed.

Set Printing Implicit.

Definition inverse (sim : t) : t.
  refine {| sim_V := Bijection.inverse _ sim.(sim_V);
            sim_E := Bijection.inverse _ sim.(sim_E);
            sim_T := Bijection.inverse _ sim.(sim_T)
         |}.
Proof.
  + intros.
    simpl.
    generalize ((sim_morphism sim) (retraction (sim_E sim) e)).
    intro.
    destruct H.
    split;
    apply (Inversion (sim_V sim)).
    rewrite H.
    now rewrite (section_retraction Graph.Eeq_equiv).
    rewrite H0.
    now rewrite (section_retraction Graph.Eeq_equiv).
  + intros e; assert (Hthresh := sim_threshold sim (retraction sim.(sim_E) e)); simpl.
    apply Inversion.
    rewrite Hthresh.
    f_equiv.
    now rewrite ((section_retraction Graph.Eeq_equiv)).
  + intros a b Hab.
    simpl.
    assert (Hcrois :=sim_croiss (sim)).
    assert (forall x y, @retraction R Req (sim_T sim) x < @retraction R Req (sim_T sim) y -> x < y)%R.
    { intros.
      specialize (Hcrois (@retraction R Req (sim_T sim) x) (@retraction R Req (sim_T sim) y) H).
      do 2 rewrite section_retraction in Hcrois; try apply Req_equiv.
      assumption.
    }
    assert (forall x y,  x <= y -> @retraction R Req (sim_T sim) x <= @retraction R Req (sim_T sim) y)%R.
    {
      intuition.
      assert (contra : forall (A B: Prop), (A -> B) -> (~B -> ~A)) by intuition.
      assert (Hc := contra (@retraction R Req (sim_T sim) y < @retraction R Req (sim_T sim) x)%R (y < x)%R (H y x)).
      apply Rle_not_lt in H0.
      apply Rnot_lt_le.
      apply (Hc H0).
    }
    destruct (H0 a b).    
    intuition.
    assumption.
    assert (a = b)%R.
    assert (Hcomp := section_compat ((sim_T sim)) (@retraction R Req (sim_T sim) a)
                                    (@retraction R Req (sim_T sim) b) H1).
    do 2 rewrite section_retraction in Hcomp; try apply Req_equiv.
    now unfold Req.
    lra.
  + intros; simpl.
    assert (Hbound := sim_bound_T sim);
      specialize (Hbound (@retraction R Req (sim_T sim) r)).
    rewrite section_retraction in Hbound.
    now symmetry.
    apply Req_equiv.
Defined.

Global Notation "s ⁻¹" := (inverse s) (at level 99).

Global Instance inverse_compat : Proper (eq ==> eq) inverse.
Proof. intros f g Hfg. unfold eq.
       repeat split; intros x y Hxy; simpl; rewrite Hxy; f_equiv; apply Hfg. Qed.

Lemma compose_inverse_l : forall sim : t, eq (sim ⁻¹ ∘ sim) id.
Proof. intros sim. repeat split; intros x y Hxy; simpl; try now rewrite retraction_section; autoclass. Qed.

Lemma compose_inverse_r : forall sim : t, eq (sim ∘ (sim ⁻¹)) id.
Proof. intros sim; repeat split; intros x y Hxy; simpl; try now rewrite section_retraction; autoclass. Qed.

Lemma inverse_compose : forall f g : t, eq ((f ∘ g) ⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g; repeat split; intros x y Hxy; simpl; rewrite Hxy; reflexivity. Qed.

End Make.

