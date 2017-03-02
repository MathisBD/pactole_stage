Require Import Utf8.
Require Import Setoid.
Require Import Equalities.
Require Import Morphisms.
Require Import Rbase Rbasic_fun.
Require Import Pactole.Preliminary.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.


Set Implicit Arguments.


(********************)
(** *  Bijections  **)
(********************)

(** Bijections on a type [T] with an equivalence relation [eqT] *)

Section Bijections.
Context (T : Type).
Context (eqT : T -> T -> Prop).
Context (HeqT : Equivalence eqT).

Record bijection := {
  section :> T → T;
  retraction : T → T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.

Definition bij_eq (f g : bijection) := (eqT ==> eqT)%signature f.(section) g.

Global Instance bij_eq_equiv : Equivalence bij_eq.
Proof. split.
+ intros f x y Hxy. apply section_compat. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

Global Existing Instance section_compat.

Global Instance section_full_compat : Proper (bij_eq ==> (eqT ==> eqT)) section.
Proof. intros f g Hfg x y Hxy. now apply Hfg. Qed.

(** The identity bijection *)
Definition bij_id := {|
  section := fun x => x;
  retraction := fun x => x;
  section_compat := fun x y Heq => Heq;
  Inversion := ltac:(easy) |}.

(** Composition of bijections *)
Definition bij_compose (f g : bijection) : bijection.
refine {| section := fun x => f (g x);
          retraction := fun x => g.(retraction) (f.(retraction) x) |}.
Proof.
+ abstract (intros x y Hxy; now apply f.(section_compat), g.(section_compat)).
+ abstract (intros x y; now rewrite f.(Inversion), <- g.(Inversion)).
Defined.
Infix "∘" := bij_compose (left associativity, at level 59).

Lemma bij_compose_assoc : forall f g h : bijection, bij_eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
Proof. intros f g h x y Hxy. rewrite Hxy. reflexivity. Qed.

(** Properties about inverse functions *)
Global Instance retraction_compat : Proper (bij_eq ==> (eqT ==> eqT)) retraction.
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

Definition bij_inverse (bij : bijection) : bijection.
refine {| section := bij.(retraction);
          retraction := bij.(section) |}.
Proof. abstract (intros; rewrite bij.(Inversion); reflexivity). Defined.

Notation "bij ⁻¹" := (bij_inverse bij) (at level 99).

Lemma retraction_section : forall (bij : bijection) x, eqT (bij.(retraction) (bij.(section) x)) x.
Proof. intros bij x. simpl. rewrite <- bij.(Inversion). now apply section_compat. Qed.

Corollary bij_inv_bij_id : forall (bij : bijection), bij_eq (bij ⁻¹ ∘ bij) bij_id.
Proof. repeat intro. simpl. now rewrite retraction_section. Qed.

Lemma section_retraction : forall (bij : bijection) x, eqT (bij.(section) (bij.(retraction) x)) x.
Proof. intros bij x. rewrite bij.(Inversion). now apply retraction_compat. Qed.

Corollary inv_bij_bij_id : forall (bij : bijection),
  (eqT ==> eqT)%signature (fun x => bij (bij ⁻¹ x)) bij_id.
Proof. repeat intro. simpl. now rewrite section_retraction. Qed.

Lemma injective_retraction : forall bij : bijection, injective eqT eqT bij -> injective eqT eqT (bij ⁻¹).
Proof.
intros bij Hinj x y Heq. rewrite <- (section_retraction bij x), Heq. simpl. now rewrite section_retraction.
Qed.

Lemma compose_inverse : forall f g : bijection, bij_eq ((f ∘ g)⁻¹) ((g ⁻¹) ∘ (f ⁻¹)).
Proof. intros f g x y Hxy. rewrite Hxy. reflexivity. Qed.

End Bijections.


(**********************)
(** *  Similarities  **)
(**********************)


(** Similarities are functions that multiply distances by a constant zoom.
    Unlike bijections that only need a setoid, we need here a metric space.
    For convenience, we also add their center, that is the location from which robots locally observe. *)
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
      sim_V :> bijection Loc.eq;
      sim_E :> bijection Graph.Eeq;
      sim_T :> bijection Req;
      sim_integrity : forall (e : Graph.E) l1 l2,
          (Graph.Veq (Graph.src e) l1 /\ (Graph.Veq (Graph.tgt e) l2))
          -> (Graph.Veq (sim_V l1) (Graph.src (sim_E e)) /\
              Graph.Veq (sim_V l2) (Graph.tgt (sim_E e)));
      sim_utility : forall e, Graph.Veq (sim_V (Graph.src e)) (Graph.src (sim_E e))
                              /\ Graph.Veq (sim_V (Graph.tgt e)) (Graph.tgt (sim_E e));
      sim_threshold : forall e, sim_T (Graph.threshold e) = Graph.threshold (sim_E e);
      sim_threshold_if : forall e0 r,
          Loc.eq
            (retraction sim_V
               (if Rle_dec r (Graph.threshold (section sim_E e0))
                then Graph.src (section sim_E e0)
                else Graph.tgt (section sim_E e0)))
            (if Rle_dec r (Graph.threshold e0)
             then Graph.src e0
             else Graph.tgt e0)
  }.

  Definition eq sim1 sim2 := bij_eq sim1.(sim_V) sim2.(sim_V)
                             /\ bij_eq sim1.(sim_E) sim2.(sim_E)
                             /\ bij_eq sim1.(sim_T) sim2.(sim_T).
  
Global Instance eq_equiv : Equivalence eq.
Proof. unfold eq, bij_eq. split.
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

Instance V_compat : Proper (eq ==> @bij_eq _ Loc.eq) sim_V.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

Instance E_compat : Proper (eq ==> @bij_eq _ Graph.Eeq) sim_E.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.

Instance T_compat : Proper (eq ==> @bij_eq _ Req) sim_T.
Proof. intros sim1 sim2 Hsim ? ? Heq. now apply Hsim. Qed.


(** As similarities are defined as bijections, we can prove that k <> 0
    (this requires that the metric space is not trivial (i.e. has dimension > 0). *)

(** The identity similarity *)
Definition id : t.
  refine {| sim_V := bij_id Loc.eq_equiv;
            sim_E := bij_id Graph.Eeq_equiv;
            sim_T := bij_id Req_equiv |}.
  Proof.
    + intros e l1 l2 (Hls, Hlt); now split.
    + intros e. now simpl.
    + intro e; now simpl.
    + intros; now simpl.
  Defined.


(** Composition of similarity *)

Definition compose (f g : t) : t.
refine {|
    sim_V := bij_compose _ f.(sim_V) g.(sim_V);
    sim_E := bij_compose _ f.(sim_E) g.(sim_E);
    sim_T := bij_compose _ f.(sim_T) g.(sim_T) |}.
Proof.
  + intros e l1 l2 H.
    split; simpl;
      generalize (sim_integrity g H); intro Hg;
        assert (Graph.Veq (Graph.src ((sim_E g) e)) (g l1) ∧
                Graph.Veq (Graph.tgt ((sim_E g) e)) (g l2))
        by intuition;
        generalize (sim_integrity f H0);
        intro; intuition.
  + intros; simpl.
    generalize (sim_utility g e).
    generalize (sim_utility f (g.(sim_E) e)).
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
  + intros e r.
    simpl.
    generalize (sim_threshold_if g e r).
    generalize (sim_threshold_if f (g.(sim_E) e) r).
    intros Hf Hg.
    now rewrite Hf, Hg.
Defined.
Global Infix "∘" := compose (left associativity, at level 59).

Global Instance compose_compat : Proper (eq ==> eq ==> eq) compose.
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold eq, bij_eq in *.     
  repeat split; intros x y Hxy;
  cbn;
  destruct Hf, Hg.
  apply H, H1, Hxy.
  apply H0, H2, Hxy.
  apply H0, H2, Hxy.
Qed.
  
  Lemma compose_assoc : forall f g h, eq (f ∘ (g ∘ h)) ((f ∘ g) ∘ h).
  Proof. intros f g h; repeat split; intros x y Hxy; simpl; now rewrite Hxy. Qed.

  Set Printing Implicit.
  
  Definition inverse (sim : t) : t.
    refine {| sim_V := bij_inverse _ sim.(sim_V);
              sim_E := bij_inverse _ sim.(sim_E);
              sim_T := bij_inverse _ sim.(sim_T)
           |}.
Proof.
  + intros. simpl.
    generalize (sim.(sim_integrity) H).
    generalize (sim.(sim_utility) (retraction (sim_E sim) e)).
    intros.
    destruct H, H1.
    assert (Hfe := Graph.find_edge_Some (sim.(sim_E) e)).
    assert (Hinv := Inversion (sim_E sim)).
    rewrite <- H1, <- H3 in Hfe.
    rewrite <- H, <- H2.
    split.
    apply (Inversion (sim_V sim)).
    destruct H0 as (Hs, Ht).
    rewrite Hs.
    now rewrite (section_retraction Graph.Eeq_equiv).
    apply (Inversion (sim_V sim)).
    destruct H0 as (Hs, Ht).
    rewrite Ht.
    now rewrite (section_retraction Graph.Eeq_equiv).
  + intros.
    simpl.
    generalize ((sim_utility sim) (retraction (sim_E sim) e)).
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
  + intros e r.
    simpl.
    assert (Hthresh_if := sim_threshold_if sim (retraction sim.(sim_E) e) r).

    assert (Hsr := section_retraction Graph.Eeq_equiv sim.(sim_E)).
    assert (Loc.eq (if
                      Rle_dec r
                        (Graph.threshold (sim.(sim_E) (@retraction Graph.E Graph.Eeq sim.(sim_E) e)))
                     then Graph.src (sim.(sim_E) (@retraction Graph.E Graph.Eeq sim.(sim_E) e))
                      else Graph.tgt (sim.(sim_E) (@retraction Graph.E Graph.Eeq sim.(sim_E) e)))
                    (if Rle_dec r (Graph.threshold e)
                     then Graph.src e else Graph.tgt e)).
    {
      assert ((Graph.threshold (sim.(sim_E) (@retraction Graph.E Graph.Eeq sim.(sim_E) e))) =  (Graph.threshold e)).
      apply Graph.threshold_compat.
      apply (section_retraction Graph.Eeq_equiv).
      rewrite H; destruct (Rle_dec r (Graph.threshold e));
        try (apply Graph.src_compat);
        try (apply Graph.tgt_compat); f_equiv;
          apply (section_retraction Graph.Eeq_equiv).
    }
    rewrite H in Hthresh_if.
    apply (Inversion).
    now rewrite Hthresh_if.
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

