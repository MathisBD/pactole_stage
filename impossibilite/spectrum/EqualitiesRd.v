Require Import Reals.
Require Import Morphisms.
Require Import ConvergentFormalismRd.
Import Permutation.


Set Implicit Arguments.


(* ********************************************************* *)
(** *  General results about equality in the robot model **)
(* ******************************************************** *)


(** This module contains definitions and properties about the notions
    of equality we need for proofs. In particular it contains
    technical lemmas (introduced by <<Instance: Proper...>>) making
    these equality relations proper rewriting relations (i.e. that
    some constants are morphisms for these relations). *)

(* TODO: change the name: it is merely an equivalence *)
Class Bisimulation (T : Type) := {
  bisim : T -> T -> Prop;
  bisim_equiv : Equivalence bisim}.
Infix "≈" := bisim (at level 30).

(* We do not want this one because it will instantiate all bisim with Leibniz equality.
Instance equiv_bisim (T : Type) (R : T -> T -> Prop) `{eqR : Equivalence T R} : Bisimulation T := {
  bisim := R;
  bisim_equiv := eqR}.
*)

Module Equalities (Location : MetricSpace) (N : Size) (Spec : Spectrum(Location)(N)).

Module Import Formalism := ConvergentFormalism(Location)(N)(Spec).

(** **  Equality of positions  **)

(** ***  On good robots only  **)

Instance ExtEq_equiv T U : Equivalence (@ExtEq T U).
Proof. split.
+ now intros ? ?.
+ intros f g Heq x. now rewrite Heq.
+ intros f g h Hfg Hgh x. now rewrite Hfg, Hgh.
Qed.

Instance ExtEq_bisim T U : Bisimulation (T -> U).
Proof. exists (@ExtEq T U). apply ExtEq_equiv. Qed.

(** ***  On full positions  **)

Instance pos_eq_equiv : Equivalence PosEq.
Proof. split.
+ intros pos x. reflexivity.
+ intros d1 d2 H r. symmetry. apply H.
+ intros d1 d2 d3 H12 H23 x. transitivity (d2 x); auto.
Qed.

Instance poseq_bisim : Bisimulation position.
Proof. exists PosEq. apply pos_eq_equiv. Defined.

Instance map_pos_compat : Proper ((Location.eq ==> Location.eq) ==> PosEq ==> PosEq) map_pos.
Proof. intros f g Hfg ? ? Hpos id. unfold map_pos. apply Hfg, Hpos. Qed.

(** ***  On spectra  **)
(*
Definition spec_eq (s1 s2 : spectrum) := Permutation s1 s2.

Instance spec_eq_equiv : Equivalence spec_eq.
Proof. apply Permutation_Equivalence. Qed.

Instance spec_eq_bisim : nBisimulation spectrum.
Proof. exists spec_eq. exact spec_eq_equiv. Qed.
*)
Instance fin_map_compat n X : Proper ((Logic.eq ==> Logic.eq) ==> Logic.eq) (@Names.fin_map n X).
Proof.
intros f g Hfg. induction n.
  reflexivity.
  simpl. f_equiv. now apply Hfg.
  apply IHn. now repeat intro; subst; apply Hfg.
Qed.

(** **  Equality of demons  **)

(** ***  Equality of demonic_actions  **)

Instance bij_eq_equiv : Equivalence bij_eq.
Proof. split.
+ intros f x y Hxy. apply section_exteq. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

Instance retraction_compat : Proper (bij_eq ==> (Location.eq ==> Location.eq)) (@retraction _ _ Location.eq_equiv).
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

Instance phase_eq_equiv : Equivalence phase_eq.
Proof. split.
+ intros [| obs]; repeat intro. reflexivity. apply (Hobs _ _ H). assumption.
+ intros [| obs1] [| obs2]; auto. intros Hobs2 Heq; repeat intro. symmetry. apply Heq; symmetry; assumption.
+ intros [| obs1] [| obs2] [| obs3] Heq1 Heq2; simpl in *; intuition. intros x y Hxy.
  rewrite (Heq1 _ _ (reflexivity x)). apply Heq2. assumption.
Qed.

(* TODO: Should we put the tests on good robots only or all robots? *)
Definition da_eq (da1 da2 : demonic_action) :=
  (forall r : Names.ident, phase_eq (da1.(step) r) (da2.(step) r)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)) /\
  (forall g, (PosEq ==> Spec.eq)%signature (da1.(spectrum_of) g) (da2.(spectrum_of) g)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. apply (spectrum_exteq _ _ g eq_refl).
+ intros d1 d2 [H1 [H2 H3]]. repeat split; intros; symmetry; auto.
+ intros d1 d2 d3 [H1 [H2 H3]] [H4 [H5 H6]]. repeat split; intros; etransitivity; eauto.
Qed.

Instance step_compat : Proper (da_eq ==> eq ==> phase_eq) step.
Proof. intros [] [] [Hd1 Hd2] p1 p2 Hp. subst. simpl in *. apply (Hd1 p2). Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 [H2 H3]]. simpl in *. apply (H2 p2). Qed.

Instance spectrum_of_compat : Proper (da_eq ==> Logic.eq ==> PosEq ==> Spec.eq) spectrum_of. 
Proof.
intros [? ? da1 ?] [? ? da2 ?] [Hda1 [Hda2 Hda3]] g1 g2 Hg p1 p2 Hp. simpl in *. subst. apply Hda3. assumption.
Qed.

(** ***  Equality of demons  **)

CoInductive deq (d1 d2 : demon) : Prop :=
  | Cdeq : da_eq (demon_head d1) (demon_head d2) -> deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. split.
+ coinduction deq_refl. reflexivity.
+ coinduction deq_sym. symmetry. now inversion H. now inversion H.
+ coinduction deq_trans.
  - inversion H. inversion H0. now transitivity (demon_head y).
  - apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
      now inversion H.
      now inversion H0.
Qed.

Instance deq_bisim : Bisimulation demon.
Proof. exists deq. apply deq_equiv. Qed.

(** **  Equality of robograms  **)

Definition req (r1 r2 : robogram) := (Spec.eq ==> Location.eq)%signature r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
+ intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
+ intros r1 r2 r3 H1 H2 x y Heq.
  rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
Qed.

Instance round_compat : Proper (req ==> da_eq ==> PosEq ==> PosEq) round.
Proof.
intros r1 r2 Hr da1 da2 Hd pos1 pos2 Hpos id.
unfold req in Hr. unfold round. simpl in *.
assert (Hstep := step_compat Hd (reflexivity id)). assert (Hda1 := da1.(step_exteq) _ _ (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try now elim Hstep.
+ simpl in Hstep. f_equiv.
  - intros x y Hxy. rewrite Hobs; eassumption || trivial. apply Hstep; reflexivity.
  - apply Hr. apply spectrum_of_compat, map_pos_compat; trivial. apply Hstep, Hpos.
+ rewrite Hd. reflexivity.
Qed.


(** **  Equality of execution  **)

CoInductive eeq (e1 e2 : execution) : Prop :=
  | Ceeq : PosEq (execution_head e1) (execution_head e2) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. split.
+ coinduction eeq_refl. reflexivity.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. intro.
  - inversion H. inversion H0. now transitivity (execution_head y id).
  - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
    now inversion H. now inversion H0.
Qed.

Instance eeq_bisim : Bisimulation execution.
Proof. exists eeq. apply eeq_equiv. Qed.


Instance execution_head_compat : Proper (eeq ==> PosEq) execution_head.
Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.

Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
Proof. intros e1 e2 He. now inversion He. Qed.

Theorem execute_compat : Proper (req ==> deq ==> PosEq ==> eeq) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. assumption.
apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.

End Equalities.
