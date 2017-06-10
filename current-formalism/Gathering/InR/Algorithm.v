(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega.
Require Import Rbase Rbasic_fun.
Require Import List SetoidList.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.R.
Require Import Pactole.Gathering.Definitions.
Import Permutation.


Set Implicit Arguments.
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").


Lemma similarity_middle : forall (sim : similarity R) x y, (sim ((x + y) / 2) = (sim x + sim y) / 2)%R.
Proof.
intros sim x y. destruct (similarity_in_R_case sim) as [Hsim | Hsim];
repeat rewrite Hsim; cbn in *; field.
Qed.
Close Scope R_scope.


(* We assume that we have at least two robots. *)
Parameter n : nat.
Axiom size_G : n >= 2.

Instance MyRobotsDef : NamesDef := RobotsDef n 0.
Instance MyRobots : Names := Robots n 0.

(* BUG?: To help finding correct instances, loops otherwise! *)
Existing Instance R_Setoid.
Existing Instance R_EqDec.
Existing Instance R_RMS.


(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall config, ~!! config == empty.
Proof. apply spect_non_nil. apply size_G. Qed.

Corollary sort_non_nil : forall config, sort (support (!! config)) <> nil.
Proof.
intros config Habs. apply (spect_non_nil config).
setoid_rewrite <- support_nil.
apply Permutation_nil. setoid_rewrite Permuted_sort at 2. rewrite Habs. reflexivity.
Qed.

Lemma half_size_config : Nat.div2 nG > 0.
Proof. assert (Heven := size_G). simpl. destruct n as [| [| n]]; simpl; omega. Qed.

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall config l, (!! config)[l] = countA_occ _ equiv_dec l (config_list config)
 := spect_from_config_spec.

(** **  Property expressing the existence of a majority tower  **)

Definition MajTower_at x conf :=
  forall y, y <> x -> ((!! conf)[y] < (!! conf)[x]).

Instance MajTower_at_compat : Proper (Logic.eq ==> equiv ==> iff) MajTower_at.
Proof. intros ? ? ? ? ? Hconf. subst. unfold MajTower_at. now setoid_rewrite Hconf. Qed.

(** Computationally, it is equivalent to having only one tower with maximum multiplicity. *)

(** ***  The maximum multiplicity of a multiset  **)

Lemma max_mult_similarity_invariant : forall (sim : similarity R) s, max_mult (map sim s) = max_mult s.
Proof.
intros. apply max_mult_map_injective_invariant.
- intros ? ? Heq. now rewrite Heq.
- apply injective.
Qed.

Corollary max_similarity : forall (sim : similarity R),
  forall s, max (map sim s) == map sim (max s).
Proof.
intros. apply max_map_injective.
- intros ? ? Heq. now rewrite Heq.
- apply injective.
Qed.

Lemma support_max_non_nil : forall config, support (max (!! config)) <> nil.
Proof. intros config Habs. rewrite support_nil, max_empty in Habs. apply (spect_non_nil _ Habs). Qed.

(** ***  Computational equivalent of having a majority tower  **)

Lemma Majority_MajTower_at : forall config pt,
  support (max (!! config)) = pt :: nil -> MajTower_at pt config.
Proof.
intros config pt Hmaj x Hx. apply max_spec2.
- rewrite <- support_In, Hmaj. now left.
- rewrite <- support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

Theorem MajTower_at_equiv : forall config pt, MajTower_at pt config <->
  support (max (!! config)) = pt :: nil.
Proof.
intros config pt. split; intro Hmaj.
* apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz. change eq with equiv.
  apply (NoDupA_equivlistA_PermutationA _).
  + apply NoDupA_singleton.
  + apply support_NoDupA.
  + intro y. rewrite InA_singleton.
    rewrite support_In, max_spec1_iff; try apply spect_non_nil; [].
    split; intro Hpt.
    - rewrite Hpt. intro x. destruct (Rdec x pt).
      -- subst x. reflexivity.
      -- apply lt_le_weak. now apply (Hmaj x).
    - destruct (Rdec y pt) as [? | Hy]; trivial.
      exfalso. apply (Hmaj y) in Hy. specialize (Hpt pt). omega.
* intros x Hx. apply max_spec2.
  - rewrite <- support_In, Hmaj. now left.
  - rewrite <- support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

(** **  Some properties of [forbidden]  **)

Lemma forbidden_even : forall conf, forbidden conf -> Nat.Even nG.
Proof. now intros conf [? _]. Qed.

Lemma forbidden_support_length : forall config, forbidden config ->
  size (!! config) = 2.
Proof.
intros config [Heven [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
rewrite <- (@cardinal_total_sub_eq _ _ _ _ _ (add pt2 (Nat.div2 nG) (singleton pt1 (Nat.div2 nG)))).
+ rewrite size_add; try (now apply half_size_config); [].
  destruct (In_dec pt2 (singleton pt1 (Nat.div2 nG))) as [Hin | Hin].
  - exfalso. rewrite In_singleton in Hin.
    destruct Hin. now elim Hdiff.
  - rewrite size_singleton; trivial. apply half_size_config.
+ intro pt. destruct (Rdec pt pt2), (Rdec pt pt1); subst.
  - now elim Hdiff.
  - rewrite add_spec, singleton_spec.
    unfold equiv_dec,R_EqDec in *. do 2 Rdec_full; contradiction || omega.
  - rewrite add_other, singleton_spec.
      now unfold equiv_dec, R_EqDec in *; Rdec_full; contradiction || omega.
      now unfold equiv_dec, R_EqDec; auto.
  - rewrite add_other, singleton_spec.
      now unfold equiv_dec, R_EqDec in *; Rdec_full; contradiction || omega.
      now unfold equiv; auto.
+ rewrite cardinal_add, cardinal_singleton, cardinal_spect_from_config.
  simpl. rewrite plus_0_r. now apply even_div2.
Qed.

Lemma forbidden_injective_invariant : forall f, Util.Preliminary.injective equiv equiv f ->
  forall config, forbidden config -> forbidden (map_config f config).
Proof.
unfold forbidden.
intros f Hf config [HnG [? [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
repeat split; trivial; [].
exists (f pt1), (f pt2). split.
- intro Heq. apply Hdiff. now apply Hf in Heq.
- split; rewrite <- spect_from_config_map, map_injective_spec;
  assumption || (now intros ? ? Heq; rewrite Heq) || apply Hf.
Qed.

Theorem forbidden_similarity_iff : forall (sim : similarity R) config,
  forbidden (map_config sim config) <-> forbidden config.
Proof.
intros sim config. split.
- setoid_rewrite <- (map_id config) at 2. change Datatypes.id with (section id).
  rewrite <- (compose_inverse_l sim). simpl.
  setoid_rewrite <- map_config_merge at 2; try now intros ? ? Heq; rewrite Heq.
  eapply forbidden_injective_invariant, injective_retraction, injective.
- apply forbidden_injective_invariant, injective.
Qed.

Lemma support_max_1_not_forbidden : forall config pt,
  MajTower_at pt config -> ~forbidden config.
Proof.
intros config pt Hmaj. rewrite MajTower_at_equiv in Hmaj.
assert (Hmax : forall x, In x (max (!! config)) <-> x = pt).
{ intro x. rewrite <- support_spec, Hmaj. split.
  - intro Hin. inversion_clear Hin. assumption. inversion H.
  - intro. subst x. now left. }
intro Hforbidden.
assert (Hsuplen := forbidden_support_length Hforbidden).
destruct Hforbidden as [Heven [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
assert (Hsup : Permutation (support (!! config)) (pt1 :: pt2 :: nil)).
{ assert (Hin1 : InA equiv pt1 (support (!! config))).
  { rewrite support_spec. unfold In. rewrite Hpt1. apply half_size_config. }
  assert (Hin2 : InA equiv pt2 (support (!! config))).
  { rewrite support_spec. unfold In. rewrite Hpt2. apply half_size_config. }
  apply (PermutationA_split _) in Hin1. destruct Hin1 as [l Hl]. rewrite Hl in Hin2.
  inversion_clear Hin2; try now subst; elim Hdiff.
  rewrite size_spec, Hl in Hsuplen. destruct l as [| x [| ? ?]]; simpl in Hsuplen; try omega.
  inversion_clear H; (now inversion H0) || (cbn in H0; subst). now rewrite <- PermutationA_Leibniz. }
assert (Hpt : pt = pt1 \/ pt = pt2).
{ assert (Hin : List.In pt (pt1 :: pt2 :: nil)).
  { rewrite <- Hsup, <- InA_Leibniz. change eq with equiv.
    rewrite support_spec, <- max_subset, <- support_spec, Hmaj. now left. }
  inversion_clear Hin; auto. inversion_clear H; auto. inversion H0. }
apply (lt_irrefl (Nat.div2 nG)). destruct Hpt; subst pt.
- rewrite <- Hpt1 at 2. rewrite <- Hpt2. apply max_spec2; try now rewrite Hmax.
  rewrite Hmax. auto.
- rewrite <- Hpt1 at 1. rewrite <- Hpt2. apply max_spec2; now rewrite Hmax.
Qed.

Definition no_Majority config := (size (max (!! config)) > 1)%nat.

(* forbidden_support_length already proves the <- direction *)
Lemma forbidden_equiv : forall config,
  forbidden config <-> no_Majority config /\ size (!! config) = 2%nat.
Proof.
  intro config. unfold no_Majority. split.
  - intro Hforbidden. split.
    + rewrite size_spec. destruct (support (max (!! config))) as [| pt1 [| pt2 l]] eqn:Hmax.
      * exfalso. revert Hmax. apply support_max_non_nil.
      * exfalso. revert Hmax Hforbidden. rewrite <- MajTower_at_equiv. apply support_max_1_not_forbidden.
      * simpl. omega.
    + now apply forbidden_support_length.
  - intros [Hlen H2]. rewrite size_spec in *.
    destruct (support (!! config)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try (now simpl in H2; omega); [].
    red.
    assert (Hlen':(size (max (!! config)) = 2)%nat).
    { assert (size (max (!! config)) <= 2)%nat.
      { unfold max.
        rewrite <- H2, <- Hsupp, <- size_spec.
        apply size_nfilter.
        now repeat intro; subst. }
      rewrite <- size_spec in Hlen. omega. }
    clear Hlen.
    (* let us reformulate this in a more convenient way *)
   cut (exists pt0 pt3 : elt,
      pt0 <> pt3 /\
      (!! config)[pt0] = Nat.div2 N.nG /\ (!! config)[pt3] = Nat.div2 N.nG /\ Nat.Even N.nG).
   { intros h.
     decompose [ex and] h; repeat split; try (assumption || apply size_G); [].
     exists x, x0; intuition. }
   exists pt1, pt2.
   split.
    * assert (hnodup:NoDupA R.eq (pt1 :: pt2 :: nil)). {
        rewrite <- Hsupp.
        apply support_NoDupA. }
      intro abs.
      subst.
      inversion hnodup;subst.
      elim H1.
      constructor.
      reflexivity.
    * assert (h:=@support_nfilter _ (eqb_max_mult_compat (!!config)) (!! config)).
      change (nfilter (fun _ : elt => Nat.eqb (max_mult (!! config))) (!! config))
      with (max (!!config)) in h.
      assert (Hlen'': length (support (!! config)) <= length (support (max (!! config)))).
      { rewrite size_spec in Hlen'. rewrite Hsupp, Hlen'. reflexivity. }
      assert (h2:=@NoDupA_inclA_length_PermutationA
                    _ R.eq _
                    (support (max (!! config)))
                    (support (!! config))
                    (support_NoDupA _)
                    (support_NoDupA _)
                    h Hlen'').
      assert (toto:=@cardinal_from_config config).
      unfold N.nB in toto.
      rewrite <- plus_n_O in toto.
      assert (~ R.eq pt1 pt2). {
        intro abs.
        repeat red in abs.
        rewrite abs in Hsupp.
        assert (hnodup:=support_NoDupA (!! config)).
        rewrite  Hsupp in hnodup.
        inversion hnodup;subst.
        match goal with
        | H: ~ InA R.eq pt2 (pt2 :: nil) |- _ => elim H
        end.
        constructor 1.
        reflexivity. }
      assert (heq_config:eq (!!config)
                               (add pt1 ((!! config)[pt1])
                                         (add pt2 ((!! config)[pt2]) empty))).
      { red.
        intros x.
        destruct (R.eq_dec x pt1) as [heqxpt1 | hneqxpt1].
        - rewrite heqxpt1.
          rewrite add_same.
          rewrite (add_other pt2 pt1).
          + rewrite empty_spec.
            omega.
          + assumption.
        - rewrite add_other;auto.
          destruct (R.eq_dec x pt2) as [heqxpt2 | hneqxpt2].
          + rewrite heqxpt2.
            rewrite add_same.
            rewrite empty_spec.
            omega.
          + rewrite add_other;auto.
            rewrite empty_spec.
            rewrite <- not_In.
            rewrite <- support_spec.
            rewrite Hsupp.
            intro abs.
            inversion abs;try contradiction;subst.
            inversion H1;try contradiction;subst.
            rewrite InA_nil in H3.
            assumption. }
      rewrite heq_config in toto.
      rewrite cardinal_fold_elements in toto.
      assert (fold_left (fun (acc : nat) (xn : elt * nat) => snd xn + acc)
                        ((pt1, (!! config)[pt1])
                           :: (pt2, (!! config)[pt2])
                           :: nil) 0
              = N.nG).
      { rewrite <- toto.
        eapply MMultiset.Preliminary.fold_left_symmetry_PermutationA with (eqA := eq_pair);auto.
        - apply eq_pair_equiv.
        - apply eq_equivalence.
        - repeat intro;subst.
          rewrite H1.
          reflexivity.
        - intros x y z. omega.
        - symmetry.
          transitivity ((pt1, (!! config)[pt1]) :: (elements (add pt2 (!! config)[pt2] empty))).
          eapply elements_add_out;auto.
          + rewrite heq_config, add_same. cut ((!! config)[pt1] > 0). omega.
            change (In pt1 (!! config)). rewrite <- support_In, Hsupp. now left.
          + rewrite add_empty.
            rewrite In_singleton.
            intros [abs _].
            contradiction.
          + apply permA_skip.
            * reflexivity.
            * transitivity ((pt2, (!! config)[pt2]) :: elements empty).
              eapply elements_add_out;auto.
              -- change (In pt2 (!! config)). rewrite <- support_In, Hsupp. now right; left.
              -- apply In_empty.
              -- now rewrite elements_empty. }
      simpl in H0.
      rewrite <- plus_n_O in H0.

      assert ((!! config)[pt2] = (!! config)[pt1]).
      { assert (hfilter:= @nfilter_In _ (eqb_max_mult_compat (!! config))).
        transitivity (max_mult (!! config)).
        + specialize (hfilter pt2 (!!config)).
          replace (nfilter (fun _ : elt => Nat.eqb (max_mult (!! config))) (!!config))
          with (max (!!config)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 2; constructor 1.
               reflexivity.
            -- symmetry.
               rewrite <- Nat.eqb_eq.
               assumption.
          * trivial.
        + specialize (hfilter pt1 (!!config)).
          replace (nfilter (fun _ : elt => Nat.eqb (max_mult (!! config))) (!!config))
          with (max (!!config)) in hfilter.
          * destruct hfilter as [hfilter1 hfilter2].
            destruct hfilter1.
            -- apply support_In.
               rewrite h2.
               rewrite Hsupp.
               constructor 1.
               reflexivity.
            -- rewrite <- Nat.eqb_eq.
               assumption.
          * trivial. }
      rewrite H1 in *|-*.
      assert ( 0 + 2 *(!! config)[pt1] = N.nG).
      { omega. }
      assert (Nat.even N.nG).
      { rewrite <- H3.
        rewrite (Nat.even_add_mul_2 0 ((!! config)[pt1])).
        apply Nat.even_0. }
      split;[| split].
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl  Nat.b2n in H3.
         repeat rewrite <- plus_n_O,plus_O_n in H3.
         omega.
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl  Nat.b2n in H3.
         repeat rewrite <- plus_n_O,plus_O_n in H3.
         omega.
      -- apply Even.even_equiv.
         apply Even.even_equiv.
         apply Nat.even_spec.
         assumption.
Qed.

Lemma not_forbidden_not_majority_length : forall config,
  no_Majority config -> ~forbidden config -> (size (!! config) >= 3)%nat.
Proof.
intros config H1 H2.
assert (size (!! config) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption.
  do 2 rewrite size_spec. apply (NoDupA_inclA_length _).
  - apply support_NoDupA.
  - unfold max. apply support_nfilter. repeat intro. now subst. }
 destruct (size (!! config)) as [| [| [| ?]]] eqn:Hlen; try omega.
exfalso. apply H2. now rewrite forbidden_equiv.
Qed.

(** **  Functions for the generic case  **)

Open Scope R_scope.

Definition mini s := List.hd 0 (sort (support s)).
Definition maxi s := List.last (sort (support s)) 0.
Definition middle s := nth 1 (sort (support s)) 0.

Instance mini_compat : Proper (equiv ==> eq) mini.
Proof. intros s1 s2 Hs. unfold mini. now rewrite Hs. Qed.

Instance maxi_compat : Proper (equiv ==> eq) maxi.
Proof. intros s1 s2 Hs. unfold maxi. now rewrite Hs. Qed.

Instance middle_compat : Proper (equiv ==> eq) middle.
Proof. intros s1 s2 Hs. unfold middle. now rewrite Hs. Qed.

Definition is_extremal r s :=
  if Rdec r (mini s) then true else
  if Rdec r (maxi s) then true else false.

Instance is_extremal_compat : Proper (equiv ==> equiv ==> eq) is_extremal.
Proof.
intros x y Hxy s s' Hs. rewrite <- Hxy. unfold is_extremal, mini, maxi.
destruct (Rdec x (hd 0 (sort (support s)))), (Rdec x (hd 0 (sort (support s'))));
try rewrite Hs in *; contradiction || trivial; [].
destruct (Rdec x (last (sort (support s)) 0)), (Rdec x (last (sort (support s')) 0));
try rewrite Hs in *; contradiction || reflexivity.
Qed.

Lemma is_extremal_map_monotonic_invariant : forall f,
  monotonic Rleb Rleb f -> Util.Preliminary.injective eq eq f ->
  forall x config, is_extremal (f x) (map f (!! config)) = is_extremal x (!! config).
Proof.
intros f Hfmon Hfinj x config. unfold is_extremal, mini, maxi.
assert (Hf : Proper (equiv ==> equiv) f). { repeat intro. cbn in *. now subst. }
destruct Hfmon as [Hfinc | Hfdec].
* repeat Rdec_full; trivial;
  rewrite map_injective_support, (sort_map_increasing Hfinc) in Heq
  || rewrite map_injective_support, (sort_map_increasing Hfinc) in Hneq;
  try rewrite map_injective_support, (sort_map_increasing Hfinc) in Heq0
  || rewrite map_injective_support, (sort_map_increasing Hfinc) in Hneq0;
  trivial.
  + rewrite (hd_indep _ (f 0)) in Heq.
    - rewrite map_hd in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Heq.
    - rewrite map_last in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (hd_indep _ (f 0)) in Hneq.
    - elim Hneq. rewrite map_hd. now f_equal.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Hneq0.
    - elim Hneq0. rewrite map_last. now f_equal.
    - intro Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
* repeat Rdec_full; trivial;
  rewrite map_injective_support, (sort_map_decreasing Hfdec) in Heq
  || rewrite map_injective_support, (sort_map_decreasing Hfdec) in Hneq;
  try rewrite map_injective_support, (sort_map_decreasing Hfdec) in Heq0
  || rewrite map_injective_support, (sort_map_decreasing Hfdec) in Hneq0;
  trivial.
  + rewrite (hd_indep _ (f 0)) in Heq.
    - rewrite hd_rev_last, map_last in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Heq.
    - rewrite last_rev_hd, map_hd in Heq. apply Hfinj in Heq. contradiction.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (last_indep _ (f 0)) in Hneq0.
    - elim Hneq0. rewrite last_rev_hd, map_hd. now f_equal.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
  + rewrite (hd_indep _ (f 0)) in Hneq.
    - elim Hneq. rewrite hd_rev_last, map_last. now f_equal.
    - intro Habs. rewrite rev_nil in Habs. apply map_eq_nil in Habs. now apply (sort_non_nil config).
Qed.

Corollary is_extremal_similarity_invariant : forall (sim : similarity R) config r,
  is_extremal (sim r) (map sim (!! config)) = is_extremal r (!! config).
Proof.
intros sim conf r. apply is_extremal_map_monotonic_invariant.
- apply similarity_monotonic.
- change eq with equiv. apply injective.
Qed.

(* When there is no robot (s is empty), the center is 0. *)
Definition extreme_center (s : spectrum) := (mini s + maxi s) / 2.

Instance extreme_center_compat : Proper (equiv ==> eq) extreme_center.
Proof. intros s s' Hs. unfold extreme_center, mini, maxi. now rewrite Hs. Qed.

Lemma extreme_center_similarity : forall (sim : similarity R) s, s =/= empty ->
  extreme_center (map sim s) = sim (extreme_center s).
Proof.
intros sim s Hs.
assert (Hsim1 : Proper (equiv ==> equiv) sim). { intros x y Hxy. now rewrite Hxy. }
assert (Hsim2 := injective sim).
unfold extreme_center, mini, maxi.
destruct (similarity_monotonic sim) as [Hinc | Hdec].
* rewrite map_injective_support, (sort_map_increasing Hinc); trivial.
  assert (Hperm := Permuted_sort (support s)). destruct (sort (support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. symmetry. now apply similarity_middle.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
* rewrite map_injective_support, (sort_map_decreasing Hdec); trivial.
  rewrite last_rev_hd, hd_rev_last.
  assert (Hperm := Permuted_sort (support s)). destruct (sort (support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. rewrite similarity_middle. field.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
Qed.

Lemma extreme_center_similarity_invariant : forall (sim : similarity R) config,
  extreme_center (map sim (!! config)) = sim (extreme_center (!! config)).
Proof. intros. apply extreme_center_similarity. apply spect_non_nil. Qed.


(** *  The robogram solving the gathering **)

(** I works as follows:
    1) if there is a majority stack, everyone goes there;
    2) if there are three stacks, everyone goes on the middle one;
    3) otherwise, robots located at non extremal locations go to the middle of the extremal locations.
    The last case will necessarily end into one of the first two, ensuring termination.
**)


Definition gatherR_pgm (s : spectrum) : R :=
  match support (max s) with
    | nil => 0 (* only happen with no robots *)
    | pt :: nil => pt (* case 1: one majority stack *)
    | _ => (* several majority stacks *)
           if beq_nat (size s) 3
           then middle s else
           if is_extremal 0 s then 0 else extreme_center s
  end.

(** The robogram is invariant by permutation of spectra. *)
Instance gatherR_pgm_compat : Proper (equiv ==> eq) gatherR_pgm.
Proof.
unfold gatherR_pgm. intros s s' Hs. assert (Hperm := support_compat (max_compat Hs)).
destruct (support (max s)) as [| pt [| pt2 l]].
+ now rewrite (PermutationA_nil _ Hperm).
+ symmetry in Hperm. destruct (PermutationA_length1 _ Hperm) as [pt' [Heq Hin]]. now rewrite Hin.
+ assert (Hlength := PermutationA_length Hperm).
  destruct (support (max s')) as [| pt' [| pt2' l']]; try discriminate. rewrite Hs.
  destruct (size s' =? 3); rewrite Hs; try reflexivity; [].
  simpl. destruct (is_extremal 0 s'); try rewrite Hs; reflexivity.
Qed.

Definition gatherR := Build_robogram _.


(** **  General simplification lemmas for [round gatherR da _] **)

Lemma round_simplify : forall da config,
  round gatherR da config
  == fun id => match da.(step) id with
                 | None => config id
                 | Some f =>
                     let s := !! config in
                     match support (max s) with
                       | nil => config id (* only happen with no robots *)
                       | pt :: nil => pt (* case 1: one majority stack *)
                       | _ => (* several majority stacks *)
                              if beq_nat (size s) 3
                              then List.nth 1 (sort (support s)) 0 else
                              if is_extremal (config id) s then (config id) else extreme_center s
                     end
               end.
Proof.
intros da config id. unfold round.
destruct (step da id) as [simc |] eqn:Hstep, id as [g | b]; try reflexivity || now eapply Fin.case0; exact b.
remember (config (Good g)) as pt.
(* Simplify the similarity *)
assert (Hratio : (simc pt).(zoom) <> 0). { eapply da.(step_zoom). eassumption. }
destruct (similarity_in_R (simc pt)) as [k [Hk Hsim]].
assert (Hinvsim : forall x, (simc pt ⁻¹) x = x / k + center (simc pt)).
{ apply inverse_similarity_in_R; trivial. destruct Hk; subst; now try apply Ropp_neq_0_compat. }
rewrite Hinvsim.
assert(Hsimccompat : Proper (equiv ==> equiv) (simc pt)). { intros ? ? Heq. now rewrite Heq. }
assert (Hsim_inj2 := injective (simc pt)).
(* Unfold the robogram *)
unfold gatherR, gatherR_pgm.
assert (Hperm : PermutationA equiv (support (max (!! (map_config (simc pt) config))))
                                   (List.map (simc pt) (support (max (!! config))))).
{ rewrite <- map_injective_support; trivial. f_equiv.
  rewrite <- max_similarity, spect_from_config_map; auto. }
destruct (support (max (!! config))) as [| pt' [| pt2' l']].
* (* Empty support *)
  simpl in Hperm. symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm.
  rewrite da.(step_center); try eassumption. hnf. field. destruct Hk; subst; now try apply Ropp_neq_0_compat.
* (* A majority stack *)
  simpl in Hperm. apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]]. rewrite Hperm.
  hnf in Hy |- *. subst y. rewrite Hsim. field. destruct Hk; subst; now try apply Ropp_neq_0_compat.
* (* No majority stack *)
  apply PermutationA_length in Hperm.
  destruct (support (max (!! (Config.map (simc pt) conf)))) as [| pt'' [| pt2'' l'']];
  try discriminate Hperm. clear Hperm pt' pt2' l' pt'' pt2'' l''.
  assert (Hlength : size (!! (Config.map (simc pt) conf)) = size (!! conf)).
  { rewrite <- from_config_map; trivial. now apply map_injective_size. }
  rewrite Hlength. destruct (size (!! conf) =? 3) eqn:Hlen.
  + (* There are three towers *)
    unfold middle. rewrite <- from_config_map, map_injective_support; trivial.
    rewrite size_spec in Hlen.
    destruct (support (!! conf)) as [| pt1 [| pt2 [| pt3 [| ? ?]]]]; try discriminate Hlen.
    destruct (similarity_monotonic (simc pt)) as [Hinc | Hdec].
    - rewrite (sort_map_increasing Hinc), (nth_indep _ 0 (simc pt 0)), map_nth, <- Hinvsim.
      simpl. rewrite <- (simc pt).(Similarity.Inversion); try reflexivity.
      rewrite map_length, <- Permuted_sort. simpl. omega.
    - { rewrite (sort_map_decreasing Hdec).
        assert (Heq1 : Nat.div2 (length (map (simc pt) (sort (pt1 :: pt2 :: pt3 :: nil)))) = 1%nat).
        { now rewrite map_length, <- Permuted_sort. }
        rewrite <- Heq1 at 1. rewrite odd_middle, (nth_indep _ 0 (simc pt 0)).
        + rewrite map_nth, <- Hinvsim. simpl. rewrite <- (simc pt).(Similarity.Inversion), <- Heq1; reflexivity.
        + rewrite map_length, <- Permuted_sort. simpl. omega.
        + rewrite map_length, <- Permuted_sort. simpl. exists 1%nat. omega. }
  + (* Generic case *)
    change 0 with R.origin. rewrite <- (simc pt).(Sim.center_prop) at 1.
    rewrite <- from_config_map, is_extremal_similarity_invariant, da.(step_center); try eassumption.
    destruct (is_extremal pt (!! conf)).
    - (* The current robot is exremal *)
      hnf. unfold R.origin, Rdef.origin. field. destruct Hk; subst; now try apply Ropp_neq_0_compat.
    - (* The current robot is not exremal *)
      rewrite <- from_config_map, extreme_center_similarity; apply spect_non_nil || trivial.
      hnf. rewrite <- (da.(step_center) _ pt Hstep) at 2.
      rewrite <- Hinvsim. simpl. now rewrite <- (simc pt).(Similarity.Inversion).
Qed.

(** ***  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, everyone goes there. **)
Lemma round_simplify_Majority : forall da config pt,
  MajTower_at pt config ->
  round gatherR da config == fun id => match step da id with
                                         | None => config id
                                         | Some _ => pt
                                       end.
Proof.
intros da config pt Hmaj id. rewrite round_simplify.
rewrite MajTower_at_equiv in Hmaj.
destruct (step da id); try reflexivity. cbv zeta.
destruct (support (max (!! config))) as [| ? [| ? ?]]; try discriminate Hmaj.
inversion Hmaj. reflexivity.
Qed.

(** If we have three towers, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall da config,
  no_Majority config ->
  (size (!! config) = 3)%nat ->
  round gatherR da config == fun id => match step da id with
                                         | None => config id
                                         | Some _ => nth 1 (sort (support (!! config))) 0
                                       end.
Proof.
intros da config Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in H3. rewrite H3. reflexivity.
Qed.

(** In the general case, all non extremal robots go to the middle of the extreme. *)
Lemma round_simplify_Generic : forall da config,
  no_Majority config ->
  (size (!! config) <> 3)%nat ->
  round gatherR da config == fun id => match step da id with
                                         | None => config id
                                         | Some _ => if is_extremal (config id) (!! config)
                                                     then config id else extreme_center (!! config)
                                       end.
Proof.
intros da config Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in H3. rewrite H3. reflexivity.
Qed.

Close Scope R_scope.


(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Majority_grow :  forall pt config da, MajTower_at pt config ->
  (!! config)[pt] <= (!! (round gatherR da config))[pt].
Proof.
intros pt config da Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id); unfold equiv_dec, R_EqDec.
  - Rdec. Rdec_full; apply le_n_S + apply le_S; apply IHl.
  - Rdec_full; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall pt pt' config da, pt <> pt' ->
  MajTower_at pt config -> (!! (round gatherR da config))[pt'] <= (!! config)[pt'].
Proof.
intros pt pt' config da Hdiff Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id); unfold equiv_dec, R_EqDec.
  - Rdec_full; try contradiction. Rdec_full; try apply le_S; apply IHl.
  - Rdec_full; try apply le_n_S; apply IHl.
Qed.

(** Whenever there is a majority stack, it remains forever so. **)
Theorem MajTower_at_forever : forall pt config da,
  MajTower_at pt config -> MajTower_at pt (round gatherR da config).
Proof.
intros pt config da Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! config)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
- eapply Majority_grow; eauto.
Qed.

Theorem Majority_not_forbidden : forall pt config, MajTower_at pt config -> ~forbidden config.
Proof.
intros pt config Hmaj. rewrite forbidden_equiv. unfold no_Majority. intros [Hmaj' _].
rewrite MajTower_at_equiv in Hmaj. rewrite size_spec, Hmaj in Hmaj'. simpl in *. omega.
Qed.

(** **  Properties in the generic case  **)

Open Scope R_scope.
(** If we have no majority stack (hence more than one stack), then the extreme locations are different. **)
Lemma Generic_min_max_lt_aux : forall l, (length l > 1)%nat -> NoDupA eq l ->
  hd 0 (sort l) < last (sort l) 0.
Proof.
intros l Hl Hnodup. rewrite Permuted_sort in Hl.
apply (@PermutationA_NoDupA _ eq _ l (sort l)) in Hnodup.
+ apply Rle_neq_lt.
  - apply sort_min. setoid_rewrite Permuted_sort at 3. apply last_In.
    destruct (sort l); discriminate || simpl in Hl; omega.
  - apply (hd_last_diff _); auto.
+ rewrite PermutationA_Leibniz. apply Permuted_sort.
Qed.

Lemma Generic_min_max_lt : forall config,
  no_Majority config -> mini (!! config) < maxi (!! config).
Proof.
intros config Hmaj. apply Generic_min_max_lt_aux.
+ apply lt_le_trans with (size (max (!! config))); trivial.
  rewrite size_spec. apply (NoDupA_inclA_length _).
  - apply support_NoDupA.
  - apply support_nfilter. repeat intro. now subst.
+ apply support_NoDupA.
Qed.

Corollary Generic_min_mid_lt : forall config,
  no_Majority config -> mini (!! config) < extreme_center (!! config).
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Corollary Generic_mid_max_lt : forall config,
  no_Majority config -> extreme_center (!! config) < maxi (!! config).
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Theorem Generic_min_same : forall da config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  mini (!! (round gatherR da config)) = mini (!! config).
Proof.
intros da config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hhdin := sort_non_nil config). apply (hd_In 0%R) in Hhdin.
rewrite <- Permuted_sort in Hhdin at 2.
rewrite <- InA_Leibniz in Hhdin. change eq with equiv in Hhdin.
rewrite support_In, spect_from_config_In in Hhdin.
destruct Hhdin as [id Hid].
(* Its position before and after are the same *)
assert (config id = round gatherR da config id).
{ rewrite round_simplify_Generic; trivial; [].
  destruct (step da id); trivial; [].
  unfold is_extremal. Rdec_full; try reflexivity; [].
  elim Hneq. rewrite Hid. apply hd_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_min.
  rewrite <- Hid, <- InA_Leibniz. change eq with equiv. rewrite support_In, H. apply pos_in_config.
* apply sort_min.
  rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply spect_from_config_In.
  exists id. apply min_sort.
  + rewrite H, <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
  + intros y Hy. rewrite <- InA_Leibniz in Hy. change eq with equiv in Hy.
    rewrite support_In, spect_from_config_In in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite round_simplify_Generic; trivial; [].
    destruct (step da id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_min. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
      -- apply sort_min. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
      -- apply Rlt_le. change (mini (!! config) < extreme_center (!! config)). now apply Generic_min_mid_lt.
    - apply sort_min. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
Qed.

Theorem Generic_max_same : forall da config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  maxi (!! (round gatherR da config)) = maxi (!! config).
Proof.
intros da config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hlastin := sort_non_nil config). apply (last_In 0%R) in Hlastin.
rewrite <- Permuted_sort in Hlastin at 2.
rewrite <- InA_Leibniz in Hlastin. change eq with equiv in Hlastin.
rewrite support_In, spect_from_config_In in Hlastin.
destruct Hlastin as [id Hid].
(* Its position before and after are the same *)
assert (config id = round gatherR da config id).
{ rewrite round_simplify_Generic; trivial; [].
  destruct (step da id); trivial; [].
  unfold is_extremal. repeat Rdec_full; try reflexivity; [].
  elim Hneq0. rewrite Hid. apply last_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_max.
  rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply spect_from_config_In.
  exists id. apply max_sort.
  + rewrite H, <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
  + intros y Hy. rewrite <- InA_Leibniz in Hy. change eq with equiv in Hy.
    rewrite support_In, spect_from_config_In in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite round_simplify_Generic; trivial; [].
    destruct (step da id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_max. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
      -- apply sort_max. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
      -- apply Rlt_le. change (extreme_center (!! config) < maxi (!! config)). now apply Generic_mid_max_lt.
    - apply sort_max. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
* apply sort_max.
  rewrite <- Hid, <- InA_Leibniz. change eq with equiv. rewrite support_In, H. apply pos_in_config.
Qed.


Corollary Generic_extreme_center_same : forall da config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  extreme_center (!! (round gatherR da config)) = extreme_center (!! config).
Proof.
intros da config Hmaj Hlen. unfold extreme_center.
now rewrite (Generic_min_same _ Hmaj Hlen), (Generic_max_same _ Hmaj Hlen).
Qed.

Theorem Generic_min_mult_same : forall da config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  (!! (round gatherR da config))[mini (!! config)] = (!! config)[mini (!! config)].
Proof.
intros da config Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (step da id); unfold equiv_dec, R_EqDec.
  + repeat Rdec_full.
    - f_equal. apply IHl.
    - destruct (is_extremal (config id) (!! config)); try contradiction; [].
      elim (Rlt_irrefl (mini (!! config))). rewrite <- Heq at 2. now apply Generic_min_mid_lt.
    - revert Hneq. rewrite Heq. unfold is_extremal. Rdec. intro Habs. now elim Habs.
    - apply IHl.
  + Rdec_full.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Theorem Generic_max_mult_same : forall da config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  (!! (round gatherR da config))[maxi (!! config)] = (!! config)[maxi (!! config)].
Proof. 
intros da config Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (step da id); unfold equiv_dec, R_EqDec.
  + repeat Rdec_full.
    - f_equal. apply IHl.
    - destruct (is_extremal (config id) (!! config)); try contradiction; [].
      elim (Rlt_irrefl (maxi (!! config))). rewrite <- Heq at 1. now apply Generic_mid_max_lt.
    - revert Hneq. rewrite Heq. unfold is_extremal. Rdec. Rdec_full; intro Habs; now elim Habs.
    - apply IHl.
  + Rdec_full.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Close Scope R_scope.

Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace nG with (nG + nB) by (simpl; omega).
rewrite <- (cardinal_spect_from_config config).
rewrite <- (add_remove_id pt1 (!! config) (reflexivity _)) at 4.
rewrite cardinal_add.
rewrite <- (add_remove_id pt2 (!! config) (reflexivity _)) at 6.
rewrite remove_add_comm, cardinal_add; trivial.
rewrite <- (add_remove_id pt3 (!! config) (reflexivity _)) at 8.
rewrite remove_add_comm, remove_add_comm, cardinal_add; trivial.
omega.
Qed.

Theorem same_destination : forall da config id1 id2,
  List.In id1 (moving gatherR da config) -> List.In id2 (moving gatherR da config) ->
  round gatherR da config id1 = round gatherR da config id2.
Proof.
intros da config id1 id2 Hid1 Hid2. do 2 rewrite round_simplify.
destruct (step da id1) eqn:Hmove1; [destruct (step da id2) eqn:Hmove2 |].
* (* the real case *)
  cbv zeta.
  destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
  + (* no robots *)
    rewrite support_nil, max_empty in Hmaj. elim (spect_non_nil _ Hmaj).
  + (* a majority tower *)
    reflexivity.
  + destruct (size (!! config) =? 3) eqn:Hlen.
    - (* three towers *)
      reflexivity.
    - { (* generic case *)
        rewrite Nat.eqb_neq in Hlen. rename Hmaj into Hmaj'.
        assert (Hmaj : no_Majority  config).
        { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. omega. } clear Hmaj'.
        destruct (is_extremal (config id1) (!! config)) eqn:Hextreme1.
        + exfalso. unfold moving in Hid1. rewrite filter_In in Hid1. destruct Hid1 as [_ Hid1].
          destruct (R.eq_dec (round gatherR da config id1) (config id1)) as [_ | Hneq]; try discriminate.
          apply Hneq. rewrite round_simplify_Generic; trivial.
          destruct (step da id1); try reflexivity. now rewrite Hextreme1.
        + destruct (is_extremal (config id2) (!! config)) eqn:Hextreme2.
          - exfalso. unfold moving in Hid2. rewrite filter_In in Hid2. destruct Hid2 as [_ Hid2].
            destruct (R.eq_dec (round gatherR da config id2) (config id2)) as [_ | Hneq]; try discriminate.
            apply Hneq. rewrite round_simplify_Generic; trivial.
            destruct (step da id2); try reflexivity. now rewrite Hextreme2.
          - reflexivity. }
* apply moving_active in Hid2. unfold active in Hid2.
  rewrite filter_In, Hmove2 in Hid2. destruct Hid2; discriminate.
* apply moving_active in Hid1. unfold active in Hid1.
  rewrite filter_In, Hmove1 in Hid1. destruct Hid1; discriminate.
Qed.

Lemma towers_elements_3 : forall config pt1 pt2,
  (size (!! config) >= 3)%nat ->
  In pt1 (!! config) -> In pt2 (!! config) -> pt1 <> pt2 ->
  exists pt3, pt1 <> pt3 /\ pt2 <> pt3 /\ In pt3 (!! config).
Proof.
intros config pt1 pt2 Hlen Hpt1 Hpt2 Hdiff12.
rewrite <- support_In in Hpt1, Hpt2. rewrite size_spec in Hlen.
apply (PermutationA_split _) in Hpt1. destruct Hpt1 as [supp1 Hperm].
rewrite Hperm in Hpt2. inversion_clear Hpt2; try (now elim Hdiff12); []. rename H into Hpt2.
apply (PermutationA_split _) in Hpt2. destruct Hpt2 as [supp2 Hperm2].
rewrite Hperm2 in Hperm. rewrite Hperm in Hlen.
destruct supp2 as [| pt3 supp]; try (now simpl in Hlen; omega); [].
exists pt3.
rewrite <- support_In. assert (Hnodup := support_NoDupA (!! config)).
rewrite Hperm in *. inversion_clear Hnodup. inversion_clear H0. repeat split.
- intro Habs. subst. apply H. now right; left.
- intro Habs. subst. apply H1. now left.
- now right; right; left.
Qed.

(** Generic result of robograms using multiset spectra. *)
Lemma increase_move :
  forall r config da pt,
    ((!! config)[pt] < (!! (round r da config))[pt])%nat ->
    exists id, round r da config id == pt /\ round r da config id =/= config id.
Proof.
  intros r config da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (Rdec_bool ((round r da config x))  pt)
                             (negb (Rdec_bool (config x) pt)))) names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id.
    rewrite andb_true_iff, negb_true_iff, Rdec_bool_true_iff, Rdec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; split; try intro; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, round r da config id <> pt \/ config id = pt).
    { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- Rdec_bool_false_iff, <- Rdec_bool_true_iff. apply Hex, In_names. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt.
    do 2 rewrite spect_from_config_spec, config_list_spec.
    induction names as [| id l]; simpl; trivial.
    unfold equiv_dec, equiv, R_EqDec in *. simpl in *.
    do 2 Rdec_full; try omega. specialize (Hg id). intuition.
Qed.

(* Because of same_destination, we can strengthen the previous result as a equivalence. *)
Lemma increase_move_iff :
  forall config da pt,
    ((!! config)[pt] < (!! (round gatherR da config))[pt])%nat <->
    exists id, round gatherR da config id = pt /\ round gatherR da config id <> config id.
Proof.
intros config da pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', List.In id' (moving gatherR da config) -> round gatherR da config id' = pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; rewrite moving_spec; auto. }
  assert (Hstay : forall id, config id = pt -> round gatherR da config id = pt).
  { intros id' Hid'. destruct (Rdec (round gatherR da config id') pt) as [Heq | Heq]; trivial.
    assert (Habs := Heq). rewrite <- Hid' in Habs.
    change (round gatherR da config id' =/= config id') in Habs.
    rewrite <- moving_spec in Habs. apply Hdest in Habs. contradiction. }
  do 2 rewrite spect_from_config_spec, config_list_spec.
  assert (Hin : List.In id names) by apply In_names.
  induction names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. unfold equiv_dec, equiv, R_EqDec in *. Rdec_full.
    - rewrite <- Hid in Heq. now elim Hroundid.
    - Rdec_full; try contradiction; []. apply le_n_S. induction l; simpl.
      -- reflexivity.
      -- repeat Rdec_full; try now idtac + apply le_n_S + apply le_S; apply IHl.
         elim Hneq0. now apply Hstay.
  + apply IHl in H. unfold equiv, equiv_dec, R_EqDec in *. simpl in *. repeat Rdec_full; try omega.
    elim Hneq. apply Hdest. now rewrite moving_spec, Heq.
Qed.


(* Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_forbidden : forall da config, ~forbidden config -> ~forbidden (round gatherR da config).
Proof.
intros da config Hok.
(* Three cases for the robogram *)
destruct (support (max (!! config))) as [| pt [| pt' l']] eqn:Hmaj.
{ (* Absurd case: no robot *)
  intros _. apply (support_max_non_nil _ Hmaj). }
{ (* There is a majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  apply Majority_not_forbidden with pt. now apply MajTower_at_forever. }
{ rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config). { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. omega. }
  clear pt pt' l' Hmaj'.
  (* A robot has moved otherwise we have the same configuration before and it is forbidden. *)
  assert (Hnil := no_moving_same_conf gatherR da config).
  destruct (moving gatherR da config) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    assert (Hmove : In rmove (moving gatherR da config)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round gatherR config *)
    assert (Hforbidden := Habs). destruct Habs as [HnG [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ round gatherR da config rmove = pt).
    { assert (Hperm : Permutation (support (!! (round gatherR da config))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
        + rewrite <- NoDupA_Leibniz. apply support_NoDupA.
        + simpl. now rewrite <- size_spec, forbidden_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz, support_spec. unfold In. rewrite Hpt1. apply half_size_config.
          - inversion H; (now inversion H0) || subst. rewrite <- InA_Leibniz, support_spec.
            unfold In. rewrite Hpt2. apply half_size_config. }
      assert (Hpt : In (round gatherR da config rmove) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm. rewrite <- InA_Leibniz, support_In. apply pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, In g (moving gatherR da config) -> round gatherR da config g = pt).
    { intros id Hid.
      rewrite <- Hrmove_pt.
      apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 N.nG) <= (!! config)[pt']).
    { transitivity ((!! (round gatherR da config))[pt']).
      - decompose [and or] Hpt; subst; omega.
      - generalize (@increase_move_iff config da pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. assumption. }
    assert (Hlt : forall p, p <> pt' -> (!! config)[p] < div2 N.nG).
    { assert (Hpt'_in : In pt' (!! config)).
      { unfold In. eapply lt_le_trans; try eassumption. apply half_size_config. }
      assert (Hle := not_forbidden_not_majority_length Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl N.nG).
      destruct (@towers_elements_3 config pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 N.nG); try assumption. apply half_size_config.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total config Hp Hdiff13 Hdiff23); [].
        unfold In in Hpt3_in. rewrite <- (even_div2 HnG). omega. }
    assert (Hmaj' : MajTower_at pt' config).
    { intros x Hx. apply lt_le_trans with (div2 N.nG); trivial. now apply Hlt. }
    apply (MajTower_at_forever da), Majority_not_forbidden in Hmaj'. contradiction. }
Qed.

Close Scope R_scope.

Definition config_to_NxN config :=
  let s := !! config in
  match support (max s) with
    | nil => (0,0)
    | pt :: nil => (1, nG - s[pt])
    | _ :: _ :: _ =>
        if beq_nat (size s) 3
        then (2, nG - s[nth 1 (sort (support s)) 0%R])
        else (3, nG - (s[extreme_center s]
                       + s[hd 0%R (sort  (support s))]
                       + s[last (sort  (support s)) 0%R]))
  end.

Instance config_to_NxN_compat: Proper (equiv ==> eq * eq) config_to_NxN.
Proof.
intros config1 config2 Heq. unfold config_to_NxN.
assert (Hperm : PermutationA equiv (support (max (!! config1)))
                                   (support (max (!! config2)))) by now rewrite Heq.
destruct (support (max (!! config2))) as [| pt [| ? ?]] eqn:Hsupp.
+ symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm. reflexivity.
+ apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]].
  rewrite Hperm, <- Hy, Heq. reflexivity.
+ apply PermutationA_length in Hperm.
  destruct (support (max (!! config1))) as [| ? [| ? ?]]; try discriminate Hperm.
  rewrite Heq. destruct (size (!! config2) =? 3); rewrite Heq; reflexivity.
Qed.

Definition lt_config x y := Lexprod.lexprod lt lt (config_to_NxN x) (config_to_NxN y).

Lemma wf_lt_config: well_founded lt_config.
Proof. unfold lt_config. apply wf_inverse_image, Lexprod.wf_lexprod; apply lt_wf. Qed.

Instance lt_config_compat: Proper (equiv ==> equiv ==> iff) lt_config.
Proof.
  intros config1 config1' heq1 config2 config2' heq2.
  unfold lt_config.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Lemma config_to_NxN_nil_spec : forall config,
  support (max (!! config)) = nil -> config_to_NxN config = (0, 0).
Proof. intros config Heq. unfold config_to_NxN. rewrite Heq. reflexivity. Qed.

Lemma config_to_NxN_Majority_spec : forall config pt,
  MajTower_at pt config ->
  config_to_NxN config = (1, nG - (!! config)[pt]).
Proof.
  intros config pt H.
  unfold config_to_NxN.
  rewrite MajTower_at_equiv in H. rewrite H.
  reflexivity.
Qed.

Lemma config_to_NxN_Three_spec : forall config,
  no_Majority config ->
  size (!! config) = 3 ->
  config_to_NxN config = (2, nG - (!! config)[nth 1 (sort (support (!! config))) 0%R]).
Proof.
intros config Hmaj Hlen. unfold config_to_NxN.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma config_to_NxN_Generic_spec : forall config,
  no_Majority config ->
  size (!! config) <> 3 ->
    config_to_NxN config = 
    (3, nG - ((!! config)[extreme_center (!! config)]
              + (!! config)[mini (!! config)]
              + (!! config)[maxi (!! config)])).
Proof.
intros config Hmaj Hlen. unfold config_to_NxN.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma multiplicity_le_nG : forall pt config, (!! config)[pt] <= nG.
Proof.
intros pt config. etransitivity.
- apply cardinal_lower.
- rewrite cardinal_spect_from_config. simpl. omega.
Qed.

(* When we only have three towers, the new configuration does not create new positions. *)
Lemma support_round_Three_incl : forall config da,
  no_Majority config ->
  size (!! config) = 3 ->
  incl (support (!! (round gatherR da config)))
       (support (!! config)).
Proof.
intros config da Hmaj Hlen pt Hin.
rewrite <- InA_Leibniz in Hin. change eq with equiv in Hin. rewrite support_In, spect_from_config_In in Hin.
destruct Hin as [id Hid]. rewrite round_simplify_Three in Hid; trivial.
destruct (step da id).
+ rewrite <- Hid. setoid_rewrite Permuted_sort at 3. apply nth_In.
  rewrite <- Permuted_sort, <- size_spec, Hlen. omega.
+ rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In, <- Hid. apply pos_in_config.
Qed.

Corollary support_decrease : forall config da,
  no_Majority config ->
  size (!! config) = 3 ->
  size (!! (round gatherR da config)) <= 3.
Proof.
intros config da Hmaj Hlen. rewrite <- Hlen.
generalize (support_round_Three_incl da Hmaj Hlen).
rewrite <- inclA_Leibniz, size_spec, size_spec.
apply (NoDupA_inclA_length _). change eq with equiv. apply support_NoDupA.
Qed.

Theorem round_lt_config : forall da config,
  ~forbidden config -> moving gatherR da config <> nil ->
  lt_config (round gatherR da config) config.
Proof.
intros da config Hvalid Hmove.
apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
assert (Hstep : step da gmove <> None).
{ apply moving_active in Hmove. now rewrite active_spec in Hmove. }
rewrite moving_spec in Hmove.
destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
* (* No robots *)
  elim (support_max_non_nil _ Hmaj).
* (* A majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  assert (Hmaj' : MajTower_at pt (round gatherR da config)) by now apply MajTower_at_forever.
  red.
  rewrite (config_to_NxN_Majority_spec Hmaj), (config_to_NxN_Majority_spec Hmaj').
  apply right_lex.
  assert (Hle : (!! (round gatherR da config))[pt] <= N.nG) by apply multiplicity_le_nG.
  cut ((!! config)[pt] < (!! (round gatherR da config))[pt]). omega.
  assert (Hdestg : round gatherR da config gmove = pt).
  { rewrite (round_simplify_Majority _ Hmaj). destruct (step da gmove); trivial. now elim Hstep. }
  rewrite increase_move_iff. eauto.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config).
  { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. omega. } clear Hmaj'.
  destruct (eq_nat_dec (size (!! config)) 3) as [Hlen | Hlen].
  + (* Three towers case *)
    red. rewrite (config_to_NxN_Three_spec Hmaj Hlen).
    destruct (support (max (!! (round gatherR da config)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (config_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (config_to_NxN_Majority_spec Hmaj'). apply left_lex. omega.
    - rename Hmaj' into Hmaj''.
      assert (Hmaj' : no_Majority (round gatherR da config)).
      { unfold no_Majority. rewrite size_spec, Hmaj''. simpl. omega. } clear Hmaj''.
      assert (Hlen' : size (!! (round gatherR da config)) = 3).
      { apply le_antisym.
        + apply (support_decrease _ Hmaj Hlen).
        + apply (not_forbidden_not_majority_length Hmaj'). now apply never_forbidden. }
      rewrite (config_to_NxN_Three_spec Hmaj' Hlen'). apply right_lex.
      rewrite <- Hlen in Hlen'.
      assert (Hperm : Permutation (support (!! (round gatherR da config)))
                                  (support (!! config))).
      { rewrite <- PermutationA_Leibniz. apply (NoDupA_inclA_length_PermutationA _).
        - apply support_NoDupA.
        - apply support_NoDupA.
        - rewrite inclA_Leibniz. eapply support_round_Three_incl; eassumption.
        - do 2 rewrite <- size_spec. rewrite Hlen'. reflexivity. }
      rewrite Hperm.
      assert (Hup := multiplicity_le_nG (nth 1 (sort (support (!! config))) 0%R)
                                        (round gatherR da config)).
      cut (multiplicity
              (nth 1 (sort (support (!! config))) 0%R)
              (!! (round gatherR da config))
            >
            multiplicity
              (nth 1 (sort (support (!! config))) 0%R)
              (!! config)). omega.
      unfold gt. rewrite increase_move_iff.
      exists gmove. split; trivial.
      erewrite round_simplify_Three; try eassumption.
      destruct (step da gmove) as [Habs | _]; try now elim Hstep.
      destruct gmove eqn:Hid; trivial.
  + (* Generic case *)
    red. rewrite (config_to_NxN_Generic_spec Hmaj Hlen).
    destruct (support (max (!! (round gatherR da config)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (config_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (config_to_NxN_Majority_spec Hmaj'). apply left_lex. omega.
    - { rename Hmaj' into Hmaj''.
        assert (Hmaj' : no_Majority (round gatherR da config)).
        { unfold no_Majority. rewrite size_spec, Hmaj''. simpl. omega. } clear Hmaj''.
        destruct (eq_nat_dec (size (!! (round gatherR da config))) 3)
        as [Hlen' | Hlen'].
        + rewrite (config_to_NxN_Three_spec Hmaj' Hlen'). apply left_lex. omega.
        + rewrite (config_to_NxN_Generic_spec Hmaj' Hlen'). apply right_lex.
          rewrite (Generic_min_same _ Hmaj Hlen), (Generic_max_same _ Hmaj Hlen).
          rewrite (Generic_min_mult_same _ Hmaj Hlen), (Generic_max_mult_same _ Hmaj Hlen).
          rewrite (Generic_extreme_center_same _ Hmaj Hlen).
          assert ((!! (round gatherR da config))[extreme_center (!! config)]
                  + (!! config)[mini (!! config)] + (!! config)[maxi (!! config)]
                  <= N.nG).
          { rewrite <- (Generic_min_mult_same da),  <- (Generic_max_mult_same da); trivial.
            apply sum3_le_total.
            - now apply Rgt_not_eq, Rlt_gt, Generic_min_mid_lt.
            - now apply Rlt_not_eq, Generic_min_max_lt.
            - now apply Rlt_not_eq, Generic_mid_max_lt. }
          cut ((!! config)[extreme_center (!! config)] < (!! (round gatherR da config))[extreme_center (!! config)]).
          omega.
          rewrite increase_move_iff. exists gmove. split; trivial.
          rewrite round_simplify_Generic in Hmove |- *; trivial.
          destruct (step da gmove); try (now elim Hstep); [].
          destruct (is_extremal (config gmove) (!! config)).
          - now elim Hmove.
          - reflexivity. }
Qed.


Definition g1 : G.
Proof.
simpl.
destruct n eqn:Hn. abstract (pose (Hle := size_G); omega).
apply Fin.F1.
Defined.


Instance gathered_at_compat : Proper (equiv ==> equiv ==> iff) gathered_at.
Proof.
intros ? pt Hpt config1 config2 Hconfig. simpl in Hpt. subst. unfold gathered_at.
split; intros H g; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (config id) config.
Proof.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. destruct id as [? | b]. apply Hgather. apply Fin.case0. exact b.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, config id <> pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => Rdec_bool (config x) pt) names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite Rdec_bool_true_iff in Hall. hnf. repeat rewrite Hall; trivial; apply In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, Rdec_bool_false_iff in Hid'. now exists id'.
Qed.

Inductive FirstMove r d config : Prop :=
  | MoveNow : moving r (Streams.hd d) config <> nil -> FirstMove r d config
  | MoveLater : moving r (Streams.hd d) config = nil ->
                FirstMove r (Streams.tl d) (round r (Streams.hd d) config) -> FirstMove r d config.

Instance FirstMove_compat : Proper (equiv ==> equiv ==> equiv ==> iff) FirstMove.
Proof.
intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst.
* revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc.
  + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc.
  + apply MoveLater.
    - rewrite <- Hr, <- Hd, <- Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
* revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc.
  + apply MoveNow. now rewrite Hr, Hd, Hc.
  + apply MoveLater.
    - rewrite Hr, Hd, Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
Qed.

Lemma not_forbidden_gathered_Majority_size : forall config id,
  ~forbidden config -> ~gathered_at (config id) config -> no_Majority config ->
  size (!! config) >= 3.
Proof.
intros config id Hforbidden Hgather Hmaj.
assert (size (!! config) > 1).
{ unfold no_Majority in Hmaj. eapply lt_le_trans; try eassumption; []. now rewrite max_subset. }
rewrite forbidden_equiv in Hforbidden.
destruct (size (!! config)) as [| [| [| n]]]; omega || tauto.
Qed.

(** Given a non-gathered, non forbidden configuration, then some robot will move some day *)
Theorem OneMustMove : forall config id, ~ forbidden config -> ~gathered_at (config id) config ->
  exists gmove, forall da, List.In gmove (active da) -> List.In gmove (moving gatherR da config).
Proof.
intros config id Hforbidden Hgather.
destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
* elim (support_max_non_nil _ Hmaj).
* rewrite <- MajTower_at_equiv in Hmaj.
  apply not_gathered_generalize with _ _ pt in Hgather.
  apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
  exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
  rewrite (round_simplify_Majority _ Hmaj). destruct (step da gmove); auto; now elim Hactive.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config). { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. omega. }
  clear Hmaj' pt e l.
  destruct (eq_nat_dec (size (!! config)) 3) as [Hlen| Hlen].
  + apply not_gathered_generalize with _ _ (middle (!! config)) in Hgather.
    apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Three _ Hmaj Hlen). destruct (step da gmove); auto; now elim Hactive.
  + assert (Hle : size (!! config) >= 4).
    { hnf. apply le_neq_lt.
      - now apply not_forbidden_gathered_Majority_size with id.
      - auto. }
    rewrite size_spec, Permuted_sort in Hle.
    destruct (sort (support (!! config))) as [| pt1 [| pt2 [| pt3 [| pt4 l]]]] eqn:Hsup;
    simpl in Hle; omega || clear Hle.
    assert (Hex : exists pt, In pt (!! config) /\ pt <> extreme_center (!! config)
                             /\ pt <> mini (!! config) /\ pt <> maxi (!! config)).
    { assert (Hmini : mini (!! config) = pt1). { unfold mini. now rewrite Hsup. }
      assert (Hmaxi : In (maxi (!! config)) (pt4 :: l)).
      { unfold maxi. rewrite Hsup. change (In (last (pt4 :: l) 0%R) (pt4 :: l)). apply last_In. discriminate. }
      assert (Hnodup := support_NoDupA (!! config)).
      rewrite NoDupA_Leibniz, Permuted_sort, Hsup in Hnodup.
      inversion_clear Hnodup. inversion_clear H0. inversion_clear H2.
      destruct (Rdec pt2 (extreme_center (!! config))) as [Heq | Heq]; subst.
      - exists pt3. repeat split; try now intro; subst; intuition.
        rewrite <- support_In, InA_Leibniz, Permuted_sort, Hsup. intuition.
      - exists pt2. repeat split; try now intro; subst; intuition.
        rewrite <- support_In, InA_Leibniz, Permuted_sort, Hsup. intuition. }
    destruct Hex as [pt [Hin Hmove]]. rewrite from_config_In in Hin.
    destruct Hin as [gmove Heq]. rewrite <- Heq in Hmove.
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Generic _ Hmaj Hlen). destruct (step da gmove); auto.
    unfold is_extremal. repeat Rdec_full; intuition.
Qed.

(* Given a k-fair demon, in any non gathered, non forbidden configuration, a robot will be the first to move. *)
Theorem Fair_FirstMove : forall d, Fair d ->
  forall config id, ~forbidden config -> ~gathered_at (config id) config -> FirstMove gatherR d config.
Proof.
intros d Hfair config id Hforbidden Hgathered.
destruct (OneMustMove id Hforbidden Hgathered) as [gmove Hmove].
destruct Hfair as [locallyfair Hfair].
revert config Hforbidden Hgathered Hmove Hfair.
specialize (locallyfair gmove).
induction locallyfair; intros config Hforbidden Hgathered Hmove Hfair.
+ apply MoveNow. intro Habs. rewrite <- active_spec in H. apply Hmove in H. rewrite Habs in H. inversion H.
+ destruct (moving gatherR (Streams.hd d) config) eqn:Hnil.
  - apply MoveLater. exact Hnil.
    rewrite (no_moving_same_config _ _ _ Hnil).
    apply (IHlocallyfair); trivial.
    now destruct Hfair.
  - apply MoveNow. rewrite Hnil. discriminate.
Qed.


Lemma gathered_at_forever : forall da config pt, gathered_at pt config -> gathered_at pt (round gatherR da config).
Proof.
intros da config pt Hgather. rewrite (round_simplify_Majority).
+ intro g. destruct (step da (Good g)); reflexivity || apply Hgather.
+ intros pt' Hdiff.
  assert (H0 : (!! config)[pt'] = 0).
  { rewrite spect_from_config_spec, config_list_spec.
    induction names as [| id l].
    + reflexivity.
    + unfold equiv_dec, R_EqDec in *. simpl. Rdec_full.
      - elim Hdiff. rewrite <- Heq. destruct id as [g | b]. apply Hgather. apply Fin.case0. exact b.
      - apply IHl. }
  rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply pos_in_config.
Qed.

Lemma gathered_at_dec : forall config pt, {gathered_at pt config} + {~gathered_at pt config}.
Proof.
intros config pt.
destruct (forallb (fun id => Rdec_bool (config id) pt) names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. simpl. rewrite <- Rdec_bool_true_iff. apply Hall. apply In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  destruct id as [g | b]; try now apply Fin.case0; exact b. intro Habs. specialize (Habs g).
  rewrite negb_true_iff, Rdec_bool_false_iff in Heq. contradiction.
Qed.

Lemma gathered_at_OK : forall d config pt, gathered_at pt config -> Gather pt (execute gatherR d config).
Proof.
cofix Hind. intros d config pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ cbn. apply Hind. now apply gathered_at_forever.
Qed.

Theorem Gathering_in_R :
  forall d, Fair d -> ValidSolGathering gatherR d.
Proof.
intros d Hfair config. revert d Hfair. pattern config.
apply (well_founded_ind wf_lt_config). clear config.
intros config Hind d Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (config (Good g1))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (config (Good g1)). constructor. apply gathered_at_OK. assumption.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  apply (Fair_FirstMove Hfair (Good g1)) in Hmove; trivial.
  induction Hmove as [d config Hmove | d config Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    destruct (Hind (round gatherR (Streams.hd d) config)) with (Streams.tl d) as [pt Hpt].
    - apply round_lt_config; assumption.
    - now destruct Hfair.
    - now apply never_forbidden.
    - exists pt. constructor; cbn; apply Hpt.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_config in Heq.
    destruct Hrec as [pt Hpt].
    - setoid_rewrite Heq. apply Hind.
    - now destruct Hfair.
    - rewrite Heq. assumption.
    - exists pt. constructor; cbn; apply Hpt.
Qed.

Print Assumptions Gathering_in_R.

