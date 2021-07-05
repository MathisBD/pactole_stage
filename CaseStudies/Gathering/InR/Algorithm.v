(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     P. Courtieu, L. Rieg, X. Urbain                                        
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms oaf the CeCILL-C licence     *)
(**************************************************************************)

Require Import Bool.
Require Import Arith.Div2.
Require Import Lia.
Require Import Rbase Rbasic_fun.
Require Import List SetoidList.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
(* Pactole basic definitions *)
Require Export Pactole.Setting.
Require Import FMapFacts.
(* Specific to R topology *)
Require Import Pactole.Spaces.R.
(* Specific to gathering *)
Require Pactole.CaseStudies.Gathering.WithMultiplicity.
(* I don't like this Import, but gathered_at is too frequent *)
Require Import Pactole.CaseStudies.Gathering.Definitions.
(* Specific to multiplicity *)
Require Import Pactole.Observations.MultisetObservation.
Require Import Pactole.Models.Similarity.
(* Specific to rigidity *)
Require Export Pactole.Models.Rigid.
(* Specific to settings without Byzantine robots *)
Require Export Pactole.Models.NoByzantine.

(* User defined *)
Import Permutation.
Import Datatypes.
Close Scope R_scope.

(* rule of thumb *)
Typeclasses eauto := 10.
Set Implicit Arguments.

(* Now we declare the context of our proof: things left abstract are
variables and hypothesis. Other things are defined by declaring type
class instances. *)
Section CorrectnessProof.

Variable n : nat.
Hypothesis size_G : n >= 2.
(** We assume that we have at least two good robots and no byzantine one. *)
Instance MyRobots : Names := Robots n 0.
Instance NoByz : NoByzantine.
Proof using . now split. Qed.

(* (* BUG?: To help finding correct instances, loops otherwise! *)
Existing Instance R_Setoid.
Existing Instance R_EqDec.
Existing Instance R_RMS. *)
(* Specific to R topology *)
Instance Loc : Location := make_Location R.
Instance VS : RealVectorSpace location := R_VS.
Instance ES : EuclideanSpace location := R_ES.

(* We are in a rigid formalism with no other info than the location,
   so the demon makes no choice. *)
(* location_setoid uses R_setoid *)
Instance RobotChoice : robot_choice location := { robot_choice_Setoid := location_Setoid }.
Instance ActiveChoice : update_choice unit := NoChoice.
Instance InactiveChoice : inactive_choice unit := { inactive_choice_EqDec := unit_eqdec }.
Instance Info : State location := OnlyLocation (fun _ => True).
Instance UpdFun : update_function location (Similarity.similarity location) unit := {
  update := fun _ _ _ target _ => target;
  update_compat := ltac:(now repeat intro) }.
Instance InaFun : inactive_function unit := {
  inactive := fun config id _ => config id;
  inactive_compat := ltac:(repeat intro; subst; auto) }.
Instance Rigid : RigidSetting.
Proof using . split. reflexivity. Qed.

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation obs_from_config := (@obs_from_config _ _ _ _ multiset_observation).
Notation "!! config" := (obs_from_config config origin) (at level 10).

Implicit Type config : configuration.
Implicit Type da : similarity_da.
Arguments origin : simpl never.

(* Refolding typeclass instances *)
Ltac changeR :=
  change R with location in *;
  change R_Setoid with location_Setoid in *;
  change R_EqDec with location_EqDec in *.

Lemma similarity_middle : forall (sim : similarity R) x y, (sim ((x + y) / 2) = (sim x + sim y) / 2)%R.
Proof using .
intros sim x y. destruct (similarity_in_R_case sim) as [Hsim | Hsim];
repeat rewrite Hsim; cbn in *; field.
Qed.

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, get_location (config1 (Good g)) == get_location (config2 (Good g))) ->
  config1 == config2.
Proof using . intros. apply no_byz_eq. intro. now apply WithMultiplicity.no_info. Qed.


(** Spectra can never be empty as the number of robots is non null. *)
Lemma obs_non_nil : forall config, !! config =/= empty.
Proof using size_G. apply WithMultiplicity.obs_non_nil. apply size_G. Qed.

Corollary sort_non_nil : forall config, sort (support (!! config)) <> nil.
Proof using size_G.
intros config Habs. apply (obs_non_nil config).
setoid_rewrite <- support_nil.
apply Permutation_nil. setoid_rewrite Permuted_sort at 2. rewrite Habs. reflexivity.
Qed.

Lemma half_size_config : Nat.div2 nG > 0.
Proof using size_G. assert (Heven := size_G). simpl. destruct n as [| [| ?]]; simpl; lia. Qed.

(* We need to unfold [obs_is_ok] for rewriting *)
Definition obs_from_config_spec : forall config l,
  (!! config)[l] = countA_occ _ equiv_dec l (List.map get_location (config_list config))
  := WithMultiplicity.obs_from_config_spec.

(** **  Property expressing the existence of a majority tower  **)

Definition MajTower_at x config :=
  forall y, y <> x -> (!! config)[y] < (!! config)[x].

Instance MajTower_at_compat : Proper (Logic.eq ==> equiv ==> iff) MajTower_at.
Proof using . intros ? ? ? ? ? Hconfig. subst. unfold MajTower_at. now setoid_rewrite Hconfig. Qed.

(** Computationally, it is equivalent to having only one tower with maximum multiplicity. *)

(** ***  The maximum multiplicity of a multiset  **)

Lemma max_similarity : forall (sim : similarity R),
  forall s, max (map sim s) == map sim (max s).
Proof using .
intros. apply max_map_injective.
- intros ? ? Heq. now rewrite Heq.
- apply Similarity.injective.
Qed.

Lemma support_max_non_nil : forall config, support (max (!! config)) <> nil.
Proof using size_G. intros config Habs. rewrite support_nil, max_is_empty in Habs. apply (obs_non_nil _ Habs). Qed.

(** ***  Computational equivalent of having a majority tower  **)

Lemma Majority_MajTower_at : forall config pt,
  support (max (!! config)) = pt :: nil -> MajTower_at pt config.
Proof using .
intros config pt Hmaj x Hx. apply max_spec_lub.
- rewrite <- support_spec, Hmaj. now left.
- rewrite <- support_spec, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

Theorem MajTower_at_equiv : forall config pt, MajTower_at pt config <->
  support (max (!! config)) = pt :: nil.
Proof using size_G.
intros config pt. split; intro Hmaj.
* apply Permutation_length_1_inv. rewrite <- PermutationA_Leibniz. change eq with (@equiv location _).
  apply (NoDupA_equivlistA_PermutationA _).
  + apply NoDupA_singleton.
  + apply support_NoDupA.
  + intro y. rewrite InA_singleton.
    rewrite support_spec, max_spec1_iff; try (now apply obs_non_nil); [].
    split; intro Hpt.
    - rewrite Hpt. intro x. destruct (Rdec x pt).
      -- subst x. reflexivity.
      -- apply lt_le_weak. now apply (Hmaj x).
    - destruct (Rdec y pt) as [? | Hy]; trivial.
      exfalso. apply (Hmaj y) in Hy. specialize (Hpt pt). simpl in *. lia.
* intros x Hx. apply max_spec_lub.
  - rewrite <- support_spec, Hmaj. now left.
  - rewrite <- support_spec, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

(** **  Some properties of [invalid]  **)

Lemma invalid_even : forall conf, WithMultiplicity.invalid conf -> Nat.Even nG.
Proof using . now intros conf [? _]. Qed.

Lemma invalid_support_length : forall config, WithMultiplicity.invalid config ->
  size (!! config) = 2.
Proof using size_G.
intros config [Heven [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
rewrite <- (@cardinal_total_sub_eq _ _ _ _ _ (add pt2 (Nat.div2 nG) (singleton pt1 (Nat.div2 nG)))).
* rewrite size_add; try (now apply half_size_config); [].
  destruct (In_dec pt2 (singleton pt1 (Nat.div2 nG))) as [Hin | Hin].
  + exfalso. rewrite In_singleton in Hin.
    destruct Hin. now elim Hdiff.
  + rewrite size_singleton; trivial. apply half_size_config.
* intro pt. destruct (Rdec pt pt2), (Rdec pt pt1); subst.
  + now elim Hdiff.
  + rewrite add_spec, singleton_spec.
    setoid_rewrite Hpt2.
    repeat destruct_match; simpl in *; contradiction || (try lia).
  + rewrite add_other, singleton_spec.
    - setoid_rewrite Hpt1. repeat destruct_match; simpl in *; contradiction || lia.
    - assumption.
  + rewrite add_other, singleton_spec.
    - repeat destruct_match; simpl in *; contradiction || lia.
    - assumption.
* rewrite cardinal_add, cardinal_singleton, cardinal_obs_from_config.
  simpl. rewrite plus_0_r. now apply even_div2.
Qed.

Lemma support_max_1_not_invalid : forall config pt,
  MajTower_at pt config -> ~WithMultiplicity.invalid config.
Proof using size_G.
intros config pt Hmaj. rewrite MajTower_at_equiv in Hmaj.
assert (Hmax : forall x, In x (max (!! config)) <-> x = pt).
{ intro x. rewrite <- support_spec, Hmaj. split.
  - intro Hin. inversion_clear Hin. assumption. inversion H.
  - intro. subst x. now left. }
intro Hinvalid.
assert (Hsuplen := invalid_support_length Hinvalid).
destruct Hinvalid as [Heven [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
assert (Hsup : Permutation (support (!! config)) (pt1 :: pt2 :: nil)).
{ assert (Hin1 : InA equiv pt1 (support (!! config))).
  { rewrite support_spec. unfold In. setoid_rewrite Hpt1. apply half_size_config. }
  assert (Hin2 : InA equiv pt2 (support (!! config))).
  { rewrite support_spec. unfold In. setoid_rewrite Hpt2. apply half_size_config. }
  apply (PermutationA_split _) in Hin1. destruct Hin1 as [l Hl]. rewrite Hl in Hin2.
  inversion_clear Hin2; try now subst; elim Hdiff.
  rewrite size_spec, Hl in Hsuplen. destruct l as [| x [| ? ?]]; simpl in Hsuplen; try lia.
  inversion_clear H; (now inversion H0) || (cbn in H0; subst). now rewrite <- PermutationA_Leibniz. }
assert (Hpt : pt = pt1 \/ pt = pt2).
{ assert (Hin : List.In pt (pt1 :: pt2 :: nil)).
  { rewrite <- Hsup, <- InA_Leibniz. change eq with (@equiv location _).
    rewrite support_spec, <- max_subset, <- support_spec, Hmaj. now left. }
  inversion_clear Hin; auto. inversion_clear H; auto. inversion H0. }
apply (lt_irrefl (Nat.div2 nG)). destruct Hpt; subst pt.
- rewrite <- Hpt1 at 2. rewrite <- Hpt2. apply max_spec_lub; try (now rewrite Hmax); [].
  rewrite Hmax. auto.
- rewrite <- Hpt1 at 1. rewrite <- Hpt2. apply max_spec_lub; now rewrite Hmax.
Qed.

Definition no_Majority config := (size (max (!! config)) > 1)%nat.

(* invalid_support_length already proves the <- direction *)
Lemma invalid_equiv : forall config,
  WithMultiplicity.invalid config <-> no_Majority config /\ size (!! config) = 2%nat.
Proof using size_G.
  intro config. unfold no_Majority. split.
  - intro Hinvalid. split.
    + rewrite size_spec.
      destruct (support (max (!! config))) as [| pt1 [| pt2 l]] eqn:Hmax.
      * exfalso. revert Hmax. apply support_max_non_nil.
      * exfalso. revert Hmax Hinvalid. rewrite <- MajTower_at_equiv. apply support_max_1_not_invalid.
      * simpl. lia.
    + now apply invalid_support_length.
  - intros [Hlen H2]. rewrite size_spec in Hlen, H2.
    destruct (support (!! config)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try (now simpl in H2; lia); [].
    red.
    assert (Hlen':(size (max (!! config)) = 2)%nat).
    { assert (size (max (!! config)) <= 2)%nat.
      { rewrite max_simplified. unfold simple_max.
        rewrite <- H2, <- Hsupp, <- size_spec.
        apply size_nfilter.
        now repeat intro; subst. }
      rewrite <- size_spec in Hlen. simpl in *; lia. }
    clear Hlen.
    (* let us reformulate this in a more convenient way *)
   cut (exists pt0 pt3,
      pt0 <> pt3 /\ (!! config)[pt0] = Nat.div2 nG /\ (!! config)[pt3] = Nat.div2 nG /\ Nat.Even nG).
   { intros h.
     decompose [ex and] h; repeat split; try (assumption || apply size_G); [].
     exists x, x0; intuition. }
   exists pt1, pt2.
   split.
    * assert (hnodup:NoDupA equiv (pt1 :: pt2 :: nil)). {
        rewrite <- Hsupp.
        apply support_NoDupA. }
      intro abs.
      subst.
      inversion hnodup;subst.
      elim H1.
      constructor.
      reflexivity.
    * assert (h : inclA equiv (support (max (!! config))) (support (!! config))).
      { f_equiv. apply max_subset. }
      assert (Hlen'': length (support (!! config)) <= length (support (max (!! config)))).
      { rewrite size_spec in Hlen'. rewrite Hsupp, Hlen'. reflexivity. }
      assert (h2:=@NoDupA_inclA_length_PermutationA
                    _ equiv _
                    (support (max (!! config)))
                    (support (!! config))
                    (support_NoDupA _)
                    (support_NoDupA _)
                    h Hlen'').
      assert (toto:=cardinal_obs_from_config config origin).
      unfold nB in toto.
      rewrite <- plus_n_O in toto.
      assert (~ equiv pt1 pt2). {
        intro abs.
        repeat red in abs.
        rewrite abs in Hsupp.
        assert (hnodup:=support_NoDupA (!! config)). clear - hnodup Hsupp.
        rewrite Hsupp in hnodup.
        inversion hnodup;subst.
        match goal with
        | H: ~ InA equiv pt2 (pt2 :: nil) |- _ => elim H
        end.
        constructor 1.
        reflexivity. }
      assert (heq_config: equiv (!!config)
                                (add pt1 ((!! config)[pt1])
                                          (add pt2 ((!! config)[pt2]) empty))).
      { intros x.
        destruct (equiv_dec x pt1) as [heqxpt1 | hneqxpt1].
        - rewrite heqxpt1.
          rewrite add_same.
          rewrite (add_other pt2 pt1).
          + rewrite empty_spec.
            lia.
          + assumption.
        - rewrite add_other;auto.
          destruct (equiv_dec x pt2) as [heqxpt2 | hneqxpt2].
          + rewrite heqxpt2.
            rewrite add_same.
            rewrite empty_spec.
            lia.
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
      assert (fold_left (fun acc xn => (snd xn + acc)%nat)
                        ((pt1, (!! config)[pt1]) :: (pt2, (!! config)[pt2]) :: nil)
                        0%nat = nG).
      { rewrite <- toto.
        eapply MMultiset.Preliminary.fold_left_symmetry_PermutationA with (eqA := eq_pair); autoclass.
        - intros ? ? ? ? ? Heq; subst; now rewrite Heq.
        - intros. lia.
        - symmetry.
          transitivity ((pt1, (!! config)[pt1]) :: (elements (add pt2 (!! config)[pt2] empty))).
          eapply elements_add_out;auto.
          + rewrite heq_config, add_same. cut ((!! config)[pt1] > 0). lia.
            change (In pt1 (!! config)). rewrite <- support_spec, Hsupp. now left.
          + rewrite add_empty.
            rewrite In_singleton.
            intros [abs _].
            contradiction.
          + apply permA_skip.
            * reflexivity.
            * transitivity ((pt2, (!! config)[pt2]) :: elements empty).
              eapply elements_add_out; auto.
              -- change (In pt2 (!! config)). rewrite <- support_spec, Hsupp. now right; left.
              -- now rewrite elements_empty. }
      cbn [fold_left snd] in H0.
      rewrite <- plus_n_O in H0.

      assert ((!! config)[pt2] = (!! config)[pt1]).
      { assert (hfilter:= nfilter_In (eqb_max_mult_compat (!! config))).
        transitivity (max_mult (!! config)).
        + specialize (hfilter pt2 (!!config)).
          change (nfilter (fun _ => Nat.eqb (max_mult (!! config))) (!!config))
          with (simple_max (!!config)) in hfilter.
          rewrite <- max_simplified in hfilter.
          destruct hfilter as [hfilter1 hfilter2].
          destruct hfilter1.
          * apply support_spec.
            rewrite h2, Hsupp.
            constructor 2; constructor 1.
            reflexivity.
          * symmetry.
            rewrite <- Nat.eqb_eq.
            assumption.
        + specialize (hfilter pt1 (!!config)).
          change (nfilter (fun _ => Nat.eqb (max_mult (!! config))) (!!config))
          with (simple_max (!!config)) in hfilter.
          rewrite <- max_simplified in hfilter.
          destruct hfilter as [hfilter1 hfilter2].
          destruct hfilter1.
          * apply support_spec.
            rewrite h2, Hsupp.
            now constructor 1.
          * now rewrite <- Nat.eqb_eq. }
      rewrite H1 in *.
      assert (0 + 2 *(!! config)[pt1] = nG)%nat by lia.
      assert (Nat.even nG).
      { rewrite <- H3.
        rewrite (Nat.even_add_mul_2 0 ((!! config)[pt1])).
        apply Nat.even_0. }
      split; [| split].
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl Nat.b2n in H3.
         lia.
      -- rewrite Nat.div2_odd in H3.
         rewrite <- Nat.negb_even in H3.
         rewrite H4 in H3.
         simpl negb in H3.
         simpl  Nat.b2n in H3.
         lia.
      -- now apply Nat.even_spec.
Qed.

Lemma not_invalid_not_majority_length : forall config,
  no_Majority config -> ~WithMultiplicity.invalid config -> (size (!! config) >= 3)%nat.
Proof using size_G.
intros config H1 H2.
assert (size (!! config) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption.
  f_equiv. apply max_subset. }
destruct (size (!! config)) as [| [| [| ?]]] eqn:Hlen; try lia.
exfalso. apply H2. now rewrite invalid_equiv.
Qed.

(** **  Functions for the generic case  **)

Open Scope R_scope.

Definition mini s := List.hd 0 (sort (support s)).
Definition maxi s := List.last (sort (support s)) 0.
Definition middle s := nth 1 (sort (support s)) 0.

Instance mini_compat : Proper (equiv ==> eq) mini.
Proof using . intros s1 s2 Hs. unfold mini. now rewrite Hs. Qed.

Instance maxi_compat : Proper (equiv ==> eq) maxi.
Proof using . intros s1 s2 Hs. unfold maxi. now rewrite Hs. Qed.

Instance middle_compat : Proper (equiv ==> eq) middle.
Proof using . intros s1 s2 Hs. unfold middle. now rewrite Hs. Qed.

Definition is_extremal r s :=
  if Rdec r (mini s) then true else
  if Rdec r (maxi s) then true else false.

Instance is_extremal_compat : Proper (equiv ==> equiv ==> eq) is_extremal.
Proof using .
intros x y Hxy s s' Hs. rewrite <- Hxy. unfold is_extremal, mini, maxi.
destruct (Rdec x (hd 0 (sort (support s)))), (Rdec x (hd 0 (sort (support s'))));
try rewrite Hs in *; contradiction || trivial; [].
destruct (Rdec x (last (sort (support s)) 0)), (Rdec x (last (sort (support s')) 0));
try rewrite Hs in *; contradiction || reflexivity.
Qed.

Lemma is_extremal_map_monotonic_invariant : forall f,
  monotonic Rleb Rleb f -> Util.Preliminary.injective eq eq f ->
  forall x config, is_extremal (f x) (map f (!! config)) = is_extremal x (!! config).
Proof using size_G.
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
Proof using size_G.
intros sim conf r. apply is_extremal_map_monotonic_invariant.
- apply similarity_monotonic.
- change eq with (@equiv location _). apply Similarity.injective.
Qed.

(* When there is no robot (s is empty), the center is 0. *)
Definition extreme_center (s : observation) := (mini s + maxi s) / 2.

Instance extreme_center_compat : Proper (equiv ==> eq) extreme_center.
Proof using . intros s s' Hs. unfold extreme_center, mini, maxi. now rewrite Hs. Qed.

Lemma extreme_center_similarity : forall (sim : similarity location) s, s =/= empty ->
  extreme_center (map sim s) = sim (extreme_center s).
Proof using .
intros sim s Hs.
assert (Hsim1 : Proper (equiv ==> equiv) sim). { intros x y Hxy. now rewrite Hxy. }
assert (Hsim2 := Similarity.injective sim).
unfold extreme_center, mini, maxi.
destruct (similarity_monotonic sim) as [Hinc | Hdec].
* rewrite map_injective_support, (sort_map_increasing Hinc); trivial; [].
  assert (Hperm := Permuted_sort (support s)).
  changeR. destruct (sort (support s)) as [| x l'].
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
  assert (Hperm := Permuted_sort (support s)).
  changeR. destruct (sort (support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
      -- simpl. rewrite similarity_middle. now rewrite Rplus_comm.
      -- rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
Qed.

Lemma extreme_center_similarity_invariant : forall (sim : similarity R) config,
  extreme_center (map sim (!! config)) = sim (extreme_center (!! config)).
Proof using size_G. intros. apply extreme_center_similarity. apply obs_non_nil. Qed.

Lemma middle_map_monotonic_invariant : forall f,
  Proper (equiv ==> equiv) f -> monotonic Rleb Rleb f -> Util.Preliminary.injective eq eq f ->
  forall config, size (!! config) = 3%nat -> middle (map f (!! config)) == f (middle (!! config)).
Proof using size_G.
intros f Hf Hmono Hinj config Hsize. unfold middle. changeR.
rewrite map_injective_support; trivial; [].
rewrite <- (map_nth f).
destruct Hmono as [Hincr | Hdecr].
+ rewrite sort_map_increasing; trivial; []. apply nth_indep.
  rewrite map_length, <- Permuted_sort, <- size_spec, Hsize. lia.
+ rewrite sort_map_decreasing; trivial; [].
  rewrite size_spec, Permuted_sort in Hsize.
  destruct (sort (support (!! config))) as [| ? [| ? [| ? [| ? ?]]]]; simpl in Hsize; try discriminate; [].
  reflexivity.
Qed.

Lemma middle_sim_invariant : forall (sim : similarity R) config, size (!! config) = 3%nat ->
  middle (map sim (!! config)) == sim (middle (!! config)).
Proof using size_G.
intros sim config Hsize.
apply middle_map_monotonic_invariant; autoclass; [].
apply similarity_monotonic.
Qed.


(** *  The robogram solving the gathering **)

(** I works as follows:
    1) if there is a majority tower, everyone goes there;
    2) if there are three towers, everyone goes on the middle one;
    3) otherwise, robots located at non extremal locations go to the middle of the extremal locations.
    The last case will necessarily end into one of the first two, ensuring termination.
**)


Definition gatherR_pgm (s : observation) : location :=
  match support (max s) with
    | nil => 0 (* only happen with no robots *)
    | pt :: nil => pt (* case 1: one majority stack *)
    | _ => (* several majority stacks *)
           if beq_nat (size s) 3
           then middle s else
           if is_extremal 0 s then 0 else extreme_center s
  end.

(** The robogram is invariant by permutation of obsra. *)
Instance gatherR_pgm_compat : Proper (equiv ==> equiv) gatherR_pgm.
Proof using .
unfold gatherR_pgm. intros s s' Hs. assert (Hperm := support_compat (max_compat Hs)).
destruct (support (max s)) as [| pt [| pt2 l]].
+ now rewrite (PermutationA_nil _ Hperm).
+ symmetry in Hperm. destruct (PermutationA_length1 _ Hperm) as [pt' [Heq Hin]]. now rewrite Hin, Heq.
+ assert (Hlength := PermutationA_length Hperm).
  destruct (support (max s')) as [| pt' [| pt2' l']]; try discriminate. rewrite Hs.
  destruct (size s' =? 3); rewrite Hs; try reflexivity; [].
  destruct (is_extremal 0 s'); try rewrite Hs; reflexivity.
Qed.

Definition gatherR := Build_robogram gatherR_pgm.

Section SSYNC_Results.

Variable da : similarity_da.
Hypothesis Hda : SSYNC_da da.

(** **  General simplification lemmas for [round gatherR da _] **)

Lemma round_simplify : forall config,
  round gatherR da config
  == fun id => match da.(activate) id with
                 | false => config id
                 | true =>
                     let s := !! config in
                     match support (max s) with
                       | nil => config id (* only happen with no robots *)
                       | pt :: nil => pt (* case 1: one majority stack *)
                       | _ => (* several majority stacks *)
                              if beq_nat (size s) 3
                              then middle s else
                              if is_extremal (config id) s then config id else extreme_center s
                     end
               end.
Proof using Hda size_G.
intros config. rewrite SSYNC_round_simplify; trivial; [].
apply no_byz_eq. intro g. unfold round.
destruct (activate da (Good g)) eqn:Hactive; try reflexivity; [].
rewrite get_location_lift, rigid_update.
remember (change_frame da config g) as sim.
simpl lift.
(* Simplify the similarity *)
destruct (similarity_in_R sim) as [k [Hk Hsim]].
assert (Hinvsim : forall x, (sim ⁻¹) x = x / k + Similarity.center sim).
{ apply inverse_similarity_in_R; trivial; [].
  destruct Hk; subst; try apply Ropp_neq_0_compat; apply Similarity.zoom_non_null. }
(* Print Graph.
change (Bijection.inverse (frame_choice_bijection sim)) with (frame_choice_bijection (sim ⁻¹)).
rewrite Hinvsim. *)
assert(Hsim_compat : Proper (equiv ==> equiv) sim). { subst. autoclass. }
assert (Hsim_inj2 := Similarity.injective sim).
assert (Hobs := obs_from_config_ignore_snd origin (map_config sim config)
                                               (get_location (map_config sim config (Good g)))).
rewrite (pgm_compat _ _ _ Hobs).
cbn [projT1].
(* Unfold the robogram *)
unfold gatherR, gatherR_pgm. cbn [pgm].
assert (Hperm : PermutationA equiv (support (max (!! (map_config sim config))))
                                   (List.map sim (support (max (!! config))))).
{ rewrite <- map_injective_support; trivial. f_equiv.
  rewrite <- max_similarity, (obs_from_config_map (St := OnlyLocation (fun _ => True)) Hsim_compat I); auto. }
destruct (support (max (!! config))) as [| pt' [| pt2' l']].
* (* Empty support *)
  simpl List.map in Hperm. symmetry in Hperm.
  now apply (PermutationA_nil _), support_max_non_nil in Hperm.
* (* A majority stack *)
  simpl List.map in Hperm. apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]].
  rewrite Hperm. hnf in Hy |- *. subst y. rewrite Hsim.
(*   assert (Heq : 1 * (k * (pt' - center sim)) / k = pt' - center sim) by now simpl; field. *)
  change (inverse (frame_choice_bijection sim)) with (frame_choice_bijection (sim ⁻¹)).
  rewrite Hinvsim.
  simpl. unfold id, ES, VS. field.
  destruct Hk; subst; try apply Ropp_neq_0_compat; apply Similarity.zoom_non_null.
* (* No majority stack *)
  apply PermutationA_length in Hperm.
  destruct (support (max (!! (map_config sim config)))) as [| pt'' [| pt2'' l'']];
  try discriminate Hperm; []. clear Hperm pt' pt2' l' pt'' pt2'' l''.
  assert (Hmap : !! (map_config (Bijection.section (Similarity.sim_f sim)) config)
                 == map (Bijection.section (Similarity.sim_f sim)) (!! config)).
  { change (Bijection.section (Similarity.sim_f sim)) with (lift (existT precondition sim I)).
    rewrite <- (obs_from_config_ignore_snd origin config (sim origin)),
            (obs_from_config_map (St := OnlyLocation (fun _ => True)) _ I config origin); reflexivity. }
  rewrite Hmap, map_injective_size; trivial; [].
  destruct (size (!! config) =? 3) eqn:Hlen.
  + (* There are three towers *)
    rewrite Hmap, middle_sim_invariant.
    - simpl. now rewrite Bijection.retraction_section.
    - now rewrite <- Nat.eqb_eq.
  + (* Generic case *)
    change (IZR Z0) with (@origin location _ _ _). rewrite <- (Similarity.center_prop sim) at 1.
    rewrite Hmap, is_extremal_similarity_invariant.
    (* These are the only two places where we use the fact that similarities are centered
       on the location of the observing robot (i.e. [similarity_center]. *)
    rewrite Heqsim at 1 2. rewrite similarity_center.
    simpl get_location. unfold id. changeR.
    destruct (is_extremal (config (Good g)) (!! config)).
    - (* The current robot is exremal *)
      change (center (change_frame da config g) == config (Good g)).
      now rewrite similarity_center.
    - (* The current robot is not exremal *)
      rewrite Hmap, extreme_center_similarity, Heqsim; apply obs_non_nil || trivial; [].
      simpl. now rewrite Bijection.retraction_section.
Qed.

(** ***  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, everyone goes there. **)
Lemma round_simplify_Majority : forall config pt,
  MajTower_at pt config ->
  round gatherR da config
  == fun id => if activate da id then pt else config id.
Proof using Hda size_G.
intros config pt Hmaj. rewrite round_simplify. intro id.
rewrite MajTower_at_equiv in Hmaj.
destruct_match; try reflexivity. cbv zeta.
destruct (support (max (!! config))) as [| ? [| ? ?]]; try discriminate Hmaj.
inversion Hmaj. reflexivity.
Qed.

(** If we have three towers, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall config,
  no_Majority config ->
  (size (!! config) = 3)%nat ->
  round gatherR da config
  == fun id => if activate da id then nth 1 (sort (support (!! config))) 0 else config id.
Proof using Hda size_G.
intros config Hmaj H3. rewrite round_simplify.
intro id. apply WithMultiplicity.no_info.
destruct (da.(activate) id); try reflexivity; []. cbv zeta.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try lia; [].
rewrite <- Nat.eqb_eq in H3. rewrite H3. reflexivity.
Qed.

(** In the general case, all non extremal robots go to the middle of the extreme. *)
Lemma round_simplify_Generic : forall config,
  no_Majority config ->
  (size (!! config) <> 3)%nat ->
  round gatherR da config == fun id => if activate da id
                                       then if is_extremal (config id) (!! config)
                                            then config id else extreme_center (!! config)
                                       else config id.
Proof using Hda size_G.
intros config Hmaj H3. rewrite round_simplify.
intro id. apply WithMultiplicity.no_info.
destruct_match; try reflexivity; []. cbv zeta.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try lia; [].
rewrite <- Nat.eqb_neq in H3. rewrite H3. reflexivity.
Qed.

Close Scope R_scope.


(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Majority_grow :  forall pt config, MajTower_at pt config ->
  (!! config)[pt] <= (!! (round gatherR da config))[pt].
Proof using Hda size_G.
intros pt config Hmaj.
rewrite (round_simplify_Majority Hmaj).
do 2 rewrite obs_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
+ reflexivity.
+ unfold Datatypes.id. changeR.
  destruct (activate da id).
  - repeat destruct_match; (apply le_n_S + apply le_S; apply IHl) || intuition.
  - destruct_match; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall pt pt' config, pt <> pt' ->
  MajTower_at pt config -> (!! (round gatherR da config))[pt'] <= (!! config)[pt'].
Proof using Hda size_G.
intros pt pt' config Hdiff Hmaj.
rewrite (round_simplify_Majority Hmaj).
do 2 rewrite obs_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
+ reflexivity.
+ unfold Datatypes.id. changeR.
  destruct (activate da id).
  - repeat destruct_match; contradiction || (try apply le_S; apply IHl).
  - repeat destruct_match; contradiction || (try apply le_n_S; apply IHl).
Qed.

(** Whenever there is a majority stack, it remains forever so. **)
Theorem MajTower_at_forever : forall pt config,
  MajTower_at pt config -> MajTower_at pt (round gatherR da config).
Proof using Hda size_G.
intros pt config Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! config)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
- eapply Majority_grow; eauto.
Qed.

Theorem Majority_not_invalid : forall pt config, MajTower_at pt config -> ~WithMultiplicity.invalid config.
Proof using size_G.
intros pt config Hmaj. rewrite invalid_equiv. unfold no_Majority. intros [Hmaj' _].
rewrite MajTower_at_equiv in Hmaj. rewrite size_spec, Hmaj in Hmaj'. simpl in *. lia.
Qed.

(** **  Properties in the generic case  **)

Open Scope R_scope.
(** If we have no majority stack (hence more than one stack),
    then the extreme locations are different. **)
Lemma Generic_min_max_lt_aux : forall l, (length l > 1)%nat -> NoDupA equiv l ->
  hd 0 (sort l) < last (sort l) 0.
Proof using size_G.
intros l Hl Hnodup. rewrite Permuted_sort in Hl.
apply (@PermutationA_NoDupA _ eq _ l (sort l)) in Hnodup.
+ apply Rle_neq_lt.
  - apply sort_min. setoid_rewrite Permuted_sort at 3. apply last_In.
    destruct (sort l); discriminate || simpl in Hl; lia.
  - apply (hd_last_diff _); auto.
+ rewrite PermutationA_Leibniz. apply Permuted_sort.
Qed.

Lemma Generic_min_max_lt : forall config,
  no_Majority config -> mini (!! config) < maxi (!! config).
Proof using size_G.
intros config Hmaj. apply Generic_min_max_lt_aux.
+ apply lt_le_trans with (size (max (!! config))); trivial.
  rewrite <- size_spec. f_equiv. apply max_subset.
+ apply support_NoDupA.
Qed.

Corollary Generic_min_mid_lt : forall config,
  no_Majority config -> mini (!! config) < extreme_center (!! config).
Proof using size_G. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Corollary Generic_mid_max_lt : forall config,
  no_Majority config -> extreme_center (!! config) < maxi (!! config).
Proof using size_G. intros ? H. unfold extreme_center. apply Generic_min_max_lt in H. lra. Qed.

Theorem Generic_min_same : forall config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  mini (!! (round gatherR da config)) = mini (!! config).
Proof using Hda size_G.
intros config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hhdin := sort_non_nil config). apply (hd_In 0%R) in Hhdin.
rewrite <- Permuted_sort in Hhdin at 2.
rewrite <- InA_Leibniz in Hhdin. change eq with (@equiv location _) in Hhdin.
rewrite support_spec, (obs_from_config_In config origin) in Hhdin.
destruct Hhdin as [id Hid].
(* Its position 	before and after are the same *)
assert (Heq : config id == round gatherR da config id).
{ rewrite (round_simplify_Generic Hmaj Hlen id); trivial; [].
  destruct (da.(activate) id); try reflexivity; [].
  unfold is_extremal. Rdec_full; try reflexivity; [].
  elim Hneq. rewrite Hid. apply hd_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_min.
  rewrite <- Hid, <- InA_Leibniz. change eq with (@equiv location _).
  rewrite support_spec, Heq. apply (pos_in_config (round gatherR da config) origin).
* apply sort_min.
  rewrite <- InA_Leibniz. change eq with (@equiv location _).
  rewrite support_spec. apply (obs_from_config_In config origin).
  exists id. apply min_sort.
  + rewrite Heq, <- InA_Leibniz. change eq with (@equiv location _).
    rewrite support_spec. apply (pos_in_config (round gatherR da config) origin).
  + intros y Hy. rewrite <- InA_Leibniz in Hy. change eq with (@equiv location _) in Hy.
    rewrite support_spec, (obs_from_config_In (round gatherR da config) origin) in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite (round_simplify_Generic Hmaj Hlen id'); trivial; [].
    destruct (da.(activate) id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_min. rewrite <- InA_Leibniz. change eq with (@equiv location _).
         rewrite support_spec. apply pos_in_config.
      -- apply sort_min. rewrite <- InA_Leibniz. change eq with (@equiv location _).
         rewrite support_spec. apply pos_in_config.
      -- apply Rlt_le. change (mini (!! config) < extreme_center (!! config)). now apply Generic_min_mid_lt.
    - apply sort_min. rewrite <- InA_Leibniz. change eq with (@equiv location _).
      rewrite support_spec. apply pos_in_config.
Qed.

Theorem Generic_max_same : forall config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  maxi (!! (round gatherR da config)) = maxi (!! config).
Proof using Hda size_G.
intros config Hmaj Hlen.
(* We have a robot [id] at the minimal position in the original config. *)
assert (Hlastin := sort_non_nil config). apply (last_In 0%R) in Hlastin.
rewrite <- Permuted_sort in Hlastin at 2.
rewrite <- InA_Leibniz in Hlastin. change eq with (@equiv location _) in Hlastin.
rewrite support_spec, (obs_from_config_In config origin) in Hlastin.
destruct Hlastin as [id Hid].
(* Its position before and after are the same *)
assert (Heq : config id == round gatherR da config id).
{ rewrite (round_simplify_Generic Hmaj Hlen id).
  destruct (da.(activate) id); try reflexivity; [].
  unfold is_extremal. repeat Rdec_full; try reflexivity; [].
  elim Hneq0. rewrite Hid. apply last_indep. apply sort_non_nil. }
(** Main proof *)
apply Rle_antisym.
* apply sort_max.
  rewrite <- InA_Leibniz. change eq with (@equiv location _).
  rewrite support_spec. apply (obs_from_config_In config origin).
  exists id. apply max_sort.
  + rewrite Heq, <- InA_Leibniz. change eq with (@equiv location _).
    rewrite support_spec. apply (pos_in_config (round gatherR da config)).
  + intros y Hy. rewrite <- InA_Leibniz in Hy. change eq with (@equiv location _) in Hy.
    rewrite support_spec, (obs_from_config_In (round gatherR da config) origin) in Hy.
    destruct Hy as [id' Hid']. rewrite <- Hid', Hid.
    rewrite (round_simplify_Generic Hmaj Hlen id'); try reflexivity; [].
    destruct (da.(activate) id').
    - unfold is_extremal. repeat Rdec_full.
      -- apply sort_max. rewrite <- InA_Leibniz. change eq with (@equiv location _).
         rewrite support_spec. apply pos_in_config.
      -- apply sort_max. rewrite <- InA_Leibniz. change eq with (@equiv location _).
         rewrite support_spec. apply pos_in_config.
      -- apply Rlt_le. change (extreme_center (!! config) < maxi (!! config)). now apply Generic_mid_max_lt.
    - apply sort_max. rewrite <- InA_Leibniz. change eq with (@equiv location _).
      rewrite support_spec. apply pos_in_config.
* apply sort_max.
  rewrite <- Hid, <- InA_Leibniz. change eq with (@equiv location _).
  rewrite support_spec, Heq. apply (pos_in_config (round gatherR da config)).
Qed.


Corollary Generic_extreme_center_same : forall config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  extreme_center (!! (round gatherR da config)) = extreme_center (!! config).
Proof using Hda size_G.
intros config Hmaj Hlen. unfold extreme_center.
now rewrite (Generic_min_same Hmaj Hlen), (Generic_max_same Hmaj Hlen).
Qed.

Theorem Generic_min_mult_same : forall config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  (!! (round gatherR da config))[mini (!! config)] = (!! config)[mini (!! config)].
Proof using Hda size_G.
intros config Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite obs_from_config_spec, config_list_spec.
induction names as [| id l]; simpl in *; unfold Datatypes.id in *.
* reflexivity.
* changeR. destruct (activate da id).
  + destruct_match_eq Hext; repeat destruct_match.
    - f_equal. apply IHl.
    - apply IHl.
    - elim (Rlt_irrefl (mini (!! config))).
      match goal with H : extreme_center _ == _ |- _ => rewrite <- H at 2 end.
      now apply Generic_min_mid_lt.
    - elim (Rlt_irrefl (mini (!! config))).
      match goal with H : extreme_center _ == _ |- _ => rewrite <- H at 2 end.
      now apply Generic_min_mid_lt.
    - exfalso. revert Hext. unfold is_extremal. repeat destruct_match; tauto || discriminate.
    - apply IHl.
  + destruct_match.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Theorem Generic_max_mult_same : forall config,
  no_Majority config -> (size (!! config) <> 3)%nat ->
  (!! (round gatherR da config))[maxi (!! config)] = (!! config)[maxi (!! config)].
Proof using Hda size_G.
intros config Hmaj Hlen.
(* We simplify the lhs *)
rewrite round_simplify_Generic; trivial.
do 2 rewrite obs_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
* reflexivity.
* changeR. unfold Datatypes.id.
  destruct (activate da id).
  + destruct_match_eq Hext; repeat destruct_match.
    - f_equal. apply IHl.
    - apply IHl.
    - elim (Rlt_irrefl (maxi (!! config))).
      match goal with H : extreme_center _ == _ |- _ => rewrite <- H at 1 end.
      now apply Generic_mid_max_lt.
    - elim (Rlt_irrefl (maxi (!! config))).
      match goal with H : extreme_center _ == _ |- _ => rewrite <- H at 1 end.
      now apply Generic_mid_max_lt.
    - exfalso. revert Hext. unfold is_extremal. repeat destruct_match; tauto || discriminate.
    - apply IHl.
  + destruct_match.
    - f_equal. apply IHl.
    - apply IHl.
Qed.

Close Scope R_scope.

Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= nG.
Proof using size_G.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace nG with (nG + nB)%nat by (simpl; lia).
rewrite <- (cardinal_obs_from_config config origin).
rewrite <- (add_remove_id pt1 (!! config) (reflexivity _)) at 4.
rewrite cardinal_add.
rewrite <- (add_remove_id pt2 (!! config) (reflexivity _)) at 6.
rewrite remove_add_comm, cardinal_add; trivial.
rewrite <- (add_remove_id pt3 (!! config) (reflexivity _)) at 8.
rewrite remove_add_comm, remove_add_comm, cardinal_add; trivial; [].
lia.
Qed.

(** All robots moving in a round move towards the same destination. *)
Theorem same_destination : forall config id1 id2,
  List.In id1 (moving gatherR da config) -> List.In id2 (moving gatherR da config) ->
  round gatherR da config id1 == round gatherR da config id2.
Proof using Hda size_G.
intros config id1 id2 Hid1 Hid2.
rewrite (round_simplify config id1), (round_simplify config id2).
destruct (da.(activate) id1) eqn:Hmove1; [destruct (da.(activate) id2) eqn:Hmove2 |].
* (* the real case *)
  cbv zeta.
  destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
  + (* no robots *)
    rewrite support_nil, max_is_empty in Hmaj. elim (obs_non_nil _ Hmaj).
  + (* a majority tower *)
    reflexivity.
  + destruct (size (!! config) =? 3) eqn:Hlen.
    - (* three towers *)
      reflexivity.
    - { (* generic case *)
        rewrite Nat.eqb_neq in Hlen. rename Hmaj into Hmaj'.
        assert (Hmaj : no_Majority config).
        { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. lia. } clear Hmaj'.
        destruct (is_extremal (config id1) (!! config)) eqn:Hextreme1.
        + exfalso. unfold moving in Hid1. rewrite List.filter_In in Hid1. destruct Hid1 as [_ Hid1].
          destruct (equiv_dec (round gatherR da config id1) (config id1)) as [_ | Hneq]; try discriminate.
          apply Hneq. rewrite (round_simplify_Generic Hmaj Hlen id1); trivial; [].
          destruct (da.(activate) id1); try reflexivity; []. now rewrite Hextreme1.
        + destruct (is_extremal (config id2) (!! config)) eqn:Hextreme2.
          - exfalso. unfold moving in Hid2. rewrite List.filter_In in Hid2. destruct Hid2 as [_ Hid2].
            destruct (equiv_dec (round gatherR da config id2) (config id2)) as [_ | Hneq]; try discriminate; [].
            apply Hneq. rewrite (round_simplify_Generic Hmaj Hlen id2).
            destruct (da.(activate) id2); try reflexivity. now rewrite Hextreme2.
          - reflexivity. }
* apply moving_active in Hid2; trivial; []. unfold active in Hid2.
  rewrite List.filter_In, Hmove2 in Hid2. destruct Hid2; discriminate.
* apply moving_active in Hid1; trivial; []. unfold active in Hid1.
  rewrite List.filter_In, Hmove1 in Hid1. destruct Hid1; discriminate.
Qed.

Lemma towers_elements_3 : forall config pt1 pt2,
  (size (!! config) >= 3)%nat ->
  In pt1 (!! config) -> In pt2 (!! config) -> pt1 <> pt2 ->
  exists pt3, pt1 <> pt3 /\ pt2 <> pt3 /\ In pt3 (!! config).
Proof using size_G.
intros config pt1 pt2 Hlen Hpt1 Hpt2 Hdiff12.
rewrite <- support_spec in Hpt1, Hpt2. rewrite size_spec in Hlen.
apply (PermutationA_split _) in Hpt1. destruct Hpt1 as [supp1 Hperm].
rewrite Hperm in Hpt2. inversion_clear Hpt2; try (now elim Hdiff12); []. rename H into Hpt2.
apply (PermutationA_split _) in Hpt2. destruct Hpt2 as [supp2 Hperm2].
rewrite Hperm2 in Hperm. rewrite Hperm in Hlen.
destruct supp2 as [| pt3 supp]; try (now simpl in Hlen; lia); [].
exists pt3.
rewrite <- support_spec. assert (Hnodup := support_NoDupA (!! config)).
rewrite Hperm in *. inversion_clear Hnodup. inversion_clear H0. repeat split.
- intro Habs. subst. apply H. now right; left.
- intro Habs. subst. apply H1. now left.
- now right; right; left.
Qed.

(* TODO: move it somewhere else? inside MultisetSpectrum? *)
(** Generic result of robograms using multiset obsra. *)
Lemma increase_move :
  forall r config pt,
    ((!! config)[pt] < (!! (round r da config))[pt])%nat ->
    exists id, get_location (round r da config id) == pt /\ round r da config id =/= config id.
Proof using .
  intros r config pt Hlt.
  destruct (existsb (fun x => if get_location (round r da config x) =?= pt then
                              if get_location (config x) =?= pt then false else true else false) names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id. revert Heq_bool. repeat destruct_match; try discriminate; [].
    split; auto; [].
    intro Heq. hnf in Heq. congruence.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, get_location (round r da config id) <> pt \/ get_location (config id) = pt).
    { intro id. specialize (Hex id (In_names _)). revert Hex. repeat destruct_match; auto. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt.
    do 2 rewrite obs_from_config_spec, config_list_spec.
    induction names as [| id l]; simpl; trivial; [].
    unfold Datatypes.id in *. repeat destruct_match; auto using le_n_S; [].
    specialize (Hg id). intuition.
Qed.

(* Because of same_destination, we can strengthen the previous result into an equivalence. *)
Lemma increase_move_iff : forall config pt,
  ((!! config)[pt] < (!! (round gatherR da config))[pt])%nat
  <-> exists id, get_location (round gatherR da config id) == pt
              /\ round gatherR da config id =/= config id.
Proof using Hda size_G.
intros config pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', List.In id' (moving gatherR da config) ->
                              get_location (round gatherR da config id') = pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; rewrite moving_spec; auto. }
  assert (Hstay : forall id, get_location (config id) = pt -> get_location (round gatherR da config id) = pt).
  { intros id' Hid'. destruct (get_location (round gatherR da config id') =?= pt) as [Heq | Heq]; trivial; [].
    assert (Habs := Heq). rewrite <- Hid' in Habs.
    assert (Habs' : round gatherR da config id' =/= config id').
    { intro Habs'. rewrite Habs' in Habs. now elim Habs. }
    rewrite <- (moving_spec gatherR) in Habs'. apply Hdest in Habs'. contradiction. }
  do 2 rewrite obs_from_config_spec, config_list_spec.
  assert (Hin : List.In id names) by apply In_names.
  induction names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. hnf in Hroundid. unfold Datatypes.id.
    destruct_match. revert_one @equiv. intro Heq.
    - rewrite <- Hid in Heq. elim Hroundid. now apply WithMultiplicity.no_info.
    - destruct_match; try contradiction; []. apply le_n_S. induction l; simpl.
      -- reflexivity.
      -- repeat destruct_match; try now idtac + apply le_n_S + apply le_S; apply IHl.
         revert_one @complement. intro Hneq. elim Hneq. now apply Hstay.
  + apply IHl in H. simpl in *. repeat destruct_match; try lia; [].
    revert_one @complement. intro Hneq. elim Hneq. 
    apply Hdest. rewrite moving_spec. intro Habs. apply Hneq. now rewrite Habs.
Qed.


(** An invalid configurataion cannot appear during execution.
    
    Any non-invalid config without a majority tower contains at least three towers.
    All robots move toward the same place (same_destination), wlog pt1.
    |\before(pt2)| >= |\after(pt2)| = nG / 2
    As there are [nG] robots, [nG/2] at [p2], we must spread [nG/2] into at least two locations
    thus each of these towers has less than [nG/2] and [pt2] was a majority tower. *)
Theorem never_invalid : forall config, ~WithMultiplicity.invalid config -> ~WithMultiplicity.invalid (round gatherR da config).
Proof using Hda size_G.
intros config Hok.
(* Three cases for the robogram *)
destruct (support (max (!! config))) as [| pt [| pt' l']] eqn:Hmaj.
{ (* Absurd case: no robot *)
  intros _. apply (support_max_non_nil _ Hmaj). }
{ (* There is a majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  apply Majority_not_invalid with pt. now apply MajTower_at_forever. }
{ rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config). { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. lia. }
  clear pt pt' l' Hmaj'.
  (* A robot has moved otherwise we have the same configuration before and it is invalid. *)
  assert (Hnil := no_moving_same_config gatherR da config).
  destruct (moving gatherR da config) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    assert (Hmove : List.In rmove (moving gatherR da config)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round gatherR config *)
    assert (Hinvalid := Habs). destruct Habs as [HnG [_ [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ get_location (round gatherR da config rmove) = pt).
    { assert (Hperm : Permutation (support (!! (round gatherR da config))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
            (* NoDupA_Leibniz had a useless hyp in coq stdlib until april 2020. *)
        (* + rewrite <- NoDupA_Leibniz. change eq with (@equiv location _). apply support_NoDupA. *)
        + simpl length at 2. now rewrite <- size_spec, invalid_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz. change eq with (@equiv location _). rewrite support_spec.
            unfold In. setoid_rewrite Hpt1. apply half_size_config.
          - inversion H; (now inversion H0) || subst.
            rewrite <- InA_Leibniz. change eq with (@equiv location _). rewrite support_spec.
            unfold In. setoid_rewrite Hpt2. apply half_size_config. }
      assert (Hpt : List.In (get_location (round gatherR da config rmove)) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm, <- InA_Leibniz. change eq with (@equiv location _).
        rewrite support_spec. apply pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, List.In g (moving gatherR da config) -> get_location (round gatherR da config g) = pt).
    { intros id Hid.
      rewrite <- Hrmove_pt.
      apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 nG) <= (!! config)[pt']).
    { transitivity ((!! (round gatherR da config))[pt']).
      - decompose [and or] Hpt; subst.
        + setoid_rewrite  Hpt2. reflexivity.
        + setoid_rewrite  Hpt1. reflexivity.
      - generalize (@increase_move_iff config pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. assumption. }
    assert (Hlt : forall p, p <> pt' -> (!! config)[p] < div2 nG).
    { assert (Hpt'_in : In pt' (!! config)).
      { unfold In. eapply lt_le_trans; try eassumption. apply half_size_config. }
      assert (Hle := not_invalid_not_majority_length Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl nG).
      destruct (@towers_elements_3 config pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 nG); try assumption. apply half_size_config.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total config Hp Hdiff13 Hdiff23); [].
        unfold In in Hpt3_in. rewrite <- (even_div2 _ HnG). lia. }
    assert (Hmaj' : MajTower_at pt' config).
    { intros x Hx. apply lt_le_trans with (div2 nG); trivial. now apply Hlt. }
    apply MajTower_at_forever, Majority_not_invalid in Hmaj'. contradiction. }
Qed.

Close Scope R_scope.
Close Scope VectorSpace_scope.

Definition config_to_NxN config :=
  let s := !! config in
  match support (max s) with
    | nil => (0, 0)
    | pt :: nil => (1, nG - s[pt])
    | _ :: _ :: _ =>
        if beq_nat (size s) 3
        then (2, nG - s[nth 1 (sort (support s)) 0%R])
        else (3, nG - (s[extreme_center s]
                       + s[hd 0%R (sort  (support s))]
                       + s[last (sort  (support s)) 0%R]))
  end.

Instance config_to_NxN_compat: Proper (equiv ==> eq * eq) config_to_NxN.
Proof using .
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
Proof using . unfold lt_config. apply wf_inverse_image, Lexprod.wf_lexprod; apply lt_wf. Qed.

Global Instance lt_config_compat: Proper (equiv ==> equiv ==> iff) lt_config.
Proof using .
  intros config1 config1' Heq1 config2 config2' Heq2.
  unfold lt_config.
  rewrite <- Heq1, <- Heq2.
  reflexivity.
Qed.

Lemma config_to_NxN_nil_spec : forall config,
  support (max (!! config)) = nil -> config_to_NxN config = (0, 0).
Proof using . intros config Heq. unfold config_to_NxN. rewrite Heq. reflexivity. Qed.

Lemma config_to_NxN_Majority_spec : forall config pt,
  MajTower_at pt config ->
  config_to_NxN config = (1, nG - (!! config)[pt])%nat.
Proof using size_G.
  intros config pt H.
  unfold config_to_NxN.
  rewrite MajTower_at_equiv in H. rewrite H.
  reflexivity.
Qed.

Lemma config_to_NxN_Three_spec : forall config,
  no_Majority config ->
  size (!! config) = 3 ->
  config_to_NxN config = (2, nG - (!! config)[nth 1 (sort (support (!! config))) 0%R]).
Proof using size_G.
intros config Hmaj Hlen. unfold config_to_NxN.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try lia.
rewrite <- Nat.eqb_eq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma config_to_NxN_Generic_spec : forall config,
  no_Majority config ->
  size (!! config) <> 3 ->
    config_to_NxN config = 
    (3, nG - ((!! config)[extreme_center (!! config)]
              + (!! config)[mini (!! config)]
              + (!! config)[maxi (!! config)])).
Proof using size_G.
intros config Hmaj Hlen. unfold config_to_NxN.
unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try lia.
rewrite <- Nat.eqb_neq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma multiplicity_le_nG : forall pt config, (!! config)[pt] <= nG.
Proof using size_G.
intros pt config. etransitivity.
- apply cardinal_lower.
- rewrite cardinal_obs_from_config. simpl. lia.
Qed.

(* When we only have three towers, the new configuration does not create new positions. *)
Lemma support_round_Three_incl : forall config,
  no_Majority config ->
  size (!! config) = 3 ->
  incl (support (!! (round gatherR da config)))
       (support (!! config)).
Proof using Hda size_G.
intros config Hmaj Hlen pt Hin.
rewrite <- InA_Leibniz in Hin. change eq with (@equiv location _) in Hin. rewrite support_spec, obs_from_config_In in Hin.
destruct Hin as [id Hid]. rewrite (round_simplify_Three Hmaj Hlen id) in Hid.
destruct (da.(activate) id).
+ rewrite <- Hid. setoid_rewrite Permuted_sort at 3. apply nth_In.
  rewrite <- Permuted_sort, <- (size_spec (!! config)), Hlen. lia.
+ rewrite <- InA_Leibniz. change eq with (@equiv location _). rewrite support_spec, <- Hid. apply pos_in_config.
Qed.

Corollary support_decrease : forall config,
  no_Majority config ->
  size (!! config) = 3 ->
  size (!! (round gatherR da config)) <= 3.
Proof using Hda size_G.
intros config Hmaj Hlen. rewrite <- Hlen.
generalize (support_round_Three_incl Hmaj Hlen).
rewrite <- inclA_Leibniz, size_spec, size_spec.
apply (NoDupA_inclA_length _). change eq with (@equiv location _). apply support_NoDupA.
Qed.

Theorem round_lt_config : forall config,
  ~WithMultiplicity.invalid config -> moving gatherR da config <> nil ->
  lt_config (round gatherR da config) config.
Proof using Hda size_G.
intros config Hvalid Hmove.
apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
assert (Hstep : da.(activate) gmove = true).
{ apply moving_active in Hmove; trivial; []. now rewrite active_spec in Hmove. }
rewrite moving_spec in Hmove.
destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
* (* No robots *)
  elim (support_max_non_nil _ Hmaj).
* (* A majority tower *)
  rewrite <- MajTower_at_equiv in Hmaj.
  assert (Hmaj' : MajTower_at pt (round gatherR da config)) by now apply MajTower_at_forever.
  red.
  rewrite (config_to_NxN_Majority_spec Hmaj), (config_to_NxN_Majority_spec Hmaj').
  apply Lexprod.right_lex.
  assert (Hle : (!! (round gatherR da config))[pt] <= nG) by apply multiplicity_le_nG.
  cut ((!! config)[pt] < (!! (round gatherR da config))[pt]). lia.
  assert (Hdestg : get_location (round gatherR da config gmove) = pt).
  { rewrite (round_simplify_Majority Hmaj gmove).
    destruct (da.(activate) gmove); trivial; now elim Hstep. }
  rewrite increase_move_iff. eauto.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config).
  { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. lia. } clear Hmaj'.
  destruct (eq_nat_dec (size (!! config)) 3) as [Hlen | Hlen].
  + (* Three towers case *)
    red. rewrite (config_to_NxN_Three_spec Hmaj Hlen).
    destruct (support (max (!! (round gatherR da config)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (config_to_NxN_nil_spec _ Hmaj'). apply Lexprod.left_lex. lia.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (config_to_NxN_Majority_spec Hmaj').
      apply Lexprod.left_lex. lia.
    - rename Hmaj' into Hmaj''.
      assert (Hmaj' : no_Majority (round gatherR da config)).
      { unfold no_Majority. rewrite size_spec, Hmaj''. simpl. lia. } clear Hmaj''.
      assert (Hlen' : size (!! (round gatherR da config)) = 3).
      { apply le_antisym.
        + apply (support_decrease Hmaj Hlen).
        + apply (not_invalid_not_majority_length Hmaj'). now apply never_invalid. }
      rewrite (config_to_NxN_Three_spec Hmaj' Hlen'). apply Lexprod.right_lex.
      rewrite <- Hlen in Hlen'.
      assert (Hperm : PermutationA equiv (support (!! (round gatherR da config)))
                                         (support (!! config))).
      { apply (NoDupA_inclA_length_PermutationA _).
        - apply support_NoDupA.
        - apply support_NoDupA.
        - rewrite inclA_Leibniz. eapply support_round_Three_incl; eassumption.
        - do 2 rewrite <- size_spec. rewrite Hlen'. reflexivity. }
      rewrite Hperm.
      assert (Hup := multiplicity_le_nG (nth 1 (sort (support (!! config))) 0%R)
                                        (round gatherR da config)).
      cut ((!! (round gatherR da config))[nth 1 (sort (support (!! config))) 0%R]
           > (!! config)[nth 1 (sort (support (!! config))) 0%R] ). simpl in *; lia.
      unfold gt. rewrite increase_move_iff.
      exists gmove. split; trivial; [].
      rewrite (round_simplify_Three Hmaj Hlen gmove).
      destruct (da.(activate) gmove); reflexivity || now elim Hstep.
  + (* Generic case *)
    red. rewrite (config_to_NxN_Generic_spec Hmaj Hlen).
    destruct (support (max (!! (round gatherR da config)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (config_to_NxN_nil_spec _ Hmaj'). apply Lexprod.left_lex. lia.
    - rewrite <- MajTower_at_equiv in Hmaj'. rewrite (config_to_NxN_Majority_spec Hmaj').
      apply Lexprod.left_lex. lia.
    - rename Hmaj' into Hmaj''.
      assert (Hmaj' : no_Majority (round gatherR da config)).
      { unfold no_Majority. rewrite size_spec, Hmaj''. simpl. lia. } clear Hmaj''.
      destruct (eq_nat_dec (size (!! (round gatherR da config))) 3)
      as [Hlen' | Hlen'].
      ++ rewrite (config_to_NxN_Three_spec Hmaj' Hlen'). apply Lexprod.left_lex. lia.
      ++ rewrite (config_to_NxN_Generic_spec Hmaj' Hlen'). apply Lexprod.right_lex.
         rewrite (Generic_min_same Hmaj Hlen), (Generic_max_same Hmaj Hlen).
         rewrite (Generic_min_mult_same Hmaj Hlen), (Generic_max_mult_same Hmaj Hlen).
         rewrite (Generic_extreme_center_same Hmaj Hlen).
         assert ((!! (round gatherR da config))[extreme_center (!! config)]
                 + (!! config)[mini (!! config)] + (!! config)[maxi (!! config)]
                 <= nG).
         { rewrite <- Generic_min_mult_same, <- Generic_max_mult_same; trivial.
           apply sum3_le_total.
           - now apply Rgt_not_eq, Rlt_gt, Generic_min_mid_lt.
           - now apply Rlt_not_eq, Generic_min_max_lt.
           - now apply Rlt_not_eq, Generic_mid_max_lt. }
         cut ((!! config)[extreme_center (!! config)] < (!! (round gatherR da config))[extreme_center (!! config)]).
         lia.
         rewrite increase_move_iff. exists gmove. split; trivial.
         rewrite (round_simplify_Generic Hmaj Hlen gmove) in Hmove |- *; trivial; [].
         destruct (da.(activate) gmove); try (now elim Hstep); [].
         destruct (is_extremal (config gmove) (!! config)).
         -- now elim Hmove.
         -- reflexivity.
Qed.

End SSYNC_Results.

Close Scope R_scope.
Close Scope VectorSpace_scope.

Definition g1 : G.
Proof.
exists 0. abstract (generalize size_G; intro; lia).
Defined.

Instance gathered_at_compat : Proper (equiv ==> equiv ==> iff) Definitions.gathered_at.
Proof using .
intros ? pt Hpt config1 config2 Hconfig. simpl in Hpt. subst. unfold Definitions.gathered_at.
split; intros H g; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (get_location (config id)) config.
Proof using size_G.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. apply (no_byz id), Hgather.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (get_location (config id)) config -> forall pt, ~gathered_at pt config.
Proof using size_G. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, get_location (config id) <> pt.
Proof using .
intros config pt Hgather.
destruct (forallb (fun x => if get_location (config x) =?= pt then true else false) names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite Rdec_bool_true_iff in Hall. hnf. repeat rewrite Hall; trivial; apply In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. revert Hid'. destruct_match; discriminate || intro. now exists id'.
Qed.

Lemma not_invalid_gathered_Majority_size : forall config id,
  ~WithMultiplicity.invalid config -> ~gathered_at (get_location (config id)) config -> no_Majority config ->
  size (!! config) >= 3.
Proof using size_G.
intros config id Hinvalid Hgather Hmaj.
assert (size (!! config) > 1).
{ unfold no_Majority in Hmaj. eapply lt_le_trans; try eassumption; []. now rewrite max_subset. }
rewrite invalid_equiv in Hinvalid.
destruct (size (!! config)) as [| [| [| ?]]]; lia || tauto.
Qed.

(** Given a non-gathered, non invalid configuration, then some robot will move some day *)
Theorem OneMustMove : forall config id, ~ WithMultiplicity.invalid config -> ~gathered_at (get_location (config id)) config ->
  exists gmove, forall da, SSYNC_da da -> List.In gmove (active da) -> List.In gmove (moving gatherR da config).
Proof using size_G.
intros config id Hinvalid Hgather.
destruct (support (max (!! config))) as [| pt [| pt' l]] eqn:Hmaj.
* elim (support_max_non_nil _ Hmaj).
* rewrite <- MajTower_at_equiv in Hmaj.
  apply not_gathered_generalize with _ _ pt in Hgather.
  apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
  exists gmove. intros da Hda Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
  rewrite (round_simplify_Majority da Hda Hmaj gmove).
  destruct (da.(activate) gmove); hnf; auto; discriminate.
* rename Hmaj into Hmaj'.
  assert (Hmaj : no_Majority config). { unfold no_Majority. rewrite size_spec, Hmaj'. simpl. lia. }
  clear Hmaj' pt pt' l.
  destruct (eq_nat_dec (size (!! config)) 3) as [Hlen| Hlen].
  + apply not_gathered_generalize with _ _ (middle (!! config)) in Hgather.
    apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
    exists gmove. intros da Hda Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Three da Hda Hmaj Hlen gmove).
    destruct (da.(activate) gmove); hnf; auto; discriminate.
  + assert (Hle : size (!! config) >= 4).
    { hnf. apply le_neq_lt.
      - now apply not_invalid_gathered_Majority_size with id.
      - auto. }
    rewrite size_spec, Permuted_sort in Hle.
    destruct (sort (support (!! config))) as [| pt1 [| pt2 [| pt3 [| pt4 l]]]] eqn:Hsup;
    simpl in Hle; lia || clear Hle.
    assert (Hex : exists pt, In pt (!! config) /\ pt <> extreme_center (!! config)
                             /\ pt <> mini (!! config) /\ pt <> maxi (!! config)).
    { assert (Hmini : mini (!! config) = pt1). { unfold mini. changeR. now rewrite Hsup. }
      assert (Hmaxi : List.In (maxi (!! config)) (pt4 :: l)).
      { unfold maxi. changeR. rewrite Hsup.
        change (List.In (last (pt4 :: l) 0%R) (pt4 :: l)). apply last_In. discriminate. }
      assert (Hnodup := support_NoDupA (!! config)).
      rewrite NoDupA_Leibniz, Permuted_sort, Hsup in Hnodup.
      inversion_clear Hnodup. inversion_clear H0. inversion_clear H2.
      destruct (Rdec pt2 (extreme_center (!! config))) as [Heq | Heq]; subst.
      - exists pt3. repeat split; try now intro; subst; intuition.
        rewrite <- support_spec, InA_Leibniz, Permuted_sort, Hsup. intuition.
      - exists pt2. repeat split; try now intro; subst; intuition.
        rewrite <- support_spec, InA_Leibniz, Permuted_sort, Hsup. intuition. }
    destruct Hex as [pt [Hin Hmove]]. rewrite obs_from_config_In in Hin.
    destruct Hin as [gmove Heq]. rewrite <- Heq in Hmove.
    exists gmove. intros da Hda Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_Generic da Hda Hmaj Hlen gmove), Hactive.
    decompose [and] Hmove. clear Hmove. unfold is_extremal. hnf. simpl in *. unfold Datatypes.id in *.
    repeat Rdec_full; intro; simpl in *; congruence.
Qed.

(* Given a k-fair demon, in any non gathered, non invalid configuration, a robot will be the first to move. *)
Theorem Fair_FirstMove : forall (d : similarity_demon), SSYNC (similarity_demon2demon d) -> Fair d ->
  forall config id, ~WithMultiplicity.invalid config -> ~gathered_at (get_location (config id)) config -> FirstMove gatherR d config.
Proof using size_G.
intros d HSSYNC Hfair config id Hinvalid Hgathered.
destruct (OneMustMove id Hinvalid Hgathered) as [gmove Hmove].
destruct Hfair as [locallyfair Hfair].
revert config Hinvalid Hgathered Hmove Hfair.
specialize (locallyfair gmove).
generalize (similarity_demon2prop d). revert locallyfair HSSYNC.
generalize (similarity_demon2demon d). clear d. intros d locallyfair HSSYNC Hprop.
induction locallyfair as [d Hactive | d]; intros config Hinvalid Hgathered Hmove Hfair.
+ apply MoveNow. intro Habs. setoid_rewrite <- active_spec in Hactive.
  rewrite <- (demon2demon Hprop) in Hactive.
  apply Hmove in Hactive; try (now destruct HSSYNC); [].
  simpl in Hactive. changeR. rewrite Habs in Hactive. inversion Hactive.
+ destruct (moving gatherR (Stream.hd d) config) eqn:Hnil.
  - apply MoveLater; try exact Hnil.
    rewrite (no_moving_same_config _ _ _ Hnil).
    destruct Hprop, Hfair, HSSYNC.
    now apply IHlocallyfair.
  - apply MoveNow. rewrite Hnil. discriminate.
Qed.


Lemma gathered_at_forever : forall da, SSYNC_da da -> forall config pt,
  gathered_at pt config -> gathered_at pt (round gatherR da config).
Proof using size_G.
intros da Hda config pt Hgather. rewrite (round_simplify_Majority).
+ intro g. destruct (da.(activate) (Good g)); reflexivity || apply Hgather.
+ assumption.
+ intros pt' Hdiff.
  assert (H0 : (!! config)[pt'] = 0).
  { rewrite obs_from_config_spec, config_list_spec.
    induction names as [| id l].
    + reflexivity.
    + simpl. destruct_match.
      - elim Hdiff. simpl in *. subst. apply (no_byz id), Hgather.
      - apply IHl. }
  rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply pos_in_config.
Qed.

Lemma gathered_at_OK : forall (d : similarity_demon) config pt,
  SSYNC (similarity_demon2demon d) -> gathered_at pt config -> Gather pt (execute gatherR d config).
Proof using size_G.
cofix Hind. intros d config pt [] Hgather. constructor.
+ clear Hind. apply Hgather.
+ cbn. apply Hind; trivial; []. now apply gathered_at_forever.
Qed.

Theorem Gathering_in_R : forall d, SSYNC (similarity_demon2demon d) -> Fair d -> WithMultiplicity.ValidSolGathering gatherR d.
Proof using size_G.
intro d. generalize (similarity_demon2prop d).
generalize (similarity_demon2demon d). clear d.
intros d Hprop HSSYNC Hfair config.
revert d Hprop HSSYNC Hfair. pattern config.
apply (well_founded_ind wf_lt_config). clear config.
intros config Hind d' Hprop HSSYNC Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (get_location (config (Good g1)))) as [Hmove | Hmove].
* (* If so, not much to do *)
  apply Stream.Now. exists (get_location (config (Good g1))).
  rewrite <- (demon2demon Hprop) in HSSYNC |- *. now apply gathered_at_OK.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  rewrite <- (demon2demon Hprop) in HSSYNC, Hfair.
  apply (Fair_FirstMove _ HSSYNC Hfair (Good g1)) in Hmove; trivial; [].
  rewrite (demon2demon Hprop) in Hfair, Hmove.
  induction Hmove as [d config Hmove | d config Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    apply Stream.Later. apply Hind.
    - rewrite <- (demon2demon Hprop) in Hmove |- *. destruct HSSYNC. now apply round_lt_config.
    - now destruct Hprop.
    - rewrite <- (demon2demon Hprop). now destruct HSSYNC.
    - now destruct Hfair.
    - rewrite <- (demon2demon Hprop). destruct HSSYNC. now apply never_invalid.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_config in Heq.
    apply Stream.Later. eapply Hrec.
    - setoid_rewrite Heq. apply Hind.
    - apply HSSYNC.
    - now destruct Hfair.
    - rewrite Heq. assumption.
Qed.

End CorrectnessProof.

(* Do not leave this here, because it makes "make vos" fail.
 It is done in Algorithm_Assumptions.v instead *)
(* Print Assumptions Gathering_in_R. *)
