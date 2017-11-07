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
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Gathering.Definitions.
Require Import Pactole.Spectra.MultisetSpectrum.
Require Export Pactole.Models.Rigid.
Import Permutation.
Import Pactole.Spaces.Similarity.
Import Datatypes. (* to recover [id] *)
Set Implicit Arguments.
Close Scope R_scope.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)


(** **  Framework of the correctness proof: a finite set with at least three elements  **)

Parameter n : nat.
Axiom size_G : (3 <= n)%nat.

(** There are n good robots and no byzantine ones. *)
Instance MyRobots : Names := Robots n 0.

Existing Instance R2_Setoid.
Existing Instance R2_EqDec.
Existing Instance R2_RMS.

(* We are in a rigid formalism with no other info than the location, so the demon makes no choice. *)
Instance Choice : update_choice Datatypes.unit := NoChoice.
Instance UpdFun : update_function Datatypes.unit := {
  update := fun _ _ pt _ => pt;
  update_compat := ltac:(now repeat intro) }.
Instance Rigid : RigidUpdate.
Proof. split. reflexivity. Qed.

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation "!! config" := (@spect_from_config R2 R2 _ _ _ _ _ _ multiset_spectrum config origin) (at level 1).
(* (@spect_from_config R2 Datatypes.unit _ _ _ _ _ _ multiset_spectrum) (at level 1). *)
Notation "x == y" := (equiv x y).
Notation spectrum := (@spectrum R2 R2 _ R2_EqDec _ R2_EqDec _ MyRobots multiset_spectrum).
Notation robogram := (@robogram R2 R2 _ _ _ _ _ MyRobots _).
Notation configuration := (@configuration R2 _ _ _ _).
Notation config_list := (@config_list R2 _ _ _ _).
Notation round := (@round R2 R2 _ _ _ _ _ _ _ _).
Notation execution := (@execution R2 R2 _ _ _ _ _).
Notation Madd := (MMultisetInterface.add).

Implicit Type config : configuration.
Implicit Type da : similarity_da.
Implicit Type d : similarity_demon.
Arguments origin : simpl never.


Lemma config_list_alls : forall pt, config_list (fun _ => pt) = alls pt nG.
Proof.
intro. rewrite config_list_spec, map_cst.
setoid_rewrite names_length. simpl. now rewrite plus_0_r.
Qed.

Lemma no_byz : forall P, (forall g, P (Good g)) -> forall id, P id.
Proof.
intros P Hg [g | b].
+ apply Hg.
+ destruct b. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, get_location (config1 (Good g)) == get_location (config2 (Good g))) ->
  config1 == config2.
Proof.
intros config1 config2 Heq id. apply no_info. destruct id as [g | b].
+ apply Heq.
+ destruct b. omega.
Qed.

Lemma map_sim_support : forall (f : Bijection.bijection R2) (s : spectrum),
  PermutationA equiv (support (map f s)) (List.map f (support s)).
Proof.
intros f s. apply map_injective_support.
- intros ? ? Heq. now rewrite Heq.
- apply Bijection.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall config, !! config =/= empty.
Proof. apply spect_non_nil. generalize size_G. simpl. omega. Qed.

Lemma support_non_nil : forall config, support (!! config) <> nil.
Proof. intros config Habs. rewrite support_nil in Habs. apply (spect_non_nil _ Habs). Qed.

Lemma support_max_non_nil : forall config, support (max (!! config)) <> nil.
Proof. intros config Habs. rewrite support_nil, max_empty in Habs. apply (spect_non_nil _ Habs). Qed.


Lemma max_morph : forall (f : Bijection.bijection R2) s, max (map f s) == map f (max s).
Proof.
intros f s. apply max_map_injective.
- intros ? ? Heq. now rewrite Heq.
- apply Bijection.injective.
Qed.

Lemma multiplicity_le_nG : forall pt config, (!! config)[pt] <= nG.
Proof.
intros pt config. etransitivity.
- apply cardinal_lower.
- rewrite cardinal_spect_from_config. simpl. omega.
Qed.

(** **  Definition of the robogram  **)

Open Scope R_scope.

(** The target in the triangle case. *)
(* TODO: replace [barycenter_3_pts] with the general [barycenter]. *)
Function target_triangle (pt1 pt2 pt3 : R2) : R2 :=
  let typ := classify_triangle pt1 pt2 pt3 in
  match typ with
    | Equilateral => barycenter_3_pts pt1 pt2 pt3
    | Isosceles p => p
    | Scalene => opposite_of_max_side pt1 pt2 pt3
  end.

Lemma target_triangle_compat : forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    target_triangle pt1 pt2 pt3 = target_triangle pt1' pt2' pt3'.
Proof.
intros pt1 pt2 pt3 pt1' pt2' pt3' hpermut.
generalize (classify_triangle_compat hpermut).
intro h_classify.
functional induction (target_triangle pt1 pt2 pt3);
generalize h_classify; intro h_classify';
symmetry in h_classify'; rewrite e in h_classify'; unfold target_triangle;
rewrite h_classify'; auto.
- apply barycenter_3_pts_compat; auto.
- apply opposite_of_max_side_compat; auto.
Qed.

(** A function computing the target location of robots.
    Safe to use only when there is no majority tower. *)
Function target (s : spectrum) : R2 :=
  let l := support s in
  match on_SEC l with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* gathered *)
    | pt1 :: pt2 :: pt3 :: nil => (* triangle cases *)
      target_triangle pt1 pt2 pt3
    | _ => (* general case *) R2.center (SEC l)
  end.

Instance target_compat : Proper (equiv ==> Logic.eq) target.
Proof.
intros s1 s2 Hs. unfold target.
assert (Hperm : Permutation (on_SEC (support s1)) (on_SEC (support s2))).
{ now rewrite <- PermutationA_Leibniz, Hs. }
destruct (on_SEC (support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
+ apply Permutation_nil in Hperm. now rewrite Hperm.
+ apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
+ apply Permutation_length_2_inv in Hperm.
  destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial; now rewrite Hs.
+ assert (length (on_SEC (support s2)) =3%nat) by now rewrite <- Hperm.
  destruct (on_SEC (support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
  apply target_triangle_compat; assumption.
+ assert (Hlen : (length (on_SEC (support s2)) = 4 + length l)%nat) by now rewrite <- Hperm.
  destruct (on_SEC (support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in Hlen; try omega.
  now rewrite Hs.
Qed.

(** The list of acceptable locations in a clean configuration. *)
Definition SECT (s : spectrum) : list R2 := target s :: on_SEC (support s).

Instance SECT_compat : Proper (equiv ==> PermutationA equiv) SECT.
Proof.
intros ? ? Hs. unfold SECT. rewrite Hs at 1.
constructor; try reflexivity; []. now rewrite Hs.
Qed.

Definition is_clean (s : spectrum) : bool :=
  if inclA_bool _ equiv_dec (support s) (SECT s) then true else false.

Instance is_clean_compat : Proper (equiv ==> Logic.eq) is_clean.
Proof.
intros ? ? Heq. unfold is_clean.
destruct (inclA_bool _ equiv_dec (support x) (SECT x)) eqn:Hx,
         (inclA_bool _ equiv_dec (support y) (SECT y)) eqn:Hy;
  trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff in *; [|].
+ elim Hy. intros e Hin. rewrite <- Heq in Hin.
  apply SECT_compat in Heq. rewrite <- Heq. now apply Hx.
+ elim Hx. intros e Hin. rewrite Heq in Hin.
  apply SECT_compat in Heq. rewrite Heq. now apply Hy.
Qed.

Lemma is_clean_spec : forall s, is_clean s = true <-> inclA equiv (support s) (SECT s).
Proof.
intro s. unfold is_clean.
split; intro Hclean.
- rewrite <- (inclA_bool_true_iff _ equiv_dec).
  now destruct (inclA_bool _ equiv_dec (support s) (SECT s)).
- rewrite <- inclA_bool_true_iff in Hclean.
  now rewrite Hclean.
Qed.

(** The robogram solving the gathering problem in R². *)
Definition gatherR2_pgm (s : spectrum) : R2 :=
  match support (max s) with
    | nil => origin (* no robot *)
    | pt :: nil => pt (* majority *)
    | _ :: _ :: _ =>
      if is_clean s then target s (* clean case *)
      else if mem equiv_dec origin (SECT s) then origin else target s (* dirty case *)
  end.

Instance gatherR2_pgm_compat : Proper (equiv ==> eq) gatherR2_pgm.
Proof.
intros s1 s2 Hs. unfold gatherR2_pgm.
assert (Hsize : length (support (max s1)) = length (support (max s2))) by now rewrite Hs.
destruct (support (max s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (support (max s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ apply max_compat, support_compat in Hs. rewrite Hs1, Hs2 in Hs.
  rewrite PermutationA_Leibniz in Hs. apply Permutation_length_1_inv in Hs. now inversion Hs.
+ rewrite Hs. destruct (is_clean s2).
  - now f_equiv.
  - destruct (mem equiv_dec origin (SECT s1)) eqn:Hin,
             (mem equiv_dec origin (SECT s2)) eqn:Hin';
    rewrite ?mem_true_iff, ?mem_false_iff, ?InA_Leibniz in *;
    try (reflexivity || (rewrite Hs in Hin; contradiction)). now f_equiv.
Qed.

Definition gatherR2 : robogram := {| pgm := gatherR2_pgm |}.

Close Scope R_scope.


(** **  Decreasing measure ensuring termination  **)

(** ***  Naming the useful cases in the algorithm and proof  **)

Definition MajTower_at x config := forall y, y <> x -> ((!! config)[y] < (!! config)[x]).

Definition no_Majority config := (size (max (!! config)) > 1)%nat.

Definition diameter_case config :=
  no_Majority config
  /\ exists pt1 pt2, PermutationA equiv (on_SEC (support (!! config))) (pt1 :: pt2 :: nil).

Definition triangle_case config :=
  no_Majority config
  /\ exists pt1 pt2 pt3, PermutationA equiv (on_SEC (support (!! config))) (pt1 :: pt2 :: pt3 :: nil).

Definition equilateral_case config :=
  no_Majority config
  /\ exists pt1 pt2 pt3, PermutationA equiv (on_SEC (support (!! config))) (pt1 :: pt2 :: pt3 :: nil)
                         /\ classify_triangle pt1 pt2 pt3 = Equilateral.

Definition generic_case config :=
  no_Majority config
  /\ exists pt1 pt2 pt3 pt4 l, PermutationA equiv (on_SEC (support (!! config)))
                                                  (pt1 :: pt2 :: pt3 :: pt4 :: l).


Instance no_Majority_compat : Proper (equiv ==> iff) no_Majority.
Proof. intros ? ? Hconfig. unfold no_Majority. now setoid_rewrite Hconfig. Qed.

Instance MajTower_at_compat : Proper (Logic.eq ==> equiv ==> iff) MajTower_at.
Proof. intros ? ? ? ? ? Hconfig. subst. unfold MajTower_at. now setoid_rewrite Hconfig. Qed.

Instance diameter_case_compat : Proper (equiv ==> iff) diameter_case.
Proof. intros ? ? Hconfig. unfold diameter_case. now setoid_rewrite Hconfig. Qed.

Instance triangle_case_compat : Proper (equiv ==> iff) triangle_case.
Proof. intros ? ? Hconfig. unfold triangle_case. now setoid_rewrite Hconfig. Qed.

Instance equilateral_case_compat : Proper (equiv ==> iff) equilateral_case.
Proof. intros ? ? Hconfig. unfold equilateral_case. now setoid_rewrite Hconfig. Qed.

Instance generic_case_compat : Proper (equiv ==> iff) generic_case.
Proof. intros ? ? Hconfig. unfold generic_case. now setoid_rewrite Hconfig. Qed.

Definition clean_diameter_case config :=
  diameter_case config /\ is_clean (!! config) = true.


(** Some results about [MajTower_at] and [no_Majority]. *)
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
    simpl equiv. split; intro Hpt.
    - subst y. intro x. destruct (equiv_dec x pt).
      -- rewrite e. reflexivity.
      -- apply lt_le_weak. now apply (Hmaj x).
    - destruct (equiv_dec y pt) as [? | Hy]; trivial.
      exfalso. apply (Hmaj y) in Hy. elim (lt_irrefl (!! config)[pt]).
      eapply le_lt_trans; try eassumption; [].
      apply Hpt.
* intros x Hx. apply max_spec2.
  - rewrite <- support_In, Hmaj. now left.
  - rewrite <- support_In, Hmaj. intro Habs. inversion_clear Habs. now auto. inversion H.
Qed.

Theorem no_Majority_equiv : forall config, no_Majority config
  <-> exists pt1 pt2 l, support (max (!! config)) = pt1 :: pt2 :: l.
Proof.
intros config.
unfold no_Majority. rewrite size_spec.
split; intro Hmaj.
+ destruct (support (max (!! config))) as [| ? [| ? ?]]; cbn in Hmaj; omega || eauto.
+ destruct Hmaj as [? [? [? Hmaj]]]. rewrite Hmaj. cbn. omega.
Qed.

Corollary make_no_Majority : forall pt1 pt2 l config,
  PermutationA equiv (support (max (!! config))) (pt1 :: pt2 :: l) -> no_Majority config.
Proof.
intros pt1 pt2 l config Hperm.
rewrite no_Majority_equiv. apply PermutationA_length in Hperm.
destruct (support (max (!! config))) as [| ? [| ? ?]]; cbn in Hperm; omega || eauto.
Qed.

Lemma no_Majority_on_SEC_length : forall config,
  no_Majority config -> 2 <= length (on_SEC (support (!! config))).
Proof.
intros config Hmaj.
destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 ?]] eqn:Hsec; simpl; omega || exfalso.
+ rewrite on_SEC_nil in Hsec.  apply (support_non_nil _ Hsec).
+ apply on_SEC_singleton_is_singleton in Hsec.
  - rewrite no_Majority_equiv in Hmaj. destruct Hmaj as [? [? [? Hmaj]]].
    assert (Hle := size_max_le (!! config)).
    do 2 rewrite size_spec in Hle.
    rewrite Hmaj, Hsec in Hle. cbn in Hle. omega.
  - rewrite <- NoDupA_Leibniz. change eq with equiv. apply support_NoDupA.
Qed.

(** A Tactic deciding in which case we are in the algorithm. *)
Ltac get_case config :=
  let Hcase := fresh "Hcase" in
(*   try rewrite <- PermutationA_Leibniz in *; *)
  lazymatch goal with
    (* Majority case *)
    | H : support (max (!! config)) = ?pt :: nil |- _ =>
        assert (Hcase : MajTower_at pt config) by now rewrite MajTower_at_equiv
    (* Diameter case *)
    | Hmaj : no_Majority config, H : on_SEC (support (!! config)) = _ :: _ :: nil |- _ =>
        assert (Hcase : diameter_case config)
          by now repeat split; trivial; setoid_rewrite H; repeat eexists; reflexivity
    (* Equilateral case *)
    | Hmaj : no_Majority config, H : on_SEC (support (!! config)) = ?pt1 :: ?pt2 :: ?pt3 :: nil,
      H' : classify_triangle ?pt1 ?pt2 ?pt3 = Equilateral |- _ =>
        assert (Hcase : equilateral_case config)
          by now repeat split; trivial; setoid_rewrite H; repeat eexists; reflexivity || assumption
    (* Triangle case *)
    | Hmaj : no_Majority config, H : on_SEC (support (!! config)) = _ :: _ :: _ :: nil |- _ =>
        assert (Hcase : triangle_case config)
          by now repeat split; trivial; setoid_rewrite H; repeat eexists; reflexivity
    (* Generic case *)
    | Hmaj : no_Majority config, H : on_SEC (support (!! config)) = _ :: _ :: _ :: _ :: _ |- _ =>
        assert (Hcase : generic_case config)
          by now repeat split; trivial; setoid_rewrite H; repeat eexists; reflexivity
    (* no_Majority *)
    | Hmaj : no_Majority config, H : support (max (!! config)) = _ :: _ :: _ |- _ => idtac
    | H : support (max (!! config)) = _ :: _ :: _ |- _ =>
        let Hmaj := fresh "Hmaj" in
        assert (Hmaj : no_Majority config) by (now eapply make_no_Majority; rewrite H); get_case config
  end.

(** ***  Equivalent formulations of [invalid]  **)

Lemma Majority_not_invalid : forall config pt,
  MajTower_at pt config -> ~invalid config.
Proof.
intros config pt Hmaj. rewrite MajTower_at_equiv in Hmaj.
assert (Hmax : forall x, In x (max (!! config)) <-> x = pt).
{ intro x. rewrite <- support_spec, Hmaj. split.
  - intro Hin. inversion_clear Hin. assumption. inversion H.
  - intro. subst x. now left. }
intro Hvalid.
assert (Hsuplen := invalid_support_length eq_refl Hvalid).
destruct Hvalid as [Heven [? [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
assert (Hsup : Permutation (support (!! config)) (pt1 :: pt2 :: nil)).
{ assert (Hin1 : InA equiv pt1 (support (!! config))).
  { rewrite support_spec. unfold In. rewrite Hpt1. apply Exp_prop.div2_not_R0. assumption. }
  assert (Hin2 : InA equiv pt2 (support (!! config))).
  { rewrite support_spec. unfold In. rewrite Hpt2. now apply Exp_prop.div2_not_R0. }
  apply (PermutationA_split _) in Hin1. destruct Hin1 as [l Hl]. rewrite Hl in Hin2.
  inversion_clear Hin2; try now subst; elim Hdiff.
  rewrite size_spec, Hl in Hsuplen. destruct l as [| x [| ? ?]]; simpl in Hsuplen; try omega.
  inversion_clear H.
  - inversion H0; simpl in H1; subst.
    + rewrite <- PermutationA_Leibniz. now change eq with equiv.
    + inversion H1. 
  - inversion H0; simpl in H2; subst.
    + rewrite <- PermutationA_Leibniz. now change eq with equiv.
    + inversion H2. }
assert (Hpt : pt = pt1 \/ pt = pt2).
{ assert (Hin : List.In pt (pt1 :: pt2 :: nil)).
  { rewrite <- Hsup, <- InA_Leibniz. change eq with equiv.
    rewrite support_spec, <- (max_subset (!! config)), <- support_spec, Hmaj.
    now left. }
inversion_clear Hin; auto. inversion_clear H0; auto. inversion H1. }
apply (lt_irrefl (Nat.div2 nG)). destruct Hpt; subst pt.
- rewrite <- Hpt1 at 2. rewrite <- Hpt2. apply max_spec2; try now rewrite Hmax.
  rewrite Hmax. auto.
- rewrite <- Hpt1 at 1. rewrite <- Hpt2. apply max_spec2; now rewrite Hmax.
Qed.

(* invalid_support_length already proves the -> direction *)
Lemma invalid_equiv : forall config,
  invalid config <-> no_Majority config /\ size (!! config) = 2%nat.
Proof.
intro config. unfold no_Majority. split.
- intro Hinvalid. split.
  + rewrite size_spec. destruct (support (max (!! config))) as [| pt1 [| pt2 l]] eqn:Hmax.
    * exfalso. revert Hmax. apply support_max_non_nil.
    * exfalso. revert Hmax Hinvalid. rewrite <- MajTower_at_equiv. apply Majority_not_invalid.
    * simpl. omega.
  + now apply invalid_support_length.
- intros [Hlen H2]. rewrite size_spec in Hlen, H2.
  destruct (support (!! config)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try (now simpl in H2; omega); [].
  red.
  assert (Hlen':(size (max (!! config)) = 2)%nat).
  { assert (size (max (!! config)) <= 2)%nat.
    { unfold max.
      rewrite <- H2, <- Hsupp, <- size_spec.
      apply size_nfilter.
      now repeat intro; subst. }
    rewrite <- size_spec in Hlen. omega. }
  clear Hlen H2.
  (* let us reformulate this in a more convenient way *)
 cut (exists pt0 pt3,
    pt0 <> pt3 /\
    (!! config)[pt0] = Nat.div2 nG /\ (!! config)[pt3] = Nat.div2 nG /\ Nat.Even nG).
 { intros h.
   decompose [ex and] h; repeat split; trivial.
   - unfold ge. transitivity 3; omega || apply size_G.
   - exists x, x0; intuition. }
 exists pt1, pt2.
 split.
  * assert (hnodup:NoDupA equiv (pt1 :: pt2 :: nil)).
    { rewrite <- Hsupp. apply support_NoDupA. }
    intro abs.
    subst.
    inversion hnodup; subst.
    elim H1.
    constructor.
    reflexivity.
  * assert (h := @support_nfilter _ _ _ _ _ _ (eqb_max_mult_compat (!!config)) (!! config)).
    { change (nfilter (fun _ : R2 => Nat.eqb (max_mult (!! config))) (!! config))
      with (max (!!config)) in h.
      assert (Hlen'': length (support (!! config)) <= length (support (max (!! config)))).
      { rewrite size_spec in Hlen'. now rewrite Hsupp, Hlen'. }
      assert (h2:=@NoDupA_inclA_length_PermutationA
                    _ equiv _
                    (support (max (!! config)))
                    (support (!! config))
                    (support_NoDupA _)
                    (support_NoDupA _)
                    h Hlen'').
      assert (toto := cardinal_spect_from_config config origin).
      rewrite <- plus_n_O in toto.
      assert (~ equiv pt1 pt2). {
        intro abs.
        repeat red in abs.
        rewrite abs in Hsupp.
        assert (hnodup := support_NoDupA (!! config)).
        rewrite  Hsupp in hnodup.
        inversion hnodup; subst.
        match goal with H : ~ InA equiv pt2 (pt2 :: nil) |- _ => elim H end.
        constructor 1.
        reflexivity. }
      assert (heq_config:equiv (!!config) (Madd pt1 ((!! config)[pt1]) (Madd pt2 ((!! config)[pt2]) empty))).
    { red.
      intros x.
      destruct (equiv_dec x pt1) as [heqxpt1 | hneqxpt1].
      - rewrite heqxpt1, add_same, (add_other pt2 pt1).
        + now rewrite empty_spec.
        + assumption.
      - rewrite add_other; auto.
        destruct (equiv_dec x pt2) as [heqxpt2 | hneqxpt2].
        + now rewrite heqxpt2, add_same, empty_spec.
        + rewrite add_other; auto.
          rewrite empty_spec, <- not_In, <- support_spec.
          intro abs. simpl equiv in abs. rewrite Hsupp in abs.

          inversion abs; try contradiction; subst.
          inversion H1; try contradiction; subst.
          rewrite InA_nil in H2.
          assumption. }
    rewrite heq_config in toto.
    rewrite cardinal_fold_elements in toto.
    assert (fold_left (fun acc xn => snd xn + acc)
                      ((pt1, (!! config)[pt1])
                         :: (pt2, (!! config)[pt2])
                         :: nil) 0
            = nG).
    { rewrite <- toto.
      eapply MMultiset.Preliminary.fold_left_symmetry_PermutationA with (eqA := eq_pair); autoclass.
      - repeat intro; subst. now rewrite H1.
      - intros. omega.
      - symmetry.
        transitivity ((pt1, (!! config)[pt1]) :: (elements (Madd pt2 (!! config)[pt2] empty))).
        eapply elements_add_out; auto.
        + rewrite heq_config, add_same. cut ((!! config)[pt1] > 0). omega.
          change (In pt1 (!! config)). rewrite <- support_In, Hsupp. now left.
        + rewrite add_empty.
          rewrite In_singleton.
          intros [abs _].
          contradiction.
        + apply permA_skip.
          * reflexivity.
          * transitivity ((pt2, (!! config)[pt2]) :: elements empty).
            -- eapply elements_add_out; auto. change (In pt2 (!! config)).
               rewrite <- support_In, Hsupp. now right; left.
            -- now rewrite elements_empty. }
    change ((!! config)[pt2] + ((!! config)[pt1] + 0) = nG) in H0.
    rewrite <- plus_n_O in H0.

    assert ((!! config)[pt2] = (!! config)[pt1]).
    { assert (hfilter:= nfilter_In (eqb_max_mult_compat (!! config))).
      transitivity (max_mult (!! config)).
      + specialize (hfilter pt2 (!!config)).
        replace (nfilter (fun _ => Nat.eqb (max_mult (!! config))) (!!config))
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
        replace (nfilter (fun _ => Nat.eqb (max_mult (!! config))) (!!config))
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
    assert ( 0 + 2 *(!! config)[pt1] = nG) by omega.
    assert (Nat.even nG = true).
    { rewrite <- H2.
      rewrite (Nat.even_add_mul_2 0 ((!! config)[pt1])).
      apply Nat.even_0. }
    split;[| split].
    -- rewrite Nat.div2_odd in H2.
       rewrite <- Nat.negb_even in H2.
       rewrite H3 in H2.
       simpl negb in H2.
       simpl  Nat.b2n in H2.
       repeat rewrite <- plus_n_O,plus_O_n in H2.
       omega.
    -- rewrite Nat.div2_odd in H2.
       rewrite <- Nat.negb_even in H2.
       rewrite H3 in H2.
       simpl negb in H2.
       simpl  Nat.b2n in H2.
       repeat rewrite <- plus_n_O,plus_O_n in H2.
       omega.
    -- apply Even.even_equiv.
       apply Even.even_equiv.
       apply Nat.even_spec.
       assumption. }
Qed.

Lemma not_invalid_no_majority_size : forall config,
  no_Majority config -> ~invalid config -> (size (!! config) >= 3)%nat.
Proof.
intros config H1 H2.
assert (size (!! config) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption; [].
  do 2 rewrite size_spec. apply (@NoDupA_inclA_length _ equiv _).
  - apply support_NoDupA.
  - unfold max. apply support_nfilter. repeat intro. now subst. }
 destruct (size (!! config)) as [| [| [| ?]]] eqn:Hlen; try omega.
exfalso. apply H2. now rewrite invalid_equiv.
Qed.


(** ***  Global decreasing measure  **)

(** It is a lexicographic order on the index of the type of config + the number of robots that should move. *)
(**
  -  ]   Gathered: no need
  - 0]   Majority tower: # robots not on majority tower
  - 1]   Clean diameter case: # robots not on target
  - 2]   Dirty diameter case: # robots not on SECT
  - 3]   Clean equilateral triangle: # robots not on target
  - 4]   Dirty equilateral triangle: # robots not on SECT
  - 3']  Clean isosceles triangle not equilateral: # robots not on target
  - 4']  Dirty isosceles triangle not equilateral: # robots not on SECT
  - 3''] Clean scalene triangle: # robots not on target
  - 4''] Dirty scalene triangle: # robots not on SECT
  - 5]   Clean generic case (|SEC| ≥ 4): # robots not on target
  - 6]   Dirty Generic case (|SEC| ≥ 4): # robots not on SECT
*)

Definition SECT_cardinal s :=
  cardinal (filter (fun x => if InA_dec equiv_dec x (SECT s) then true else false) s).

Instance SECT_cardinal_compat : Proper (equiv ==> Logic.eq) SECT_cardinal.
Proof.
intros s1 s2 Hs. unfold SECT_cardinal. f_equiv. rewrite Hs.
apply filter_extensionality_compat.
- intros x y Hxy. now rewrite Hxy.
- intro x. destruct (InA_dec equiv_dec x (SECT s1)), (InA_dec equiv_dec x (SECT s2));
  trivial; rewrite Hs in *; contradiction.
Qed.

Lemma SECT_cardinal_le_nG : forall config, SECT_cardinal (!! config) <= nG.
Proof.
intro config. unfold SECT_cardinal.
replace nG with (nG + nB) by (simpl; apply plus_0_r).
rewrite <- (cardinal_spect_from_config config origin).
apply cardinal_sub_compat, filter_subset.
intros ? ? H. now rewrite H.
Qed.

Definition measure_clean (s : spectrum) := nG - s[target s].
Definition measure_dirty (s : spectrum) := nG - SECT_cardinal s.

Function measure (s : spectrum) : nat * nat :=
  match support (max s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => (0, nG -  s[pt]) (* majority *)
    | _ :: _ :: _ =>
      match on_SEC (support s) with
        | nil | _ :: nil => (0, 0) (* impossible cases *)
        | pt1 :: pt2 :: nil => (* diameter case *)
            if is_clean s then (1, measure_clean s) else (2, measure_dirty s)
        | pt1 :: pt2 :: pt3 :: nil => (* triangle case *)
            if is_clean s then (3, measure_clean s) else (4, measure_dirty s)
        | _ => (* general case *) if is_clean s then (5, measure_clean s) else (6, measure_dirty s)
      end
  end.

Instance measure_clean_compat : Proper (equiv ==> Logic.eq) measure_clean.
Proof. intros ? ? Heq. unfold measure_clean. now rewrite Heq. Qed.

Instance measure_dirty_compat : Proper (equiv ==> Logic.eq) measure_dirty.
Proof. intros ? ? Heq. unfold measure_dirty. now rewrite Heq. Qed.

Instance measure_compat : Proper (equiv ==> Logic.eq) measure.
Proof.
intros s1 s2 Hs. unfold measure.
assert (Hsize : length (support (max s1)) = length (support (max s2))) by now rewrite Hs.
destruct (support (max s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (support (max s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ rewrite Hs. repeat f_equal.
  rewrite <- (PermutationA_1 _). rewrite <- Hs1, <- Hs2. rewrite Hs. reflexivity.
+ clear -Hs.
  assert (Hperm : Permutation (on_SEC (support s1)) (on_SEC (support s2))).
  { now rewrite <- PermutationA_Leibniz, Hs. }
  destruct (on_SEC (support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
  - apply Permutation_nil in Hperm. now rewrite Hperm.
  - apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
  - apply Permutation_length_2_inv in Hperm.
    destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial;
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (Hlen : (length (on_SEC (support s2)) =3%nat)) by now rewrite <- Hperm.
    destruct (on_SEC (support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in Hlen; try omega.
    rewrite Hs. destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (Hlen : (length (on_SEC (support s2)) = 4 + length l)%nat) by now rewrite <- Hperm.
    destruct (on_SEC (support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in Hlen; try omega.
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
Qed.


Definition lt_config x y := Lexprod.lexprod lt lt (measure (!! x)) (measure (!! y)).

Lemma wf_lt_config: well_founded lt_config.
Proof. unfold lt_config. apply wf_inverse_image, Lexprod.wf_lexprod; apply lt_wf. Qed.

Instance lt_config_compat : Proper (equiv ==> equiv ==> iff) lt_config.
Proof.
intros config1 config1' Heq1 config2 config2' Heq2.
unfold lt_config.
now rewrite <- Heq1, <- Heq2.
Qed.

(** ***  The robogram is invariant by a change of the frame of reference  **)

(** We first prove how the functions used by the robogram are affected by a change of the frame of reference. *)
Lemma target_triangle_morph:
  forall (sim : similarity R2) pt1 pt2 pt3, target_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = sim (target_triangle pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold target_triangle.
rewrite classify_triangle_morph.
destruct (classify_triangle pt1 pt2 pt3); simpl; auto.
- apply barycenter_3_morph.
- apply opposite_of_max_side_morph.
Qed.

Lemma target_morph : forall (sim : similarity R2) (s : spectrum),
  support s <> nil -> target (map sim s) = sim (target s).
Proof.
intros sim s hnonempty. unfold target.
assert (Hperm : Permutation (List.map sim (on_SEC (support s))) (on_SEC (support (map sim s)))).
{ assert (Heq : on_SEC (support s)
                == List.filter (fun x => on_circle (sim_circle sim (SEC (support s))) (sim x)) (support s)).
  { apply Preliminary.filter_extensionality_compat; trivial; [].
    repeat intro. subst. now rewrite on_circle_morph. }
  rewrite Heq. rewrite <- filter_map.
  rewrite <- PermutationA_Leibniz. rewrite <- map_injective_support; trivial.
  - unfold on_SEC. rewrite Preliminary.filter_extensionality_compat; try reflexivity; [].
    repeat intro. subst. f_equal. symmetry. rewrite <- SEC_morph.
    apply SEC_compat. rewrite <- PermutationA_Leibniz. change eq with equiv. apply map_sim_support.
  - intros ? ? H. now rewrite H.
  - apply injective. }
rewrite <- PermutationA_Leibniz in Hperm. change eq with equiv in Hperm.
assert (Hlen := PermutationA_length Hperm).
destruct ((on_SEC (support s))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hn,
         (on_SEC (support (map sim s))) as [| pt1' [| pt2' [| pt3' [| ? ?]]]];
simpl in Hlen, Hperm; try (omega || reflexivity); clear Hlen.
+ rewrite on_SEC_nil in Hn. contradiction.
+ now rewrite (PermutationA_1 _) in Hperm.
+ change (sim (R2.center (SEC (support s)))) with (R2.center (sim_circle sim (SEC (support s)))).
  f_equal. rewrite <- SEC_morph. apply SEC_compat.
  rewrite <- PermutationA_Leibniz. change eq with equiv. apply map_sim_support.
+ rewrite PermutationA_Leibniz in Hperm. rewrite <- (target_triangle_compat Hperm). apply target_triangle_morph.
+ change (sim (R2.center (SEC (support s)))) with (R2.center (sim_circle sim (SEC (support s)))).
  f_equal. rewrite <- SEC_morph. apply SEC_compat.
  rewrite <- PermutationA_Leibniz. change eq with equiv. apply map_sim_support.
Qed.

Corollary SECT_morph : forall (sim : similarity R2) s,
  support s <> nil -> PermutationA equiv (SECT (map sim s)) (List.map sim (SECT s)).
Proof.
intros sim s s_nonempty. unfold SECT.
rewrite (target_morph _ _ s_nonempty). constructor; try reflexivity; [].
transitivity (List.filter (on_circle (SEC (support (map sim s)))) (List.map sim (support s))).
+ apply filter_PermutationA_compat, map_sim_support; autoclass.
+ rewrite filter_map.
  cut (List.map sim (List.filter (fun x => on_circle (SEC (support (map sim s))) (sim x)) (support s))
       = (List.map sim (on_SEC (support s)))).
  - intro Heq. now rewrite Heq.
  - f_equal. apply Preliminary.filter_extensionality_compat; trivial.
    repeat intro. subst. now rewrite map_sim_support, SEC_morph, on_circle_morph.
Qed.

Lemma is_clean_morph : forall (sim : similarity R2) s,
    support s <> nil -> is_clean (map sim s) = is_clean s.
Proof.
intros sim s s_nonempty. unfold is_clean.
destruct (inclA_bool _ equiv_dec (support (map sim s)) (SECT (map sim s))) eqn:Hx,
         (inclA_bool _ equiv_dec (support s) (SECT s)) eqn:Hy;
trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff, ?inclA_Leibniz in *; [|].
- elim Hy. intros x Hin. apply (in_map sim) in Hin. rewrite <- map_sim_support in Hin.
  apply Hx in Hin. rewrite SECT_morph, in_map_iff in Hin;auto.
  destruct Hin as [x' [Heq ?]]. apply (Similarity.injective sim) in Heq. now rewrite <- Heq.
- elim Hx. intros x Hin. rewrite SECT_morph; auto. rewrite map_sim_support in Hin.
  rewrite in_map_iff in *. destruct Hin as [x' [? Hin]]. subst. exists x'. repeat split. now apply Hy.
Qed.

(** We express the behavior of the algorithm in the global (demon) frame of reference. *)
Theorem round_simplify : forall da config,
  round gatherR2 da config
  == fun id => if da.(activate) config id
               then let s : spectrum := !! config in
                    match support (max s) with
                      | nil => config id (* only happen with no robots *)
                      | pt :: nil => pt (* majority tower *)
                      | _ => if is_clean s then target s else
                             if mem equiv_dec (get_location (config id)) (SECT s) then config id else target s
                    end
               else config id.
Proof.
intros da config. apply no_byz_eq. intro g. unfold round.
rewrite spect_from_config_ignore_snd. simpl RobotInfo.app. unfold id.
assert (supp_nonempty := support_non_nil config).
destruct (da.(activate) config (Good g)) eqn:Hactive; try reflexivity; [].
remember (change_frame da config g) as sim.
assert (Hsim : Proper (equiv ==> equiv) sim). { intros ? ? Heq. now rewrite Heq. }
unfold gatherR2, gatherR2_pgm. cbn [pgm].
assert (Hperm : Permutation (List.map sim (support (max (!! config))))
                            (support (max (!! (map_config sim config))))).
{ rewrite  <- PermutationA_Leibniz. change eq with equiv.
  now rewrite <- map_sim_support, <- max_morph, spect_from_config_map. }
assert (Hlen := Permutation_length Hperm).
destruct (support (max (!! config))) as [| pt1 [| pt2 l]] eqn:Hmax,
         (support (max (!! (map_config sim config)))) as [| pt1' [| pt2' l']];
simpl in Hlen; discriminate || clear Hlen; [| |].
* rewrite support_nil, max_empty in Hmax. elim (spect_non_nil _ Hmax).
* simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'. cbn. apply (Bijection.compose_inverse_l sim).
* change (map_config sim config) with (map_config (RobotInfo.app sim) config).
  rewrite <- (spect_from_config_ignore_snd (map_config (RobotInfo.app sim) config) (sim origin)),
          <- spect_from_config_map, is_clean_morph; trivial; [].
  destruct (is_clean (!! config)).
  + rewrite rigid_update, <- (spect_from_config_ignore_snd _ (sim origin)),
            <- spect_from_config_map, target_morph; trivial; [].
    apply (compose_inverse_l sim).
  + change (0, 0)%R with origin. rewrite rigid_update. rewrite <- (center_prop sim) at 1.
    rewrite Heqsim at 3. rewrite similarity_center.
    assert (Hperm' : PermutationA equiv (SECT (!! (map_config sim config))) (List.map sim (SECT (!! config)))).
    { rewrite <- SECT_morph; auto. f_equiv. now rewrite spect_from_config_map. }
    rewrite (mem_compat _ equiv_dec _ _ (reflexivity _) (PermutationA_equivlistA _ Hperm')).
    rewrite (mem_injective_map _); trivial; try (now apply injective); [].
    destruct (mem equiv_dec (get_location (config (Good g))) (SECT (!! config))).
    - rewrite <- (center_prop sim), Heqsim, similarity_center. now apply compose_inverse_l.
    - (* change (Bijection.section (sim ⁻¹)) with (Bijection.retraction sim). *)
      simpl. change eq with equiv. unfold id.
      rewrite <- sim.(Bijection.Inversion), <- target_morph; auto; [].
      f_equiv. rewrite spect_from_config_map; trivial; [].
      rewrite spect_from_config_ignore_snd, <- spect_from_config_ignore_snd. f_equiv.
Qed.

(** ****  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, every robot goes there. **)
Lemma round_simplify_Majority : forall da config pt,
    MajTower_at pt config ->
    round gatherR2 da config == fun id => if da.(activate) config id then pt else config id.
Proof.
intros da config pt Hmaj. rewrite round_simplify.
intro id. apply no_info.
destruct (da.(activate) config id); try reflexivity; [].
rewrite MajTower_at_equiv in Hmaj. cbn zeta. now rewrite Hmaj.
Qed.

(** If the configuration is clean, every robot goes to the target. *)
Lemma round_simplify_clean : forall da config,
  no_Majority config ->
  is_clean (!! config) = true ->
  round gatherR2 da config == fun id => if da.(activate) config id then target (!! config) else config id.
Proof.
intros da config Hmaj Hclean. rewrite round_simplify. apply no_byz_eq. intro g.
destruct (da.(activate) config (Good g)); try reflexivity; [].
cbn zeta. rewrite Hclean.
rewrite no_Majority_equiv in Hmaj. destruct Hmaj as [? [? [? Hmaj]]].
now rewrite Hmaj.
Qed.

(** If the configuration is dirty, every robot /not on the SECT/ goes to the target. *)
Lemma round_simplify_dirty : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  round gatherR2 da config == fun id => if da.(activate) config id
                                        then if mem equiv_dec (get_location (config id)) (SECT (!! config))
                                             then config id else target (!! config)
                                        else config id.
Proof.
intros da config Hmaj Hclean. rewrite round_simplify.
apply no_byz_eq. intro g.
destruct (da.(activate) config (Good g)); try reflexivity; [].
cbv zeta. rewrite Hclean.
rewrite no_Majority_equiv in Hmaj. destruct Hmaj as [? [? [? Hmaj]]].
now rewrite Hmaj.
Qed.


(* In the case where one majority tower exists, target is not used and does not compute the real target.
   Hence the no_Majority hypothesis  *)
Theorem destination_is_target : forall da config, no_Majority config ->
  forall id, List.In id (moving gatherR2 da config) -> get_location (round gatherR2 da config id) = target (!! config).
Proof.
intros da config Hmaj id Hmove. rewrite (round_simplify da config id).
destruct (da.(activate) config id) eqn:Hactive.
* rewrite moving_spec, (round_simplify da config id), Hactive in Hmove. cbn zeta in *.
  unfold no_Majority in Hmaj. rewrite size_spec in Hmaj.
  destruct (support (max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega; [].
  destruct (is_clean (!! config)) eqn:Hclean.
  + reflexivity.
  + destruct (mem equiv_dec (get_location (config id)) (SECT (!! config))) eqn:Hmem.
    - now elim Hmove.
    - reflexivity.
* apply moving_active in Hmove. rewrite active_spec in Hmove. congruence.
Qed.

Corollary same_destination : forall da (config : configuration) id1 id2,
  List.In id1 (moving gatherR2 da config) -> List.In id2 (moving gatherR2 da config) ->
  round gatherR2 da config id1 == round gatherR2 da config id2.
Proof.
intros da config id1 id2 Hmove1 Hmove2. apply no_info.
destruct (le_lt_dec 2 (length (support (max (!! config))))) as [Hle |Hlt].
+ assert (no_Majority config). { unfold no_Majority. now rewrite size_spec. }
  now repeat rewrite destination_is_target.
+ rewrite moving_spec in Hmove1, Hmove2.
  rewrite (round_simplify _ _ id1) in Hmove1 |- *. rewrite (round_simplify _ _ id2) in Hmove2 |- *.
  destruct (da.(activate) config id1), (da.(activate) config id2); try (now elim Hmove1 + elim Hmove2); [].
  cbn zeta in *.
  destruct (support (max (!! config))) as [| ? [| ? ?]] eqn:Hsupp.
  - now elim Hmove1.
  - reflexivity.
  - simpl in Hlt. omega.
Qed.

(** Generic result of robograms using multiset spectra. *)
Lemma increase_move :
  forall r config da pt,
    ((!! config)[pt] < (!! (round r da config))[pt])%nat ->
    exists id, get_location (round r da config id) == pt
            /\ get_location (round r da config id) =/= get_location (config id).
Proof.
intros r config da pt Hlt.
destruct (existsb (fun x =>
                     (andb (R2dec_bool ((get_location (round r da config x))) pt)
                           (negb (R2dec_bool (get_location (config x)) pt)))) names) eqn:Hex.
- apply (existsb_exists) in Hex.
  destruct Hex as [id [Hin Heq_bool]].
  exists id.
  rewrite andb_true_iff, negb_true_iff, R2dec_bool_true_iff, R2dec_bool_false_iff in Heq_bool.
  destruct Heq_bool. split; congruence.
- exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
  (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
  assert (Hg : forall id, get_location (round r da config id) <> pt \/ get_location (config id) = pt).
  { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
    destruct (Hex (In_names _)) as [H | H];
    rewrite R2dec_bool_false_iff in H || rewrite R2dec_bool_true_iff in H; simpl in H; tauto. }
  (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
  clear Hex. revert Hlt. apply le_not_lt.
  do 2 rewrite spect_from_config_spec, config_list_spec.
  induction names as [| id l]; trivial; [].
  destruct (get_location (round r da config id) =?= pt) as [Heq | Heq];
  simpl; (do 2 R2dec_full; simpl in *; subst; try omega; []); specialize (Hg id); intuition.
Qed.


(** Because of [same_destination], we can strengthen the previous result into an equivalence. *)
Theorem increase_move_iff :
  forall config da pt,
    ((!! config)[pt] < (!! (round gatherR2 da config))[pt])%nat <->
    exists id, get_location (round gatherR2 da config id) == pt
            /\ get_location (round gatherR2 da config id) =/= get_location (config id).
Proof.
intros config da pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', List.In id' (moving gatherR2 da config) ->
                              get_location (round gatherR2 da config id') == pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; [].
    rewrite moving_spec. intro Heq. apply Hroundid. now rewrite Heq. }
  assert (Hstay : forall id, get_location (config id) == pt -> get_location (round gatherR2 da config id) == pt).
  { intros id' Hid'. destruct (get_location (round gatherR2 da config id') =?= pt) as [Heq | Heq]; trivial; [].
    assert (Habs : round gatherR2 da config id' =/= pt).
    { intro Habs. apply Heq. now rewrite Habs. }
    rewrite <- Hid' in Habs. change (get_location (config id')) with (config id') in Habs.
    rewrite <- moving_spec in Habs. apply Hdest in Habs. contradiction. }
  do 2 rewrite spect_from_config_spec, config_list_spec.
  assert (Hin : List.In id names) by apply In_names.
  induction names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. R2dec_full.
    - rewrite <- Hid in Heq. now elim Hroundid.
    - R2dec_full; try contradiction; [].
      apply le_n_S. induction l as [| id' ?]; simpl.
      -- reflexivity.
      -- repeat R2dec_full; try now idtac + apply le_n_S + apply le_S; apply IHl.
         exfalso. now generalize (Hstay id' ltac:(assumption)).
  + apply IHl in H. simpl. repeat R2dec_full; try (simpl in *; omega); [].
    elim Hneq. apply Hdest. rewrite moving_spec. intro Habs. rewrite Habs in Hneq. contradiction.
Qed.

(** ***  Lemmas about [target]  **)

(** ****  The value of [target] in the various cases  **)

Lemma diameter_target : forall config ptx pty,
  on_SEC (support (!! config)) = ptx :: pty :: nil ->
  target (!! config) = middle ptx pty.
Proof.
intros config ptx pty HonSEC.
unfold target.
rewrite HonSEC.
apply on_SEC_pair_is_diameter in HonSEC.
now rewrite HonSEC.
Qed.

Lemma equilateral_target : forall config ptx pty ptz,
  PermutationA equiv (on_SEC (support (!! config))) (ptx :: pty :: ptz :: nil) ->
  classify_triangle ptx pty ptz = Equilateral ->
  target (!! config) = barycenter_3_pts ptx pty ptz.
Proof.
intros config ptx pty ptz Hperm Htriangle.
unfold target.
assert (Hlen : length (on_SEC (support (!! config))) = 3) by now rewrite Hperm.
destruct (on_SEC (support (!! config))) as [| ? [| ? [| ? [| ? ?]]]]; simpl in Hlen; try discriminate.
rewrite PermutationA_Leibniz in Hperm. rewrite (target_triangle_compat Hperm).
unfold target_triangle. now rewrite Htriangle.
Qed.

Lemma isosceles_target : forall config ptx pty ptz vertex,
    PermutationA equiv (on_SEC (support (!! config))) (ptx :: pty :: ptz :: nil) ->
    classify_triangle ptx pty ptz = Isosceles vertex ->
    target (!! config) = vertex.
Proof.
intros config ptx pty ptz vertex Hsec Htriangle.
unfold target.
assert (Hlen : length (on_SEC (support (!! config))) = length (ptx :: pty :: ptz :: nil))
  by (f_equiv; eassumption).
destruct (on_SEC (support (!! config))) as [| t [| t0 [| t1 [| t2 l]]]] eqn:Heq;
simpl in Hlen; try omega; [].
assert (h := @PermutationA_3 _ equiv _ t t0 t1 ptx pty ptz).
destruct h. specialize (H Hsec).
decompose [or and] H;
match goal with
  | |- target_triangle ?x ?y ?z = ?v => 
    assert (hhh:classify_triangle x y z = classify_triangle ptx pty ptz);
    [ eapply classify_triangle_compat; rewrite <- PermutationA_Leibniz, PermutationA_3; autoclass
    | rewrite <- hhh in Htriangle; auto; unfold target_triangle; rewrite Htriangle; reflexivity ]
end.
Qed.

Lemma scalene_target : forall config ptx pty ptz,
    PermutationA equiv (on_SEC (support (!! config))) (ptx :: pty :: ptz :: nil) ->
    classify_triangle ptx pty ptz = Scalene ->
    target (!! config) = opposite_of_max_side ptx pty ptz.
Proof.
intros config ptx pty ptz Hsec Htriangle.
remember (opposite_of_max_side ptx pty ptz) as vertex.
unfold target.
assert (Hlen : length (on_SEC (support (!! config))) = length (ptx :: pty :: ptz :: nil))
  by (f_equiv; eassumption).
destruct (on_SEC (support (!! config))) as [| t [| t0 [| t1 [| t2 l]]]] eqn:Heq;
simpl in Hlen; try omega; [].
assert (h := @PermutationA_3 _ equiv _ t t0 t1 ptx pty ptz).
destruct h.
specialize (H Hsec).
decompose [or and] H;
match goal with
  | |- target_triangle ?x ?y ?z = ?v => 
    assert (hhh:classify_triangle x y z = classify_triangle ptx pty ptz);
    [ eapply classify_triangle_compat; rewrite <- PermutationA_Leibniz, PermutationA_3; autoclass
               | rewrite <- hhh in Htriangle; auto; unfold target_triangle;
                 rewrite Htriangle, H2, H1, H4; symmetry; auto ]
end;
match goal with
  | |- ?v = opposite_of_max_side ?x ?y ?z => 
    assert (hhhh:opposite_of_max_side ptx pty ptz = opposite_of_max_side x y z);
    [ apply opposite_of_max_side_compat; [now rewrite <- hhh
      | rewrite <- PermutationA_Leibniz, PermutationA_3; auto 8; autoclass ]
    | now rewrite <- hhhh;assumption ]
end.
Qed.

Lemma generic_target : forall config,
  generic_case config ->
  target (!! config) = R2.center (SEC (support (!! config))).
Proof.
intros config [_ [? [? [? [? [? HpermSEC]]]]]]. unfold target.
apply PermutationA_length in HpermSEC.
destruct (on_SEC (support (!! config))) as [| ? [| ? [| ? [| ? ?]]]]; cbn in HpermSEC; omega || reflexivity.
Qed.

(** ****  Results about [target] and [SEC]  **)

Lemma same_on_SEC_same_target : forall config1 config2,
  PermutationA equiv (on_SEC (support (!! config1))) (on_SEC (support (!! config2))) ->
  target (!! config1) = target (!! config2).
Proof.
intros config1 config2 Hperm. unfold target.
assert (Hlen := PermutationA_length Hperm).
destruct (on_SEC (support (!! config1))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec1,
         (on_SEC (support (!! config2))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec2;
reflexivity || simpl in Hlen; try omega.
- now rewrite (PermutationA_1 _) in Hperm.
- f_equal. setoid_rewrite SEC_on_SEC. now rewrite Hsec1, Hperm, Hsec2.
- apply target_triangle_compat. now rewrite <- PermutationA_Leibniz.
- f_equal. setoid_rewrite SEC_on_SEC. now rewrite Hsec1, Hperm, Hsec2.
Qed.

Lemma same_on_SEC_same_SECT : forall config1 config2,
  PermutationA equiv (on_SEC (support (!! config1))) (on_SEC (support (!! config2))) ->
  PermutationA equiv (SECT (!! config1)) (SECT (!! config2)).
Proof.
intros config1 config2 Hsame. unfold SECT.
rewrite Hsame.
apply same_on_SEC_same_target in Hsame.
now rewrite Hsame.
Qed.

Lemma target_inside_SEC : forall config,
  no_Majority config ->
  (dist (target (!! config)) (R2.center (SEC (support (!! config))))
   <= radius (SEC (support (!! config))))%R.
Proof.
Opaque Rmax. Opaque dist. Opaque middle.
intros config Hmaj. unfold target.
assert (Hlen := no_Majority_on_SEC_length Hmaj).
destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 [| pt3 [| pt l]]]] eqn:Hsec;
simpl in Hlen; omega || clear Hlen; [| |].
+ rewrite R2_dist_defined_2.
  rewrite SEC_on_SEC, Hsec, radius_is_max_dist, SEC_dueton.
  simpl. unfold max_dist. simpl. etransitivity; apply Rmax_l.
+ rewrite SEC_on_SEC, Hsec. unfold target_triangle.
  destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
  - apply barycenter_3_pts_inside_SEC.
  - rewrite classify_triangle_Isosceles_spec in Htriangle.
    assert (Hin : InA equiv vertex (on_SEC (support (!! config)))).
    { rewrite Hsec. decompose [and or] Htriangle; subst; intuition. }
    unfold on_SEC in Hin. rewrite filter_InA in Hin; autoclass. destruct Hin as [_ Hin].
    rewrite on_circle_true_iff, SEC_on_SEC, Hsec in Hin. now rewrite Hin.
  - unfold opposite_of_max_side. unfold Rle_bool.
    do 2 match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
    match goal with |- (dist ?pt _ <= _)%R =>
      assert (Hin : InA equiv pt (on_SEC (support (!! config)))) by (rewrite Hsec; intuition);
      unfold on_SEC in Hin; rewrite filter_InA in Hin; autoclass; []; rewrite <- Hsec, <- SEC_on_SEC;
      destruct Hin as [_ Hin]; rewrite on_circle_true_iff in Hin; now rewrite Hin
    end.
+ rewrite R2_dist_defined_2.
  rewrite SEC_on_SEC, Hsec, radius_is_max_dist.
  transitivity (dist pt1 (R2.center (SEC (pt1 :: pt2 :: pt3 :: pt :: l)))).
  - apply dist_pos.
  - apply max_dist_le. intuition.
Transparent Rmax. Transparent middle.
Qed.

(** If the target is on the SEC, then we are in a non-equilateral triangle case. *)
Lemma target_on_SEC_cases : forall config, no_Majority config ->
  (on_circle (SEC (support (!! config))) (target (!! config)) = true <->
  triangle_case config /\ ~equilateral_case config).
Proof.
intros config Hmaj. split.
* intro Htarget.
  rewrite SEC_on_SEC in Htarget. unfold target in *.
  assert (Hlen := no_Majority_on_SEC_length Hmaj).
  assert (Hnodup : NoDupA equiv (on_SEC (support (!! config)))) by apply on_SEC_NoDupA, support_NoDupA.
  destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec;
  simpl in Hlen; omega || clear Hlen; [| |].
  + exfalso.
    assert (Heq : equiv pt1 pt2).
    { rewrite SEC_dueton in Htarget.
      rewrite on_circle_true_iff in Htarget.
      rewrite SEC_on_SEC, Hsec, SEC_dueton in Htarget.
      cbn in Htarget.
      rewrite R2_dist_defined_2 in Htarget.
      rewrite <- dist_defined. lra. }
    inversion_clear Hnodup. intuition.
  + unfold target_triangle in *. destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
    - exfalso.
      rewrite triangle_barycenter_inside in Htarget; try discriminate; [].
      inversion_clear Hnodup. intuition.
    - get_case config. split; trivial. intro Habs.
      unfold triangle_case, equilateral_case in *.
      destruct Habs as [_ [? [? [? [Hperm Hequilateral]]]]].
      rewrite Hsec, PermutationA_Leibniz in Hperm.
      rewrite <- (classify_triangle_compat Hperm), Htriangle in Hequilateral.
      discriminate.
    - get_case config. split; trivial. intro Habs.
      unfold triangle_case, equilateral_case in *.
      destruct Habs as [_ [? [? [? [Hperm Hequilateral]]]]].
      rewrite Hsec, PermutationA_Leibniz in Hperm.
      rewrite <- (classify_triangle_compat Hperm), Htriangle in Hequilateral.
      discriminate.
  + exfalso.
    setoid_rewrite SEC_on_SEC in Htarget at 2. rewrite Hsec in Htarget.
    rewrite center_on_circle in Htarget.
    rewrite SEC_zero_radius_incl_singleton in Htarget. destruct Htarget as [pt Hpt].
    assert (Heq : pt1 == pt2).
    { transitivity pt.
      - specialize (Hpt pt1). cbn in Hpt. intuition.
      - specialize (Hpt pt2). cbn in Hpt. intuition. }
    inversion_clear Hnodup. intuition.
* intros [[_ [ptx [pty [ptz Hperm]]]] Hequilateral].
  assert (Hlen := PermutationA_length Hperm).
  destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec; try discriminate; [].
  destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
  + get_case config. contradiction.
  + erewrite (isosceles_target config ltac:(now rewrite Hsec)); try eassumption; [].
    eapply proj2. rewrite <- (filter_InA _). unfold on_SEC in Hsec. rewrite Hsec.
    rewrite classify_triangle_Isosceles_spec in Htriangle.
    decompose [and or] Htriangle; subst; intuition.
  + erewrite (scalene_target config ltac:(now rewrite Hsec)); try eassumption; [].
    eapply proj2. rewrite <- (filter_InA _). unfold on_SEC in Hsec. rewrite Hsec.
    unfold opposite_of_max_side.
    do 2 match goal with |- context[Rle_bool ?x ?y] => destruct (Rle_bool x y) end; intuition.
Qed.

Lemma target_on_SEC_already_occupied : forall config,
  no_Majority config ->
  on_circle (SEC (support (!! config))) (target (!! config)) = true ->
  InA equiv (target (!! config)) (support (!! config)).
Proof.
intros config Hmaj Htarget.
apply target_on_SEC_cases in Htarget; trivial.
destruct Htarget as [[_ [ptx [pty [ptz Hperm]]]] Hequilateral].
assert (Hlen := PermutationA_length Hperm).
destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec;
simpl in Hlen; discriminate || clear Hlen; [].
unfold target. rewrite Hsec. unfold target_triangle.
destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
+ get_case config. contradiction.
+ rewrite classify_triangle_Isosceles_spec in Htriangle.
  decompose [and or] Htriangle; subst; clear Htriangle;
  match goal with |- InA equiv ?pt (support (!! config)) =>
    assert (Hin : InA equiv pt (pt1 :: pt2 :: pt3 :: nil)) by intuition;
    rewrite <- Hsec in Hin; unfold on_SEC in Hin; now rewrite filter_InA in Hin; autoclass
  end.
+ unfold opposite_of_max_side. unfold Rle_bool.
  do 2 match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
  match goal with |- InA equiv ?pt (support (!! config)) =>
    assert (Hin : InA equiv pt (pt1 :: pt2 :: pt3 :: nil)) by intuition;
    rewrite <- Hsec in Hin; unfold on_SEC in Hin; now rewrite filter_InA in Hin; autoclass
  end.
Qed.

(** ***  Generic results about the [SEC] after one round **)

Lemma incl_next : forall da (config : configuration),
    (inclA equiv (support (!! (round gatherR2 da config)))
                 ((target (!! config)) :: (support (!! config)))).
Proof.
intros da config.
red.
intros x Hin.
rewrite support_elements in Hin.
apply elements_spec in Hin.
destruct Hin as [_ Hin].
destruct (x =?= target (!! config)) as [Heq | Heq]; try (now left); [].
right.
rewrite support_elements.
apply elements_spec.
split; trivial; [].
destruct (le_lt_dec ((!! config)[x]) 0); trivial; [].
exfalso.
destruct (@increase_move gatherR2 config da x)
  as [r_moving [Hdest_rmoving Hrmoving]].
* omega.
* destruct (le_lt_dec 2 (length (support (max (!! config))))) as [Hle | Hlt].
  + rewrite destination_is_target in Hdest_rmoving.
    - now elim Heq.
    - unfold no_Majority. now rewrite size_spec.
    - rewrite moving_spec. intro Habs. apply Hrmoving. now rewrite Habs.
  + assert ((support (max (!! config))) = x :: nil).
    { destruct (support (max (!! config))) as [| pt [| ? ?]] eqn:Heq'; cbv in Hlt; try omega.
      + now destruct (support_max_non_nil config).
      + get_case config.
        rewrite (@round_simplify_Majority _ _ pt Hcase r_moving) in Hdest_rmoving.
        destruct (da.(activate) config r_moving).
        - now rewrite <- Hdest_rmoving.
        - assert (H := pos_in_config config origin r_moving).
          rewrite Hdest_rmoving in H. unfold In in H. omega. }
    assert (Hperm : PermutationA equiv (support (max (!! config))) (x :: nil)) by now rewrite H.
    rewrite support_1 in Hperm.
    destruct Hperm as [_ Hperm].
    destruct (max_2_mult (!! config) x); omega.
Qed.

Lemma incl_clean_next : forall da config,
  is_clean (!! config) = true ->
  inclA equiv (support (!! (round gatherR2 da config)))
              (target (!! config) :: on_SEC (support (!! config))).
Proof.
intros da config H.
transitivity ((target (!! config)) :: (support (!! config))).
- apply incl_next.
- rewrite inclA_Leibniz.
  apply incl_cons.
  + now left.
  + now rewrite <- inclA_Leibniz, <- is_clean_spec.
Qed.

Lemma next_SEC_enclosed : forall da config,
  no_Majority config -> 
  enclosing_circle (SEC (support (!! config))) (support (!! (round gatherR2 da config))).
Proof.
intros da config Hmaj pt Hin.
rewrite <- InA_Leibniz in Hin. change eq with equiv in Hin. rewrite support_In in Hin. unfold In in Hin.
rewrite spect_from_config_spec, config_list_spec in Hin.
induction names as [| id l]; try (simpl in *; omega); [].
cbn -[get_location] in Hin. R2dec_full in Hin; try (now apply IHl); [].
rewrite <- Heq, (round_simplify _ _ id); trivial; [].
destruct (da.(activate) config id).
* assert (Hmax := Hmaj). rewrite no_Majority_equiv in Hmax. destruct Hmax as [pt1 [pt2 [lmax Hmax]]].
  cbn zeta. rewrite Hmax.
  destruct (is_clean (!! config)).
  + now apply target_inside_SEC.
  + destruct (mem equiv_dec (get_location (config id)) (SECT (!! config))) eqn:Hmem.
    - apply SEC_spec1. rewrite <- InA_Leibniz.
      change eq with equiv. rewrite support_In. apply pos_in_config.
    - now apply target_inside_SEC.
* apply SEC_spec1. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config.
Qed.

(** ***  Lemmas about the dirty cases  **)

(* To prove dirty_next_on_SEC_same below, we first prove that any point on the SEC does not move. *)
Lemma dirty_next_still_on_SEC : forall da config id,
  no_Majority config ->
  is_clean (!! config) = false ->
  on_circle (SEC (support (!! config))) (get_location (config id)) = true ->
  round gatherR2 da config id == config id.
Proof.
intros da config id Hmaj Hclean Hcircle.
rewrite (round_simplify_dirty da Hmaj Hclean id).
destruct (da.(activate) config id); try reflexivity; [].
destruct (mem equiv_dec (get_location (config id)) (SECT (!! config))) eqn:Hmem; try reflexivity; [].
rewrite mem_false_iff in Hmem. elim Hmem.
unfold SECT. right. unfold on_SEC. rewrite filter_InA; autoclass; [].
split; trivial; [].
rewrite support_In. apply pos_in_config.
Qed.

Lemma dirty_next_SEC_same : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  SEC (support (!! (round gatherR2 da config))) = SEC (support (!! config)).
Proof.
intros da config Hmaj Hclean.
assert (HonSEC : forall id, List.In (get_location (config id)) (on_SEC (support (!! config))) ->
                   round gatherR2 da config id == config id).
{ intros id Hid. rewrite (round_simplify_dirty da Hmaj Hclean id).
  destruct (da.(activate) config id); try reflexivity; [].
  assert (Heq : mem equiv_dec (get_location (config id)) (SECT (!! config)) = true).
  { rewrite mem_true_iff. right. now apply InA_Leibniz. }
  now rewrite Heq. }
apply enclosing_same_on_SEC_is_same_SEC.
+ now apply next_SEC_enclosed.
+ intros pt Hin.
  assert (Hid : exists id, get_location (config id) == pt).
  { unfold on_SEC in Hin. setoid_rewrite List.filter_In in Hin. destruct Hin as [Hin Hsec].
    rewrite <- InA_Leibniz in Hin. change eq with equiv in Hin.
    now rewrite support_In, spect_from_config_In in Hin. }
  destruct Hid as [id Hid]. rewrite <- Hid in *.
  rewrite <- HonSEC; trivial. rewrite <- InA_Leibniz. change eq with equiv.
  rewrite support_In. apply pos_in_config.
Qed.

Lemma dirty_next_on_SEC_same : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  PermutationA equiv (on_SEC (support (!! (round gatherR2 da config)))) (on_SEC (support (!! config))).
Proof.
intros da config Hmaj Hclean. apply (NoDupA_equivlistA_PermutationA _).
* unfold on_SEC. apply (Preliminary.NoDupA_filter_compat _), support_NoDupA.
* unfold on_SEC. apply (Preliminary.NoDupA_filter_compat _), support_NoDupA.
* intro pt.
  unfold on_SEC in *. rewrite dirty_next_SEC_same; trivial; [].
  do 2 (rewrite filter_InA; autoclass); [].
  split; intros [Hin Hcircle]; split; trivial; [|].
  + rewrite support_In, spect_from_config_In in Hin. destruct Hin as [id Hid].
    rewrite (round_simplify_dirty da Hmaj Hclean id) in Hid.
    destruct (da.(activate) config id).
    - destruct (mem equiv_dec (get_location (config id)) (SECT (!! config))) eqn:Hmem.
      -- rewrite <- Hid, support_In. apply pos_in_config.
      -- rewrite <- Hid in *. clear Hid pt.
         now apply target_on_SEC_already_occupied.
    - rewrite <- Hid, support_In. apply pos_in_config.
  + rewrite support_In, spect_from_config_In in Hin. destruct Hin as [id Hid].
    rewrite <- Hid in *.
    assert (Heq : round gatherR2 da config id == config id) by now apply dirty_next_still_on_SEC.
    rewrite <- Heq, support_In. apply pos_in_config.
Qed.

(** ***  Lemma about the majority case  **)

(* Next lemmas taken from the gathering algo in R. *)
(** When there is a majority tower, it grows and all other towers wither. **)
Theorem Majority_grow :  forall pt config da, MajTower_at pt config ->
  (!! config)[pt] <= (!! (round gatherR2 da config))[pt].
Proof.
intros pt config da Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; cbn -[get_location].
+ reflexivity.
+ destruct (da.(activate) config id); cbn -[get_location].
  - change (get_location pt =?= pt) with (pt =?= pt). R2dec.
    R2dec_full; apply le_n_S + apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall config da pt, MajTower_at pt config ->
  forall pt', pt <> pt' -> (!! (round gatherR2 da config))[pt'] <= (!! config)[pt'].
Proof.
intros config da pt Hmaj pt' Hdiff.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite spect_from_config_spec, config_list_spec.
induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (da.(activate) config id); simpl.
  - R2dec_full; try contradiction; []. R2dec_full; try apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.

(** Whenever there is a majority tower, it remains forever so. *)
Theorem MajTower_at_forever : forall pt config da,
  MajTower_at pt config -> MajTower_at pt (round gatherR2 da config).
Proof.
intros pt config da Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! config)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
- eapply Majority_grow; eauto.
Qed.

Lemma solve_measure_clean : forall da config,
  no_Majority config ->
  moving gatherR2 da config <> nil ->
  target (!! (round gatherR2 da config)) = target (!! config) ->
  measure_clean (!! (round gatherR2 da config)) < measure_clean (!! config).
Proof.
intros da config Hmaj Hmoving Htarget.
unfold measure_clean. rewrite Htarget.
assert (Hle := multiplicity_le_nG (target (!! config)) (round gatherR2 da config)).
cut ((!! config)[target (!! config)] < (!! (round gatherR2 da config))[target (!! config)]).
+ omega.
+ rewrite increase_move_iff.
  apply not_nil_In in Hmoving. destruct Hmoving as [gmove Hmove].
  exists gmove. split.
  - now apply destination_is_target.
  - intro Habs. apply no_info in Habs. revert Habs.
    change (round gatherR2 da config gmove =/= config gmove).
    now rewrite <- moving_spec.
Qed.

Opaque spect_from_config.
(* Opaque R2_Setoid. *)

Lemma solve_measure_dirty : forall da (config : configuration),
  moving gatherR2 da config <> nil ->
  no_Majority config ->
  is_clean (!! config) = false ->
  no_Majority (round gatherR2 da config) ->
  is_clean (!! (round gatherR2 da config)) = false ->
  measure_dirty (!! (round gatherR2 da config)) < measure_dirty (!! config).
Proof.
intros da config Hmoving Hmaj Hclean Hmaj' Hclean'.
assert (HsameSEC := dirty_next_on_SEC_same da Hmaj Hclean).
assert (Htarget := same_on_SEC_same_target _ _ HsameSEC).
assert (HsameSECT := same_on_SEC_same_SECT _ _ HsameSEC).
unfold measure_dirty.
assert (HlenG : SECT_cardinal (!! (round gatherR2 da config)) <= nG) by apply SECT_cardinal_le_nG.
cut (SECT_cardinal (!! config) < SECT_cardinal (!! (round gatherR2 da config))); try omega; [].
assert (Hlt : (!! config)[target (!! config)] < (!! (round gatherR2 da config))[target (!! config)]).
{ rewrite increase_move_iff.
  apply not_nil_In in Hmoving. destruct Hmoving as [gmove Hmove].
  exists gmove. split.
  - now apply destination_is_target.
  - intro Habs. apply no_info in Habs. revert Habs.
    change (round gatherR2 da config gmove =/= config gmove).
    now rewrite <- moving_spec. }
unfold SECT_cardinal.
pose (f s x := if InA_dec equiv_dec x (SECT s) then true else false).
assert (Hext : forall x, f (!! (round gatherR2 da config)) x = f (!! config) x).
{ intro pt. unfold f.
  destruct (InA_dec equiv_dec pt (SECT (!! config))) as [Htest1 | Htest1],
           (InA_dec equiv_dec pt (SECT (!! (round gatherR2 da config)))) as [Htest2 | Htest2]; trivial.
  - elim Htest2. now rewrite HsameSECT.
  - elim Htest1. now rewrite <- HsameSECT. }
unfold f in Hext.
rewrite (filter_extensionality_compat _ _ Hext). clear Hext.
pose (f_target := fun x => if equiv_dec x (target (!! config)) then true else false).
pose (f_out_target := fun x => if InA_dec equiv_dec x (SECT (!! config)) then negb (f_target x) else false).
(* assert (Proper (equiv ==> eq) f_target).
{ intros ? ? Heq. simpl in Heq. subst. unfold f_target. R2dec_full. } *)
assert (Hext : forall x, f (!! config) x = f_target x || f_out_target x).
{ intro pt. unfold f, f_out_target, f_target. simpl. R2dec_full; intuition. }
unfold f in Hext. setoid_rewrite (filter_extensionality_compat _ _ Hext). clear Hext f.
assert (Hdisjoint : forall m x, In x m -> f_target x && f_out_target x = false).
{ intros m x Hin.
  destruct (f_target x) eqn:Heq1, (f_out_target x) eqn:Heq2; trivial.
  exfalso. unfold f_out_target, f_target in *. clear f_target f_out_target.
  R2dec_full in Heq1; try discriminate; [].
  rewrite Heq in Heq2.
  destruct (InA_dec equiv_dec (target (!! config)) (SECT (!! config))); discriminate. }
setoid_rewrite filter_disjoint_or_union; try (try (intros ? ? Heq; rewrite Heq); autoclass); [].
do 2 rewrite cardinal_union.
unfold f_target. setoid_rewrite cardinal_filter_is_multiplicity.
assert (Heq : @equiv spectrum spectrum_Setoid (filter f_out_target (!! (round gatherR2 da config)))
                                (filter f_out_target (!! config))).
{ intro pt. repeat rewrite filter_spec; try (now intros ? ? Heq; rewrite Heq); [].
  destruct (f_out_target pt) eqn:Htest; trivial.
  rewrite round_simplify_dirty; trivial. symmetry.
  (* by induction on the list of robot names *)
  do 2 rewrite spect_from_config_spec, config_list_spec.
  induction names as [| id l].
  * reflexivity.
  * simpl. R2dec_full.
    + rewrite Heq. destruct (da.(activate) config id) eqn:Hactive.
      - assert (Hmem : mem equiv_dec pt (SECT (!! config)) = true).
        { rewrite mem_true_iff. unfold f_out_target in Htest.
          destruct (InA_dec equiv_dec pt (SECT (!! config))) as [Hin | Hin]; trivial; discriminate. }
        simpl in Hmem. rewrite Hmem. destruct_match; try contradiction; []. f_equal. apply IHl.
      - R2dec. f_equal. apply IHl.
    + destruct (da.(activate) config id) eqn:Hactive.
      - change (@eq R2) with equiv.
        destruct_match_eq Hmem.
        ++ R2dec_full; contradiction || apply IHl.
        ++ R2dec_full.
           -- exfalso.
              unfold f_out_target in Htest.
              destruct (InA_dec equiv_dec pt (SECT (!! config))); try discriminate; [].
              rewrite negb_true_iff in Htest.
              unfold f_target in Htest. symmetry in Heq.
              R2dec_full in Htest; discriminate || contradiction.
           -- apply IHl.
      - R2dec. apply IHl. }
rewrite Heq.
omega.
Qed.

(** ***  An invalid configuration cannot appear  **)

(* For [never_invalid] *)
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

(* For [never_invalid] *)
Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace nG with (nG + nB) by (simpl; omega).
rewrite <- (cardinal_spect_from_config config origin).
rewrite <- (add_remove_id pt1 (!! config) (reflexivity _)) at 4.
rewrite cardinal_add.
rewrite <- (add_remove_id pt2 (!! config) (reflexivity _)) at 6.
rewrite remove_add_comm, cardinal_add; trivial.
rewrite <- (add_remove_id pt3 (!! config) (reflexivity _)) at 8.
rewrite remove_add_comm, remove_add_comm, cardinal_add; trivial.
omega.
Qed.

(* Taken from the gathering in R.
   Any non-invalid config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_invalid : forall da config, ~invalid config -> ~invalid (round gatherR2 da config).
Proof.
intros da config Hok.
(* Three cases for the robogram *)
destruct (support (max (!! config))) as [| pt [| pt' l']] eqn:Hmaj.
- assert (round gatherR2 da config == config).
  { rewrite round_simplify; cbv zeta; try rewrite Hmaj.
    intro id. now destruct (da.(activate) config id). }
  now rewrite H.
  (* There is a majority tower *)
- apply Majority_not_invalid with pt.
  rewrite <- MajTower_at_equiv in *.
  apply (@MajTower_at_forever pt config da) in Hmaj.
  assumption.
- get_case config.
  clear pt pt' l' Hmaj. rename Hmaj0 into Hmaj.
  (* A robot has moved otherwise we have the same configuration before and it is invalid. *)
  assert (Hnil := no_moving_same_config gatherR2 da config).
  destruct (moving gatherR2 da config) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    clear Hnil.
    assert (Hmove : List.In rmove (moving gatherR2 da config)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round robogram config *)
    assert (Hinvalid := Habs). destruct Habs as [HnG [HsizeG[pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ get_location (round gatherR2 da config rmove) == pt).
    { assert (Hperm : Permutation (support (!! (round gatherR2 da config))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
        + rewrite <- NoDupA_Leibniz. change eq with equiv. apply support_NoDupA.
        + now rewrite <- size_spec, invalid_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz. change eq with equiv. rewrite support_spec.
            unfold In. rewrite Hpt1. apply Exp_prop.div2_not_R0. apply HsizeG.
          - inversion H; (now inversion H0) || subst. rewrite <- InA_Leibniz. change eq with equiv.
            rewrite support_spec. unfold In. rewrite Hpt2. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hpt : List.In (get_location (round gatherR2 da config rmove)) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm, <- InA_Leibniz. change eq with equiv. rewrite support_In. apply pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, List.In g (moving gatherR2 da config) -> get_location (round gatherR2 da config g) == pt).
    { intros id Hid. rewrite <- Hrmove_pt. apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 nG) <= (!! config)[pt']).
    { transitivity ((!! (round gatherR2 da config))[pt']).
      - decompose [and or] Hpt; subst; omega.
      - generalize (@increase_move_iff config da pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. intro Habs. apply Hid2. now rewrite Habs. }
    assert (Hlt : forall p, p <> pt' -> (!! config)[p] < div2 nG).
    { assert (Hpt'_in : In pt' (!! config)).
      { unfold In. eapply lt_le_trans; try eassumption. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hle := not_invalid_no_majority_size Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl nG).
      destruct (@towers_elements_3 config pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 nG); try assumption. apply Exp_prop.div2_not_R0. apply HsizeG.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total config Hp Hdiff13 Hdiff23); [].
        unfold In in Hpt3_in. rewrite <- ?Even.even_equiv in *.
        rewrite (even_double nG); auto. unfold Nat.double. omega. }
    assert (Hmaj' : MajTower_at pt' config).
    { intros x Hx. apply lt_le_trans with (div2 nG); trivial. now apply Hlt. }
    apply MajTower_at_equiv in Hmaj'.
    red in Hmaj.
    rewrite size_spec in Hmaj.
    rewrite Hmaj' in Hmaj.
    simpl in Hmaj.
    omega.
Qed.

(** ***  Lemmas about the diameter case  **)


Lemma diameter_clean_support : forall config ptx pty,
  ~invalid config ->
  no_Majority config ->
  is_clean (!! config) = true ->
  on_SEC (support (!! config)) = ptx :: pty :: nil ->
  PermutationA equiv (support (!! config)) (middle ptx pty :: ptx :: pty :: nil).
Proof.
intros config ptx pty Hinvalid hmax Hclean HonSEC.
assert (Htarget : target (!! config) = middle ptx pty) by (apply (diameter_target); auto).
apply (NoDupA_inclA_length_PermutationA _).
- apply support_NoDupA.
- assert (Hdiff : ptx <> pty).
  { assert (Hnodup : NoDupA equiv (on_SEC (support (!! config)))).
    { unfold on_SEC in HonSEC.
      apply Preliminary.NoDupA_filter_compat;autoclass.
      apply support_NoDupA. }
    rewrite HonSEC in Hnodup.
    inversion Hnodup as [ | ? ? h1 h2]; subst.
    intro abs; subst.
    apply h1; now left. }
  constructor.
  + apply middle_diff.
    assumption.
  + rewrite <- HonSEC. apply on_SEC_NoDupA, support_NoDupA.
- intros x Hin.
  rewrite is_clean_spec in Hclean. apply Hclean in Hin.
  now rewrite <- Htarget, <- HonSEC.
- rewrite <- size_spec. now apply not_invalid_no_majority_size.
Qed.

Lemma diameter_round_same : forall da config ptx pty,
  no_Majority (round gatherR2 da config) ->
  PermutationA equiv (support (!! config)) (middle ptx pty :: ptx :: pty :: nil) ->
  PermutationA equiv (support (!! (round gatherR2 da config)))
                        (middle ptx pty :: ptx :: pty :: nil).
Proof.
intros da config ptx pty Hmaj Hperm.
assert (Htarget : target (!! config) = middle ptx pty).
{ assert (HonSEC : PermutationA equiv (on_SEC (support (!! config))) (ptx :: pty :: nil)).
  { rewrite Hperm. rewrite on_SEC_middle_diameter, on_SEC_dueton; try reflexivity; [].
    assert (Hnodup : NoDupA equiv (support (!! config))) by apply support_NoDupA.
    rewrite Hperm in Hnodup. inversion_clear Hnodup. inversion_clear H0. intuition. }
  destruct (on_SEC (support (!! config))) as [| ? [| ? [| ? ?]]] eqn:Hsec;
  try (apply PermutationA_length in HonSEC; discriminate); [].
  apply (PermutationA_2 _) in HonSEC. destruct HonSEC as [[Heq1 Heq2] | [Heq1 Heq2]]; rewrite <- Heq1, <- Heq2.
  - now apply diameter_target.
  - rewrite middle_comm. now apply diameter_target. }
apply (NoDupA_inclA_length_PermutationA _).
- apply support_NoDupA.
- rewrite <- Hperm.
  apply support_NoDupA.
- assert (Hincl:= incl_next da config).
  rewrite Hperm in Hincl.
  rewrite Htarget in Hincl.
  apply (inclA_cons_InA _) in Hincl; auto.
- simpl length at 1.
  rewrite <- size_spec.
  apply not_invalid_no_majority_size; trivial.
  apply never_invalid.
  rewrite invalid_equiv.
  intros [_ Habs].
  rewrite size_spec, Hperm in Habs.
  simpl in Habs; omega.
Qed.


Lemma diameter_next_target_same : forall da config,
  ~invalid config ->
  clean_diameter_case config ->
  no_Majority (round gatherR2 da config) ->
  target (!! (round gatherR2 da config)) = target (!! config).
Proof.
intros da config Hinvalid Hcleandiam Hmaj'.
destruct Hcleandiam as [[Hmaj [pt1 [pt2 Htwocol]]] Hclean].
apply PermutationA_length in Htwocol.
unfold target.
destruct (on_SEC (support (!! config))) as [| ptx [| pty [| ptz [| ptt ?]]]] eqn:Hsec; try discriminate; [].
assert (Hincl := incl_next da config).
assert (Htarget : target (!!config) = middle ptx pty) by (apply diameter_target; auto).
assert (Hperm := @diameter_clean_support config ptx pty Hinvalid Hmaj Hclean Hsec).
assert (Hperm' : PermutationA equiv (support (!! (round gatherR2 da config)))
                                    (middle ptx pty :: ptx :: pty :: nil)).
{ apply (NoDupA_inclA_length_PermutationA _).
  - apply support_NoDupA.
  - rewrite <- Hperm.
    apply support_NoDupA.
  - apply (inclA_cons_InA _) with (middle ptx pty).
    + intuition.
    + rewrite <- Hperm, <- Htarget. apply Hincl.
  - simpl length at 1. rewrite <- size_spec. now apply not_invalid_no_majority_size, never_invalid. }
assert (HpermSEC' : PermutationA equiv (on_SEC (support (!! (round gatherR2 da config))))
                                       (ptx :: pty :: nil)).
{ rewrite Hperm'. rewrite on_SEC_middle_diameter.
  - now rewrite on_SEC_dueton.
  - assert (Hnodup : NoDupA equiv (middle ptx pty :: ptx :: pty :: nil)).
    { rewrite <- Hperm. apply support_NoDupA. }
    inversion_clear Hnodup. inversion_clear H0. intuition. }
assert (Hlen : length (on_SEC (support (!! (round gatherR2 da config)))) = 2) by now rewrite HpermSEC'.
destruct (on_SEC (support (!! (round gatherR2 da config))))
  as [| ptx' [| pty' [| ? ?]]] eqn:Hsec'; cbn in Hlen; try discriminate.
do 2 rewrite SEC_on_SEC, ?Hsec, ?Hsec', SEC_dueton. simpl.
apply (PermutationA_2 _) in HpermSEC'.
destruct HpermSEC' as [[Heq1 Heq2] | [Heq1 Heq2]]; rewrite Heq1, Heq2; trivial || apply middle_comm.
Qed.

Lemma clean_diameter_next_maj_or_diameter : forall da config ptx pty,
  ~invalid config ->
  no_Majority config ->
  is_clean (!! config) = true ->
  on_SEC (support (!! config)) = ptx :: pty :: nil ->
  (exists pt, MajTower_at pt (round gatherR2 da config))
  \/ no_Majority (round gatherR2 da config)
     /\ PermutationA equiv (on_SEC (support (!! (round gatherR2 da config)))) (ptx :: pty :: nil).
Proof.
intros da config ptx pty Hinvalid Hmaj Hclean Hsec.
assert (Hperm := diameter_clean_support Hinvalid Hmaj Hclean Hsec).
destruct (support (max (!! (round gatherR2 da config)))) as [| pt [| ? ?]] eqn:Hmax'.
- rewrite support_nil, max_empty, <- support_nil in Hmax'.
  now elim (support_non_nil _ Hmax').
- left. exists pt.
  rewrite MajTower_at_equiv. now rewrite Hmax'.
- right.
  assert (Hmaj' : no_Majority (round gatherR2 da config)).
  { eapply make_no_Majority. rewrite Hmax'. reflexivity. }
  split; trivial; [].
  assert (Htarget := diameter_target config Hsec).
  assert (Hperm' := diameter_round_same da Hmaj' Hperm).
  rewrite Hperm'.
  rewrite on_SEC_middle_diameter.
  + now rewrite on_SEC_dueton.
  + assert (Hnodup : NoDupA equiv (on_SEC (support (!! config)))).
    { apply on_SEC_NoDupA, support_NoDupA. }
    rewrite Hsec in Hnodup. inversion_clear Hnodup. intuition.
Qed.

(** ***  Lemmas about the triangle cases  **)


(** ****  Lemmas about the equilateral triangle case  **)

Lemma SEC_3_to_2: forall da config ptx pty ptz bary pt ptdiam,
  InA equiv pt (ptx :: pty :: ptz :: nil) ->
  InA equiv ptdiam (ptx :: pty :: ptz :: nil) ->
  pt<> ptdiam ->
  PermutationA equiv (on_SEC (support (!! config))) (ptx :: pty :: ptz :: nil) ->
  PermutationA equiv (on_SEC (support (!! (round gatherR2 da config)))) (bary :: ptdiam :: nil) ->
  classify_triangle ptx pty ptz = Equilateral ->
  bary == (barycenter_3_pts ptx pty ptz) ->
  ~ InA equiv pt (support (!! (round gatherR2 da config))).
Proof.
intros da config ptx pty ptz bary pt ptdiam hIn_pt hIn_ptdiam hneq_pt_ptdiam Hsec Hsec' Htriangle heq_bary.
intro abs.
assert (h_bary:=@same_dist_vertex_notin_sub_circle ptdiam pt bary). 

assert (h_radius_pt : radius (SEC (ptx :: pty :: ptz :: nil)) =  dist bary pt).
{ rewrite InA_Leibniz in hIn_pt.
  simpl in hIn_pt.
  decompose [or False] hIn_pt;subst.
  - generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity.
  - assert (hperm:PermutationA equiv (ptx :: pt :: ptz :: nil) (pt :: ptx :: ptz :: nil)) by permut_3_4.
    rewrite ?hperm in *.
    generalize hperm; intro hperm'.
    apply PermutationA_Leibniz in hperm'.
    rewrite (classify_triangle_compat hperm') in Htriangle.
    rewrite (barycenter_3_pts_compat hperm') in heq_bary.
    generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity.
  - assert (hperm:PermutationA equiv (ptx :: pty :: pt :: nil) (pt :: ptx :: pty :: nil)) by permut_3_4.
    rewrite ?hperm in *.
    generalize hperm;intro hperm'.
    apply PermutationA_Leibniz in hperm'.
    rewrite (classify_triangle_compat hperm') in Htriangle.
    rewrite (barycenter_3_pts_compat hperm') in heq_bary.
    generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity. }
assert (h_radius_ptdiam : radius (SEC (ptx :: pty :: ptz :: nil)) =  dist bary ptdiam).
{ rewrite InA_Leibniz in hIn_ptdiam.
  simpl in hIn_ptdiam.
  decompose [or False] hIn_ptdiam;subst.
  - generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity.
  - assert (hperm:PermutationA equiv (ptx :: ptdiam :: ptz :: nil) (ptdiam :: ptx :: ptz :: nil)) by permut_3_4.
    rewrite ?hperm in *.
    generalize hperm;intro hperm'.
    apply PermutationA_Leibniz in hperm'.
    rewrite (classify_triangle_compat hperm') in Htriangle.
    rewrite (barycenter_3_pts_compat hperm') in heq_bary.
    generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity.
  - assert (hperm:PermutationA equiv (ptx :: pty :: ptdiam :: nil) (ptdiam :: ptx :: pty :: nil)) by permut_3_4.
    rewrite ?hperm in *.
    generalize hperm;intro hperm'.
    apply PermutationA_Leibniz in hperm'.
    rewrite (classify_triangle_compat hperm') in Htriangle.
    rewrite (barycenter_3_pts_compat hperm') in heq_bary.
    generalize (@equilateral_SEC _ _ _ Htriangle).
    intro h_sec_xyz.
    rewrite <- heq_bary in h_sec_xyz.
    rewrite h_sec_xyz.
    simpl.
    reflexivity. }
assert (dist ptdiam bary = dist pt bary).
{ setoid_rewrite dist_sym.
  rewrite <- h_radius_ptdiam , <- h_radius_pt.
  reflexivity. }
apply hneq_pt_ptdiam.
apply h_bary;auto. 
assert (h_diameter_after : SEC (support (!! (round gatherR2 da config)))
                           = {| R2.center := middle bary ptdiam; radius := / 2 * dist bary ptdiam |}).
{ assert (Hlen := PermutationA_length Hsec').
  destruct (on_SEC (support (!! (round gatherR2 da config))))
    as [| x [ | y [|?] ]] eqn:Heq; simpl in Hlen; omega || clear Hlen.
  apply PermutationA_2 in Hsec'; autoclass.
  destruct Hsec' as [ [h1 h2] | [h2 h1]].
  - apply on_SEC_pair_is_diameter.
    rewrite Heq.
    hnf in h1, h2.
    now subst.
  - rewrite middle_comm.
    rewrite dist_sym.
    apply on_SEC_pair_is_diameter.
    rewrite Heq.
    hnf in h1, h2.
    now subst. }
assert (dist_pt1_mid_is_radius: dist bary (middle bary ptdiam)
                                = radius (SEC (support (!! (round gatherR2 da config))))).
{ rewrite h_diameter_after. simpl radius. now rewrite R2dist_middle. }

rewrite dist_pt1_mid_is_radius.
rewrite radius_is_max_dist.
replace (middle bary ptdiam) with (R2.center (SEC (support (!! (round gatherR2 da config))))).
+ rewrite dist_sym.
  apply max_dist_le.
  now rewrite InA_Leibniz in abs.
+ now rewrite h_diameter_after.
Qed.

(* Extracting nodupA and ~InA consequences (in terms of <>) *)
Ltac inv_notin H :=
  match type of H with
  | ~ List.In ?x nil => clear H
  | ~ InA (@equiv R2 _) ?x ?l =>
    let h := fresh H in
    assert (h:~ List.In x l); 
    [ rewrite <- InA_Leibniz; assumption | inv_notin h ]
  | ~ List.In ?x ?l =>
    apply not_in_cons in H;
    let h := fresh H in
    let heq := fresh "heq" in
    destruct H as [heq h];
    try inv_notin h
  end.

Ltac inv_nodup H :=
  lazymatch type of H with
  | NoDupA (@equiv R2 _) nil => clear H
  | NoDupA (@equiv R2 _) (?x::nil) => clear H
  | NoDupA (@equiv R2 _) (?x::?y::?l) =>
    let x := fresh "x" in
    let l := fresh "l" in
    let C := fresh "h_notin" in
    let D := fresh "h_nodup" in
    inversion H as [|x l C D [E F]];
    match type of E with
    | ?x = _ => subst x
    end;
    match type of F with
    | ?x = _ => subst x
    end;
    inv_notin C;
    inv_nodup D
(*     try clear C; try clear D *)
  | NoDupA (@equiv R2 _) (?x :: ?l) => idtac (* nothing to do here *)
  end.

(** ****  Merging results about the different kinds of triangles  **)

Lemma triangle_next_maj_or_diameter_or_triangle : forall da config,
  ~invalid config ->
  triangle_case config ->
  (* A majority tower *)
  length (support (max (!! (round gatherR2 da config)))) = 1
  (* No majority tower and we go from equilateral to unclean diameter case *)
  \/ no_Majority (round gatherR2 da config)
     /\ equilateral_case config
     /\ length (on_SEC (support (!! (round gatherR2 da config)))) = 2
     /\ is_clean (!! (round gatherR2 da config)) = false
     /\ inclA equiv (on_SEC (support (!! (round gatherR2 da config)))) ((on_SEC (support (!! config))))
  (* No majority tower and the SEC remains the same *)
  \/ no_Majority (round gatherR2 da config)
     /\ PermutationA equiv (on_SEC (support (!! (round gatherR2 da config))))
                           (on_SEC (support (!! config))).
Proof.
intros da config Hinvalid [Hmaj [ptx [pty [ptz Hsec]]]].
destruct (support (max (!! (round gatherR2 da config)))) as [| pt1 [| pt2 l]] eqn:Hmax'.
- rewrite support_nil, max_empty in Hmax'. elim (spect_non_nil _ Hmax').
- now left.
- right.
  get_case (round gatherR2 da config). rename Hmaj0 into Hmaj'.
  clear Hmax' pt1 pt2 l.
  assert (Hinvalid' : ~invalid (round gatherR2 da config)) by now apply never_invalid.
  assert (Hlen' : size (!! (round gatherR2 da config)) >= 3) by now apply not_invalid_no_majority_size.
  destruct (classify_triangle ptx pty ptz) eqn:Htriangle.
  + (* Equilateral case *)
    assert (Htarget : target (!! config) = barycenter_3_pts ptx pty ptz) by now apply equilateral_target.
    assert (Hle := no_Majority_on_SEC_length Hmaj').
    destruct (on_SEC (support (!! (round gatherR2 da config)))) as [| pt1 [| pt2 [| pt3 l]]] eqn:Hsec';
    cbn in Hle; try omega.
    * (* Valid case: SEC is a pair *)
      destruct (is_clean (!! (round gatherR2 da config))) eqn:Hclean'.
      -- (* Absurd case: the center of the SEC is not on a diameter *)
        exfalso.
        clear Hle.
        assert (Hcenter := on_SEC_pair_is_diameter _ Hsec').
        assert (Hperm : PermutationA equiv (support (!! (round gatherR2 da config)))
                                           (middle pt1 pt2 :: pt1 :: pt2 :: nil)).
        apply diameter_clean_support;auto.
        destruct (is_clean (!! config)) eqn:Hclean.
        ** assert (Hincl : inclA equiv (support (!! (round gatherR2 da config)))
                                       (target (!! config) :: ptx :: pty :: ptz :: nil)).
           { rewrite <- Hsec. now apply incl_clean_next. }
           rewrite Hperm in Hincl.
           destruct (InA_dec equiv_dec (target(!! config)) (middle pt1 pt2 :: pt1 :: pt2 :: nil)) as [Hin | Hin].
           --- rewrite Htarget in Hin.
               assert (hNoDup:NoDupA equiv (pt1 :: pt2 :: nil)).
               { rewrite <- Hsec'. apply on_SEC_NoDupA, support_NoDupA. }
               Opaque middle. Opaque barycenter_3_pts. cbn in Hin.
               { rewrite InA_Leibniz in Hin. simpl in Hin. decompose [or False] Hin; clear Hin.
                  - rewrite H, Htarget in Hincl.
                    eapply inclA_cons_inv in Hincl; autoclass; auto.
                    + unfold inclA in Hincl.
                      assert (hpt1:= Hincl pt1 (InA_cons_hd _ eq_refl)).
                      assert (hpt2:= Hincl pt2 (InA_cons_tl pt1 (InA_cons_hd _ eq_refl))).
                      rewrite InA_Leibniz in hpt1,hpt2.

                      simpl in hpt1, hpt2;
                      decompose [or False] hpt1;
                      decompose [or False] hpt2;subst;clear hpt1; clear hpt2.
                      * inv hNoDup. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                      * assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                        inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                      * rewrite (@barycenter_3_pts_compat pt1 pty pt2 pt1 pt2 pty) in H; repeat econstructor.
                        rewrite(@classify_triangle_compat pt1 pty pt2 pt1 pt2 pty) in Htriangle; repeat econstructor.
                        assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                        inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                      * rewrite (@barycenter_3_pts_compat pt2 pt1 ptz pt1 pt2 ptz) in H; repeat econstructor.
                        rewrite(@classify_triangle_compat pt2 pt1 ptz pt1 pt2 ptz) in Htriangle; repeat econstructor.
                        assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                        inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                      * inv hNoDup. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                      * rewrite (@barycenter_3_pts_compat ptx pt1 pt2 pt1 pt2 ptx) in H.
                        -- rewrite (@classify_triangle_compat ptx pt1 pt2 pt1 pt2 ptx) in Htriangle.
                           ++ assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                              inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                           ++ now do 3 econstructor.
                        -- now do 3 econstructor.
                      * rewrite (@barycenter_3_pts_compat pt2 pty pt1 pt1 pt2 pty) in H.
                        -- rewrite (@classify_triangle_compat pt2 pty pt1 pt1 pt2 pty) in Htriangle.
                           ++ assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                              inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                           ++ now do 3 econstructor.
                        -- now do 3 econstructor.
                      * rewrite (@barycenter_3_pts_compat ptx pt2 pt1 pt1 pt2 ptx) in H.
                        -- rewrite (@classify_triangle_compat ptx pt2 pt1 pt1 pt2 ptx) in Htriangle.
                           ++ assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H).
                              inversion hNoDup; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                           ++ permut_3_4.
                        -- econstructor 4 with (pt2 :: ptx :: pt1 :: nil); now do 3 econstructor.
                      * inv hNoDup. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                    + rewrite <- H. apply middle_diff.
                      inversion hNoDup; subst.
                      intro abs; subst. match goal with | H: ~ InA _ _ _ |- _ => apply H end. now left.
                  - (* if (target (config)) is in (SEC (round config)) then two previously
                       SEC-towers have moved to (target (config)). therefore there are
                       two tower => majority (or contradicting invalid).  *)

                    assert (Hin : List.In pt2 (ptx :: pty :: ptz :: nil)).
                    { assert (Hin : List.In pt2 (target (!! config) :: ptx :: pty :: ptz :: nil)).
                      { rewrite <- Hsec.
                        apply InA_Leibniz.
                        eapply incl_clean_next with da;auto.
                        assert (Hin : InA equiv pt2 (on_SEC (support (!! (round gatherR2 da config))))).
                        { rewrite Hsec'. now right; left. }
                        rewrite InA_Leibniz in Hin |- *.
                        now apply on_SEC_In. }
(* FIXME: Auto-names changed...
                      inversion H1; trivial; [].
                      exfalso.
                      rewrite <- H2 in Htarget.
                      rewrite Htarget in H3.
                      subst pt2; inv hNoDup; intuition. }
                    unfold inclA in H0.
                    assert (hmid:InA equiv (middle pt1 pt2) (middle pt1 pt2 :: pt1 :: pt2 :: nil)).
                    { left.
                      reflexivity. }
                    specialize (H0 (middle pt1 pt2) hmid).
                    rewrite InA_Leibniz in H0.
                    simpl in H0.
                    decompose [or False] H0;clear H0.
                    + rewrite Htarget in H1.
                      rewrite <- H2 in H1.
                      elim (@middle_diff pt1 pt2).
                      * intro abs. rewrite abs in hNoDup. inversion hNoDup.
                        apply H4.
                        left; reflexivity.
                      * rewrite <- H1.
                        left;reflexivity.
                    + assert(ptx = pt2).
                      { rewrite middle_comm in H3.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=ptx) (white:=pt1);eauto.
                        left.
                        reflexivity. }
                      subst ptx.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(pty = pt2).
                      { rewrite middle_comm in H1.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=pty) (white:=pt1);eauto.
                        right;left.
                        reflexivity. }
                      subst pty.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(ptz = pt2).
                      { rewrite middle_comm in H3.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=ptz) (white:=pt1);eauto.
                        right;right;left.
                        reflexivity. }
                      subst ptz.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                  - (* if (target (config)) is in (SEC (round config)) then two previously
                       SEC-towers have moved to (target (config)). therefore there are
                       two towers => majority (or contradicting invalid).  *)
                    assert (hIn:In pt1 (ptx :: pty :: ptz :: nil)).
                    { assert (In pt1 (target (!! config) :: ptx :: pty :: ptz :: nil)).
                      { rewrite <- Hsec.
                        apply InA_Leibniz.
                        eapply incl_clean_next with da;auto.
                        assert (InA equiv pt1 (on_SEC (support (!! (round gatherR2 da config))))).
                        { rewrite Hsec'.
                          left;reflexivity. }
                        rewrite InA_Leibniz in H2 |-*.
                        apply on_SEC_In.
                        assumption. }
                      inversion H2.
                      - exfalso.
                        rewrite H3 in Htarget.
                        rewrite <- Htarget in H1.
                        subst pt2.
                        inversion  hNoDup.
                        apply H5.
                        left;reflexivity.
                      - assumption. }
                    unfold inclA in H0.
                    assert (hmid:InA equiv (middle pt1 pt2) (middle pt1 pt2 :: pt1 :: pt2 :: nil)).
                    { left.
                      reflexivity. }
                    specialize (H0 (middle pt1 pt2) hmid).
                    rewrite InA_Leibniz in H0.
                    simpl in H0.
                    decompose [or False] H0;clear H0.
                    + rewrite Htarget in H2.
                      rewrite <- H1 in H2.
                      elim (@middle_diff pt1 pt2).
                      * intro abs. rewrite abs in hNoDup. inversion hNoDup.
                        apply H4.
                        left; reflexivity.
                      * rewrite <- H2.
                        right;left;reflexivity.
                    + assert(ptx = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=ptx) (white:=pt2);eauto.
                        left.
                        reflexivity. }
                      subst ptx.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(pty = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=pty) (white:=pt2);eauto.
                        right;left.
                        reflexivity. }
                      subst pty.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(ptz = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=ptz) (white:=pt2);eauto.
                        right;right;left.
                        reflexivity. }
                      subst ptz.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity. }
            --- (* (ptx :: pty :: ptz :: nil) = (middle pt1 pt2 :: pt1 :: pt2 :: nil)
                   contradiction with calssify_triangle = equilateral *)
              assert (PermutationA equiv (ptx :: pty :: ptz :: nil) (middle pt1 pt2 :: pt1 :: pt2 :: nil)).
              { apply inclA_skip in H0;autoclass.
                - symmetry.
                  apply NoDupA_inclA_length_PermutationA with (1:=equiv_equiv);auto.
                  + rewrite <- H.
                    apply support_NoDupA;auto.
                  + rewrite <- Hsec.
                    apply on_SEC_NoDupA;auto.
                    apply support_NoDupA;auto.
                - rewrite InA_Leibniz.
                  assumption. }
              assert (classify_triangle (middle pt1 pt2) pt1 pt2 = Equilateral).
              { rewrite PermutationA_Leibniz in H1. now rewrite (classify_triangle_compat H1) in Htriangle. }
              functional inversion H2. clear H2.
              rewrite -> ?Rdec_bool_true_iff in *.
              rewrite R2.dist_sym in H3.
              rewrite R2dist_middle in H3.
              assert (R2.dist pt1 pt2 = 0%R).
              { lra. }
              apply R2.dist_defined in H2.
              assert (hNoDup:NoDupA equiv (pt1 :: pt2 :: nil)).
              { rewrite <- Hsec'.
                apply on_SEC_NoDupA.
                apply support_NoDupA. }

              rewrite H2 in hNoDup.
              inversion hNoDup.
              apply H7. left;reflexivity.
         ** rewrite <- dirty_next_on_SEC_same in Hsec;auto.
            rewrite Hsec' in Hsec.
            assert (length (pt1 :: pt2 :: nil) = length (ptx :: pty :: ptz :: nil)).
            { rewrite Hsec.
              reflexivity. }
            simpl in H0;omega.

      -- (* Valid case: the center of the SEC is not on a diameter *)
         left. repeat split; trivial; eauto.
         assert (h_clean_config:is_clean (!! config) = true).
         { destruct (bool_dec (is_clean (!! config)) true) as [ heq_clean_true | heq_clean_false].
           - assumption.
           - exfalso.
             apply not_true_is_false in heq_clean_false.
             assert (hdirty:=@dirty_next_SEC_same da config Hmaj heq_clean_false).
             setoid_rewrite <- (@dirty_next_on_SEC_same da config Hmaj heq_clean_false) in Hsec.
             rewrite Hsec' in Hsec.
             apply PermutationA_length in Hsec.
             simpl in Hsec.
             omega. }

         assert (hincl_round:inclA equiv (support (!! (round gatherR2 da config)))
                                   (target (!! config) :: on_SEC (support (!! config)))).
         { eapply incl_clean_next ;eauto. }
         rewrite Htarget in hincl_round.
         rewrite Hsec in hincl_round.
         assert (h_incl_pt1_pt2 : inclA equiv (pt1 :: pt2 :: nil)
                                              (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)).
         { transitivity (support (!! (round gatherR2 da config))).
           -  rewrite <- Hsec'.
             unfold on_SEC.
             unfold inclA.
             intros x H1.
             rewrite filter_InA in H1.
             destruct H1.
             assumption.
             autoclass. 
           - assumption. }

         assert (hnodup: NoDupA equiv (pt1 :: pt2 :: nil)).
         { rewrite <- Hsec'. 
           apply on_SEC_NoDupA.
           apply support_NoDupA. }

         assert (hnodupxyz: NoDupA equiv (ptx :: pty :: ptz :: nil)).
         { rewrite <- Hsec. 
           apply on_SEC_NoDupA.
           apply support_NoDupA. }
         inv_nodup hnodupxyz.
         inv_nodup hnodup.
         destruct (equiv_dec pt1 (barycenter_3_pts ptx pty ptz)) as [heq_pt1_bary | hneq_pt1_bary].
         ++ { exfalso.
              assert(hpermut_config: PermutationA equiv (support (!! (round gatherR2 da config)))
                                                      (pt1 :: pt2 :: nil)).
              { rewrite heq_pt1_bary in heq2, h_incl_pt1_pt2.
                apply inclA_cons_inv in h_incl_pt1_pt2; autoclass.
                + red in h_incl_pt1_pt2.
                  assert (h_pt2:InA equiv pt2 (pt2 :: nil)).
                  { left;reflexivity. }
                  specialize (h_incl_pt1_pt2 pt2 h_pt2).
                  clear h_pt2.
                  inversion h_incl_pt1_pt2 as [pt lpt heq_pt2_ptx [__h heq_lpt]| pt lpt h_in_pt2_lpt [__h heq_lpt]].
                  (* pt2 = ptx *)
                  * unfold equiv, R2def.eq in heq_pt2_ptx.
                    subst.
                    assert (hpermut:PermutationA equiv (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                 (pty :: ptz :: barycenter_3_pts ptx pty ptz :: ptx :: nil))
                      by permut_3_4.
                    rewrite hpermut in hincl_round;clear hpermut.
                    assert (h_ynotin:~ InA equiv pty (support (!! (round gatherR2 da config)))).
                    { eapply SEC_3_to_2;eauto.
                      - repeat econstructor; reflexivity.
                      - rewrite Hsec'.
                        reflexivity. }
                    assert (h_znotin:~ InA equiv ptz (support (!! (round gatherR2 da config)))).
                    { eapply SEC_3_to_2;eauto.
                      - repeat econstructor; reflexivity.
                      - rewrite Hsec'.
                        reflexivity. }
                    do 2 (apply inclA_skip in hincl_round; autoclass).
                    apply NoDupA_inclA_length_PermutationA; autoclass.
                    -- apply support_NoDupA.
                    -- now rewrite heq_pt1_bary.
                    -- simpl.
                       transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                       ++ now rewrite Hsec'.
                       ++ unfold on_SEC.
                          rewrite filter_length.
                          omega.

                  * { (* InA equiv pt2 (pt2 :: nil)  *)
                      subst pt.
                      subst lpt.
                      inversion h_in_pt2_lpt
                        as [pt lpt heq_pt2_pty [__h heq_lpt] | pt lpt h_in_pt2_lpt' [__h heq_lpt]].
                      (* pt2 = pty *)
                      * unfold equiv, R2def.eq in heq_pt2_pty.
                        subst.
                        assert (Hperm:PermutationA equiv (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                         (ptx :: ptz :: barycenter_3_pts ptx pty ptz :: pty :: nil))
                          by permut_3_4.
                        rewrite Hperm in hincl_round;clear Hperm.
                        assert (h_ynotin:~ InA equiv ptx (support (!! (round gatherR2 da config)))).
                        { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                        assert (h_znotin:~ InA equiv ptz (support (!! (round gatherR2 da config)))).
                        { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                        apply inclA_skip in hincl_round;autoclass.
                        apply inclA_skip in hincl_round;autoclass.
                        apply NoDupA_inclA_length_PermutationA;autoclass.
                        -- apply support_NoDupA.                   
                        -- rewrite heq_pt1_bary.
                           assumption.
                        -- simpl.
                           transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                           ++ rewrite Hsec'.
                              reflexivity.
                           ++ unfold on_SEC.
                              rewrite filter_length.
                              omega.
                      * subst pt.
                        subst lpt.
                        { inversion h_in_pt2_lpt'
                            as [pt lpt heq_pt2_pty [__h heq_lpt] | pt lpt h_in_pt2_lpt'' [__h heq_lpt]].
                          (* pt2 = pty *)
                          * unfold equiv, R2def.eq in heq_pt2_pty.
                            subst.
                            assert (Hperm : PermutationA equiv
                                      (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                      (ptx :: pty :: barycenter_3_pts ptx pty ptz :: ptz :: nil))
                              by permut_3_4.
                            rewrite Hperm in hincl_round;clear Hperm.
                            assert (h_ynotin:~ InA equiv ptx (support (!! (round gatherR2 da config)))).
                            { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                            assert (h_znotin:~ InA equiv pty (support (!! (round gatherR2 da config)))).
                            { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                            apply inclA_skip in hincl_round;autoclass.
                            apply inclA_skip in hincl_round;autoclass.
                            apply NoDupA_inclA_length_PermutationA;autoclass.
                            -- apply support_NoDupA.                   
                            -- now rewrite heq_pt1_bary.
                            -- simpl.
                               transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                               ++ rewrite Hsec'.
                                  reflexivity.
                               ++ unfold on_SEC.
                                  rewrite filter_length.
                                  omega.
                          * inversion h_in_pt2_lpt''. } }
                  + intro Hin. apply heq2. now inversion Hin. }
                - rewrite size_spec in Hlen'.
                  rewrite hpermut_config in Hlen'.
                  simpl in Hlen'.
                  omega. }
         ++ { destruct (equiv_dec pt2 (barycenter_3_pts ptx pty ptz)) as [heq_pt2_bary | hneq_pt2_bary].
              ++ { exfalso.
                   assert(hpermut_config: PermutationA equiv (support (!! (round gatherR2 da config)))
                                                           (pt2 :: pt1 :: nil)).
                   { assert (hpermut12:PermutationA equiv (pt1 :: pt2 :: nil) (pt2 :: pt1 :: nil))  by permut_3_4.
                     rewrite hpermut12 in h_incl_pt1_pt2.
                     rewrite heq_pt2_bary in heq2, h_incl_pt1_pt2.
                     apply inclA_cons_inv in h_incl_pt1_pt2;autoclass.
                     + red in h_incl_pt1_pt2.
                       assert (h_pt1:InA equiv pt1 (pt1 :: nil)).
                       { left;reflexivity. }
                       specialize (h_incl_pt1_pt2 pt1 h_pt1).
                       clear h_pt1.
                       inversion h_incl_pt1_pt2 as [pt lpt heq_pt1_ptx [__h heq_lpt]
                                                  | pt lpt h_in_pt1_lpt [__h heq_lpt]].
                       (* pt1 = ptx *)
                       * unfold equiv, R2def.eq in heq_pt1_ptx.
                         subst ptx.
                         subst pt.
                         assert (Hperm:PermutationA equiv (barycenter_3_pts pt1 pty ptz :: pt1 :: pty :: ptz :: nil)
                                                      (pty :: ptz :: barycenter_3_pts pt1 pty ptz :: pt1 :: nil))
                           by permut_3_4.
                         rewrite Hperm in hincl_round;clear Hperm.
                         assert (h_ynotin:~ InA equiv pty (support (!! (round gatherR2 da config)))).
                         { eapply SEC_3_to_2;eauto.
                           - repeat econstructor; reflexivity.
                           - rewrite Hsec'.
                             permut_3_4. }
                         assert (h_znotin:~ InA equiv ptz (support (!! (round gatherR2 da config)))).
                         { eapply SEC_3_to_2;eauto.
                           - repeat econstructor; reflexivity.
                           - rewrite Hsec'.
                             permut_3_4. }
                         apply inclA_skip in hincl_round;autoclass.
                         apply inclA_skip in hincl_round;autoclass.
                         apply NoDupA_inclA_length_PermutationA;autoclass.
                         -- apply support_NoDupA.                   
                         -- repeat constructor.
                            ++ intro Habs.
                               inversion_clear Habs.
                               ** congruence.
                               ** now rewrite InA_nil in *.
                            ++ now rewrite InA_nil.
                         -- now rewrite heq_pt2_bary.
                         -- simpl.
                            transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                            ++ now rewrite Hsec'.
                            ++ unfold on_SEC.
                               rewrite filter_length.
                               omega.

                       * { (* InA equiv pt1 (pt1 :: nil)  *)
                           subst pt.
                           subst lpt.
                           inversion h_in_pt1_lpt as [pt lpt heq_pt1_pty [__h heq_lpt]
                                                     | pt lpt h_in_pt1_lpt' [__h heq_lpt]].
                           (* pt1 = pty *)
                           * unfold equiv, R2def.eq in heq_pt1_pty.
                             subst.
                             assert (Hperm : PermutationA equiv
                                       (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                       (ptx :: ptz :: barycenter_3_pts ptx pty ptz :: pty :: nil))
                               by permut_3_4.
                             rewrite Hperm in hincl_round;clear Hperm.
                             assert (h_xnotin:~ InA equiv ptx (support (!! (round gatherR2 da config)))).
                             { eapply SEC_3_to_2;eauto.
                               - repeat econstructor; reflexivity.
                               - rewrite Hsec'.
                                 permut_3_4. }
                             assert (h_znotin:~ InA equiv ptz (support (!! (round gatherR2 da config)))).
                             { eapply SEC_3_to_2;eauto.
                               - repeat econstructor; reflexivity.
                               - rewrite Hsec'.
                                 permut_3_4. }
                             apply inclA_skip in hincl_round;autoclass.
                             apply inclA_skip in hincl_round;autoclass.
                             apply NoDupA_inclA_length_PermutationA;autoclass.
                             -- apply support_NoDupA.                   
                             -- repeat constructor.
                                ++ intro Habs.
                                   inversion_clear Habs.
                                   ** congruence.
                                   ** now rewrite InA_nil in *.
                                ++ now rewrite InA_nil.
                             -- rewrite heq_pt2_bary.
                                assumption.
                             -- simpl.
                                transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                                ++ rewrite Hsec'.
                                   reflexivity.
                                ++ unfold on_SEC.
                                   rewrite filter_length.
                                   omega.
                           * subst pt.
                             subst lpt.
                             { inversion h_in_pt1_lpt'
                                as [pt lpt heq_pt1_ptz [__h heq_lpt] | pt lpt h_in_pt1_lpt'' [__h heq_lpt]].
                               (* pt1 = pty *)
                               * unfold equiv, R2def.eq in heq_pt1_ptz.
                                 subst.
                                 assert (hpermut : PermutationA equiv
                                                     (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                     (ptx :: pty :: barycenter_3_pts ptx pty ptz :: ptz :: nil))
                                   by permut_3_4.
                                 rewrite hpermut in hincl_round;clear hpermut.
                                 assert (h_xnotin:~ InA equiv ptx (support (!! (round gatherR2 da config)))).
                                 { eapply SEC_3_to_2;eauto.
                                   - repeat econstructor; reflexivity.
                                   - rewrite Hsec'.
                                     permut_3_4. }
                                 assert (h_ynotin:~ InA equiv pty (support (!! (round gatherR2 da config)))).
                                 { eapply SEC_3_to_2; eauto.
                                   - repeat econstructor; reflexivity.
                                   - rewrite Hsec'.
                                     permut_3_4. }

                                 do 2 (apply inclA_skip in hincl_round; autoclass).
                                 apply NoDupA_inclA_length_PermutationA; autoclass.
                                 -- apply support_NoDupA.
                                 -- repeat constructor.
                                    ++ intro Habs.
                                       inversion_clear Habs.
                                       ** congruence.
                                       ** now rewrite InA_nil in *.
                                    ++ now rewrite InA_nil.
                                 -- now rewrite heq_pt2_bary.
                                 -- simpl.
                                    transitivity (length (on_SEC (support (!! (round gatherR2 da config))))).
                                    ++ rewrite Hsec'.
                                       reflexivity.
                                    ++ unfold on_SEC.
                                       rewrite filter_length.
                                       omega.
                               * inversion h_in_pt1_lpt''. } }
                     + intro abs.
                       inversion abs.
                       * apply heq2.
                         symmetry.
                         assumption.
                       * rewrite <- InA_nil.
                         eauto. }
                   + rewrite size_spec in Hlen'.
                     rewrite hpermut_config in Hlen'.
                     simpl in Hlen'.
                     omega. }

              ++ rewrite Hsec.
                 intros pt hin.
                 assert (h:=h_incl_pt1_pt2 _ hin).
                 inversion_clear h.
                 ** inversion hin.
                    --- subst.
                        rewrite H1 in H.
                        contradiction.
                    --- subst.
                        inversion H1.
                        +++ rewrite H2 in H.
                            contradiction.
                        +++ inversion H2.
                 ** assumption. }

    * (* Valid case: SEC is a triangle *)
      right. split; trivial.
      rewrite <- Hsec'.
      (* TODO: the SEC has not changed *)
      destruct (is_clean (!! config)) eqn:Hclean.
      -- destruct (moving gatherR2 da config) as [| gmove ?] eqn:Hmoving.
         ++ apply no_moving_same_config in Hmoving. now rewrite Hmoving.
         ++ assert (Hperm' : PermutationA equiv (support (!! (round gatherR2 da config)))
                                                (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)).
            { assert ((!! (round gatherR2 da config))[target (!! config)] > 0).
              { apply le_lt_trans with ((!! config)[target (!! config)]); try omega.
                rewrite increase_move_iff.
                exists gmove. split.
                - apply destination_is_target; trivial.
                  rewrite Hmoving. now left.
                - now rewrite <- moving_spec, Hmoving; left. }
              apply (NoDupA_inclA_length_PermutationA _).
              - apply support_NoDupA.
              - apply equilateral_barycenter_NoDupA; trivial.
                assert (Hnodup : NoDupA equiv (on_SEC (support (!! config)))).
                { apply on_SEC_NoDupA, support_NoDupA. }
                rewrite Hsec in Hnodup. inversion Hnodup. intuition.
              - rewrite <- Htarget, <- Hsec. now apply incl_clean_next.
              - rewrite <- size_spec.
                destruct (size (!! (round gatherR2 da config))) as [| [| [| [| ?]]]] eqn:Hlen; simpl; try omega.
                exfalso.
                assert (l = nil).
                { destruct l as [| pt4 l]; trivial.
                  cut (4 + length l <= 3); try omega.
                  change (4 + length l) with (length (pt1 :: pt2 :: pt3 :: pt4 :: l)).
                  rewrite <- Hsec', <- Hlen, size_spec.
                  apply (NoDupA_inclA_length equiv_equiv).
                  - apply on_SEC_NoDupA, support_NoDupA.
                  - unfold on_SEC. intro. rewrite (filter_InA _). intuition. }
                subst.
                assert (Hperm' : PermutationA equiv (support (!! (round gatherR2 da config)))
                                                    (pt1 :: pt2 :: pt3 :: nil)).
                { symmetry.
                  apply (NoDupA_inclA_length_PermutationA _).
                  - rewrite <- Hsec'. apply on_SEC_NoDupA, support_NoDupA.
                  - apply support_NoDupA.
                  - rewrite <- Hsec'. unfold on_SEC. intro. rewrite (filter_InA _). intuition.
                  - rewrite <- size_spec. cbn. omega. }
                rewrite <- Hsec' in Hperm'.
                (* Triangle equilatéral: comme qqchose bouge et que on est encore avec 3
                   colonne après, une colonne s'est déplacée vers le barycentre, contradiction:
                   le barycentre ne peut pas être sur le SEC. *)
                assert (Hnodup : NoDupA equiv (ptx :: pty :: ptz :: nil)).
                { rewrite <- Hsec. apply on_SEC_NoDupA, support_NoDupA. }
                assert (Hex : exists pta ptb ptc,
                              PermutationA equiv (pta :: ptb :: ptc :: nil) (ptx :: pty :: ptz :: nil)
                              /\ PermutationA equiv (barycenter_3_pts ptx pty ptz :: pta :: ptb ::nil)
                                                    (pt1 :: pt2 :: pt3 :: nil)).
                { assert (hincl:=incl_clean_next da config Hclean).
                  rewrite Hsec in hincl.
                  rewrite Hperm', Hsec' in hincl.
                  assert (hbary : InA equiv (barycenter_3_pts ptx pty ptz)
                                            (support (!! (round gatherR2 da config)))).
                  { rewrite support_In.
                    rewrite <- Htarget.
                    assumption. }
                  rewrite Hperm',Hsec' in hbary.
                  apply PermutationA_split in hbary; autoclass.
                  destruct hbary as [l hpermut_l].
                  setoid_rewrite hpermut_l.
                  assert (Hlength := PermutationA_length hpermut_l).
                  destruct l as [| pta [| ptb [| ? ?]]]; simpl in Hlength; omega || clear Hlength.
                  inv_nodup Hnodup.
                  assert (Hnodup' := equilateral_barycenter_NoDupA _ Htriangle ltac:(auto)).
                  assert (Hnodup123 : NoDupA equiv (pt1 :: pt2 :: pt3 :: nil)).
                  { rewrite <- Hsec'. apply on_SEC_NoDupA, support_NoDupA. }
                  inv_nodup Hnodup'.
                  rewrite hpermut_l in Hnodup123. inv_nodup Hnodup123.
                  assert (Hpta : InA equiv pta (ptx :: pty :: ptz :: nil)).
                  { rewrite hpermut_l, Htarget in hincl. apply (inclA_cons_inv _ h_notin4) in hincl.
                    apply hincl. now constructor. }
                  assert (Hptb : InA equiv ptb (ptx :: pty :: ptz :: nil)).
                  { rewrite hpermut_l, Htarget in hincl. apply (inclA_cons_inv _ h_notin4) in hincl.
                    apply hincl. now do 2 constructor. }
                  rewrite InA_Leibniz in Hpta, Hptb. simpl in Hpta, Hptb.
                  exists pta, ptb.
                  cut (exists ptc, PermutationA equiv (pta :: ptb :: ptc :: nil) (ptx :: pty :: ptz :: nil)).
                  - intros [ptc Hptc]. exists ptc. now split.
                  - decompose [or False] Hpta; decompose [or False] Hptb;
                    lazymatch goal with
                      | Ha : ?pt = pta, Hb : ?pt = ptb |- _ => congruence
                      | Ha : ?pt = pta, Hb : ?pt' = ptb |- _ =>
                          match goal with
                            | H : pt <> ?ptc, H' : pt' <> ?ptc |- _ => exists ptc
                            | H : ?ptc <> pt, H' : pt' <> ?ptc |- _ => exists ptc
                            | H : pt <> ?ptc, H' : ?ptc <> pt' |- _ => exists ptc
                            | H : ?ptc <> pt, H' : ?ptc <> pt' |- _ => exists ptc
                          end
                    end; subst; permut_3_4. }
                destruct Hex as [pta [ptb [ptc [Hpermxyz Hperm]]]].
                pose (better_SEC := {| center := middle pta ptb; radius := /2 * R2.dist pta ptb |}).
                assert (Hbary_strict : (R2.dist (barycenter_3_pts ptx pty ptz) (center better_SEC)
                                        < radius better_SEC)%R).
                { rewrite PermutationA_Leibniz in Hpermxyz. rewrite <- (barycenter_3_pts_compat Hpermxyz).
                  unfold better_SEC. simpl. rewrite R2norm_dist. unfold barycenter_3_pts, middle.
                  replace (/ 3 * (pta + (ptb + ptc)) - 1 / 2 * (pta + ptb))%R2
                    with (/6 * (ptc + ptc - (pta + ptb)))%R2 by (destruct pta, ptb, ptc; simpl; f_equal; field).
                  rewrite R2norm_mul. rewrite Rabs_pos_eq; try lra; [].
                  rewrite <- R2norm_dist.
                  cut (R2.dist (ptc + ptc) (pta + ptb) < 3 * R2.dist pta ptb)%R; try lra; [].
                  eapply Rle_lt_trans.
                  - apply (R2riang_ineq _ (ptc + pta)%R2).
                  - setoid_rewrite R2.add_comm at 2 4. do 2 rewrite R2add_dist.
                    rewrite <- (classify_triangle_compat Hpermxyz) in Htriangle.
                    rewrite classify_triangle_Equilateral_spec in Htriangle.
                    destruct Htriangle as [Heq1 Heq2].
                    setoid_rewrite R2.dist_sym at 1 2. rewrite Heq1, Heq2.
                    assert (Hle' := R2.dist_pos ptb ptc).
                    rewrite <- PermutationA_Leibniz in Hpermxyz. rewrite <- Hpermxyz in Hnodup. inv_nodup Hnodup.
                    rewrite <- R2.dist_defined in heq1. lra. }
                assert (enclosing_circle better_SEC (barycenter_3_pts ptx pty ptz :: pta :: ptb :: nil)).
                { intros pt hin.
                  simpl in hin.
                  decompose [or False] hin;subst pt;clear hin.
                  - apply Rlt_le. 
                    assumption.
                  - unfold better_SEC ; simpl.
                    rewrite R2dist_middle.
                    reflexivity.
                  - unfold better_SEC ; simpl.
                    rewrite middle_comm.
                    rewrite R2dist_middle.
                    rewrite R2.dist_sym.
                    reflexivity. }
                assert (better_SEC = (SEC (support (!! (round gatherR2 da config))))).
                { rewrite PermutationA_Leibniz in Hperm',Hperm.
                  rewrite Hperm',Hsec',<-Hperm.
                  apply SEC_unicity.
                  - assumption.
                  - unfold better_SEC.
                    simpl.
                    apply SEC_min_radius; intuition. }
                absurd (on_circle better_SEC (barycenter_3_pts  ptx pty ptz)=true).
                + rewrite on_circle_true_iff.
                  apply Rlt_not_eq.
                  assumption.
                + rewrite H1.
                  eapply proj2.
                  rewrite <- filter_InA;autoclass.
                  unfold on_SEC in Hsec'.
                  rewrite Hsec'.
                  rewrite <- Hperm.
                  constructor.
                  reflexivity.
                }
            apply (NoDupA_equivlistA_PermutationA _).
            ** apply on_SEC_NoDupA, support_NoDupA.
            ** apply on_SEC_NoDupA, support_NoDupA.
            ** rewrite Hperm', Hsec.
               rewrite on_SEC_barycenter_triangle, <- Hsec, on_SEC_idempotent; try reflexivity.
               intros [? ?]. subst.
               assert (Hnodup : NoDupA equiv (on_SEC (support (!! config)))).
               { apply on_SEC_NoDupA, support_NoDupA. }
               rewrite Hsec in Hnodup. inversion Hnodup. intuition.
      -- now apply dirty_next_on_SEC_same.
  + (* Isosceles case *)
    assert (Htarget := isosceles_target config Hsec Htriangle).
    right. split; trivial.
    destruct (is_clean (!! config)) eqn:Hclean.
    -- destruct (moving gatherR2 da config) as [| gmove ?] eqn:Hmoving.
       ++ apply no_moving_same_config in Hmoving. now rewrite Hmoving.
       ++ assert (Hperm' : PermutationA equiv (support (!! (round gatherR2 da config)))
                                        (ptx :: pty :: ptz :: nil)).
          { assert (forall x, In x (gmove :: l) -> get_location (round gatherR2 da config x) == vertex).
            { rewrite <- Htarget.
              intros x H3.
              apply destination_is_target; auto.
              rewrite Hmoving.
              assumption. }
            assert (h_vertex:=isoscele_vertex_is_vertex _ _ _ Htriangle).
            assert (H_supp: PermutationA equiv (support (!! config)) (ptx :: pty :: ptz :: nil)).
            { rewrite is_clean_spec in Hclean.
              unfold SECT in Hclean.
              rewrite Hsec in Hclean.
              apply inclA_cons_InA in Hclean;autoclass;auto.
              - apply NoDupA_inclA_length_PermutationA;autoclass.
                + apply support_NoDupA;auto.
                + rewrite <- Hsec.
                  apply on_SEC_NoDupA.
                  apply support_NoDupA;auto.
                + transitivity (length (on_SEC (support (!! config)))).
                  -- rewrite Hsec.
                     reflexivity.
                  -- unfold on_SEC. 
                     rewrite filter_length.
                     omega.
              - rewrite Htarget.
                assumption. }

            apply NoDupA_inclA_length_PermutationA; autoclass.
            - apply support_NoDupA.
            - rewrite <- Hsec.
              apply on_SEC_NoDupA, support_NoDupA.
            - transitivity (target (!! config) :: ptx :: pty :: ptz :: nil).
              + rewrite <- H_supp.
                apply incl_next.
              + apply inclA_Leibniz.
                apply incl_cons.
                * rewrite Htarget.
                  apply InA_Leibniz.
                  assumption.
                * apply inclA_Leibniz.
                  reflexivity.
            - rewrite size_spec in Hlen'.
              apply Hlen'. }
          rewrite Hperm'.
          rewrite <- Hsec.
          apply on_SEC_idempotent.
    -- now apply dirty_next_on_SEC_same.
  + (* Scalene case *)
    assert (Htarget := scalene_target config Hsec Htriangle).
    right. split; trivial.
    (* TODO: the SEC has not changed, same thing? *)
    destruct (is_clean (!! config)) eqn:Hclean.
    -- destruct (moving gatherR2 da config) as [| gmove ?] eqn:Hmoving.
       ++ apply no_moving_same_config in Hmoving. now rewrite Hmoving.
       ++
         remember (opposite_of_max_side ptx pty ptz) as vertex.
         assert (Hperm' : PermutationA equiv (support (!! (round gatherR2 da config)))
                                        (ptx :: pty :: ptz :: nil)).
          { assert (forall x, In x (gmove :: l) -> get_location (round gatherR2 da config x) == vertex).
            { rewrite <- Htarget.
              intros x H3.
              apply destination_is_target;auto.
              rewrite Hmoving.
              assumption. }
            assert (h_vertex:=scalene_vertex_is_vertex _ _ _ Htriangle).
            assert (H_supp: PermutationA equiv (support (!! config)) (ptx :: pty :: ptz :: nil)).
            { rewrite is_clean_spec in Hclean.
              unfold SECT in Hclean.
              rewrite Hsec in Hclean.
              apply inclA_cons_InA in Hclean;autoclass;auto.
              - apply NoDupA_inclA_length_PermutationA;autoclass.
                + apply support_NoDupA;auto.
                + rewrite <- Hsec.
                  apply on_SEC_NoDupA.
                  apply support_NoDupA;auto.
                + transitivity (length (on_SEC (support (!! config)))).
                  -- rewrite Hsec.
                     reflexivity.
                  -- unfold on_SEC. 
                     rewrite filter_length.
                     omega.
              - subst.
                rewrite Htarget.
                assumption. }

            apply NoDupA_inclA_length_PermutationA; autoclass.
            - apply support_NoDupA.
            - rewrite <- Hsec.
              apply on_SEC_NoDupA, support_NoDupA.
            - transitivity (target (!! config) :: ptx :: pty :: ptz :: nil).
              + rewrite <- H_supp.
                apply incl_next.
              + apply inclA_Leibniz.
                apply incl_cons.
                * subst.
                  rewrite Htarget.
                  apply InA_Leibniz.
                  assumption.
                * apply inclA_Leibniz.
                  reflexivity.
            - rewrite size_spec in Hlen'.
              apply Hlen'. }
          rewrite Hperm'.
          rewrite <- Hsec.
          apply on_SEC_idempotent.
    -- now apply dirty_next_on_SEC_same.
Qed. *)
Admitted.

(** ***  Lemmas about the generic case  **)

Lemma clean_generic_next_generic_same_SEC : forall da config,
  generic_case config ->
  generic_case (round gatherR2 da config) ->
  SEC (support (!! (round gatherR2 da config))) = SEC (support (!! config)).
Proof.
intros da config Hcase Hcase'.
destruct (is_clean (!! config)) eqn:Hclean; try (now destruct Hcase; apply dirty_next_SEC_same); [].
assert (Hincl' := incl_clean_next da config Hclean).
destruct Hcase' as [Hmaj' [pt1' [pt2' [pt3' [pt4' [l' Hperm']]]]]].
(* These positions are different *)
assert (Hnodup : NoDupA equiv (pt1' :: pt2' :: pt3' :: pt4' :: l')).
{ rewrite <- Hperm'. apply on_SEC_NoDupA, support_NoDupA. }
inv_nodup Hnodup.
inversion_clear Hnodup. inversion_clear H0. inversion_clear H2.
assert (Hneq12 : pt1' <> pt2') by intuition.
assert (Hneq13 : pt1' <> pt3') by intuition.
assert (Hneq14 : pt1' <> pt4') by intuition.
assert (Hneq23 : pt2' <> pt3') by intuition.
assert (Hneq24 : pt2' <> pt4') by intuition.
assert (Hneq34 : pt3' <> pt4') by intuition.
clear H H0 H1 H3.
(* There are robots occupying these positions *)
assert (Hid1 : exists id1, get_location (round gatherR2 da config id1) == pt1').
{ change eq with equiv. rewrite <- spect_from_config_In,  <- support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid2 : exists id2, get_location (round gatherR2 da config id2) == pt2').
{ change eq with equiv. rewrite <- spect_from_config_In,  <- support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid3 : exists id3, get_location (round gatherR2 da config id3) == pt3').
{ change eq with equiv. rewrite <- spect_from_config_In,  <- support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid4 : exists id4, get_location (round gatherR2 da config id4) == pt4').
{ change eq with equiv. rewrite <- spect_from_config_In,  <- support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
destruct Hid1 as [id1 Hid1], Hid2 as [id2 Hid2], Hid3 as [id3 Hid3], Hid4 as [id4 Hid4].
hnf in Hid1, Hid2, Hid3, Hid4.
destruct Hcase as [Hmaj _].
rewrite (round_simplify_clean da Hmaj Hclean id1) in Hid1.
rewrite (round_simplify_clean da Hmaj Hclean id2) in Hid2.
rewrite (round_simplify_clean da Hmaj Hclean id3) in Hid3.
rewrite (round_simplify_clean da Hmaj Hclean id4) in Hid4.
(* These robots are different *)
assert (Hneqid12 : id1 <> id2). { intro. subst id1. rewrite Hid1 in Hid2. contradiction. }
assert (Hneqid13 : id1 <> id3). { intro. subst id1. rewrite Hid1 in Hid3. contradiction. }
assert (Hneqid14 : id1 <> id4). { intro. subst id1. rewrite Hid1 in Hid4. contradiction. }
assert (Hneqid23 : id2 <> id3). { intro. subst id2. rewrite Hid2 in Hid3. contradiction. }
assert (Hneqid24 : id2 <> id4). { intro. subst id2. rewrite Hid2 in Hid4. contradiction. }
assert (Hneqid34 : id3 <> id4). { intro. subst id3. rewrite Hid3 in Hid4. contradiction. }
(* At most one of these robots was activated during the round *)
assert (Hex : forall id id',
                List.In id (id1 :: id2 :: id3 :: id4 :: nil) -> List.In id' (id1 :: id2 :: id3 :: id4 :: nil) ->
                id <> id' -> da.(activate) config id = true -> da.(activate) config id' = false).
{ intros id id' Hid Hid' Hneq Hactive. simpl in *.
  destruct (da.(activate) config id') eqn:Hactive'; trivial; exfalso.
  decompose [or] Hid; decompose [or] Hid'; try subst id; try subst id';
  (now elim Hneq) || rewrite Hactive in *; rewrite Hactive' in *;
  rewrite ?Hid1, ?Hid2, ?Hid3, ?Hid4 in *; R2dec. }
(* Therefore, at least three were not activated and not on the target *)
assert (Hperm_id : exists id1' id2' id3' id4',
      Permutation (id1 :: id2 :: id3 :: id4 :: nil) (id1' :: id2' :: id3' :: id4' :: nil)
      /\ da.(activate) config id2' = false /\ da.(activate) config id3' = false /\ da.(activate) config id4' = false
      /\ NoDup (get_location (config id2') :: get_location (config id3') :: get_location (config id4') :: nil)
      /\ get_location (config id2') <> target (!!config)
      /\ get_location (config id3') <> target (!!config)
      /\ get_location (config id4') <> target (!!config)).
{ destruct (da.(activate) config id1) eqn:Hactive1.
  * exists id1, id2, id3, id4. split; trivial; [].
    repeat split; try (now generalize Hactive1; apply Hex; intuition).
    -- assert (Heq2 : da.(activate) config id2 = false) by (generalize Hactive1; apply Hex; intuition).
       assert (Heq3 : da.(activate) config id3 = false) by (generalize Hactive1; apply Hex; intuition).
       assert (Heq4 : da.(activate) config id4 = false) by (generalize Hactive1; apply Hex; intuition).
       rewrite Heq2, Heq3, Heq4 in *. clear Heq2 Heq3 Heq4. subst.
       assert (Hnodup : NoDup (target (!! config) :: get_location (config id2)
                               :: get_location (config id3) :: get_location (config id4) :: l')).
       { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, support_NoDupA. }
       inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
    -- intro. apply Hneq12. rewrite (Hex id1 id2) in Hid2; trivial; subst; intuition.
    -- intro. apply Hneq13. rewrite (Hex id1 id3) in Hid3; trivial; subst; intuition.
    -- intro. apply Hneq14. rewrite (Hex id1 id4) in Hid4; trivial; subst; intuition.
  * destruct (da.(activate) config id2) eqn:Hactive2.
    + exists id2, id1, id3, id4. split; [now do 3 econstructor|].
      repeat split; try now generalize Hactive2; apply Hex; intuition.
      -- assert (Heq1 : da.(activate) config id1 = false) by (generalize Hactive2; apply Hex; intuition).
         assert (Heq3 : da.(activate) config id3 = false) by (generalize Hactive2; apply Hex; intuition).
         assert (Heq4 : da.(activate) config id4 = false) by (generalize Hactive2; apply Hex; intuition).
         rewrite Heq1, Heq3, Heq4 in *. clear Heq1 Heq3 Heq4. subst.
         assert (Hnodup : NoDup (get_location (config id1) :: target (!! config)
                                 :: get_location (config id3) :: get_location (config id4) :: l')).
         { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, support_NoDupA. }
         inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
      -- intro. apply Hneq12. now subst.
      -- intro. apply Hneq23. rewrite (Hex id2 id3) in Hid3; trivial; subst; intuition.
      -- intro. apply Hneq24. rewrite (Hex id2 id4) in Hid4; trivial; subst; intuition.
    + destruct (da.(activate) config id3) eqn:Hactive3.
      - exists id3, id1, id2, id4. split; [now do 3 econstructor|].
        repeat split; try now generalize Hactive3; apply Hex; intuition.
        -- assert (Heq1 : da.(activate) config id1 = false) by (generalize Hactive3; apply Hex; intuition).
           assert (Heq2 : da.(activate) config id2 = false) by (generalize Hactive3; apply Hex; intuition).
           assert (Heq4 : da.(activate) config id4 = false) by (generalize Hactive3; apply Hex; intuition).
           rewrite Heq1, Heq2, Heq4 in *. clear Heq1 Heq2 Heq4. subst.
           assert (Hnodup : NoDup (get_location (config id1) :: get_location (config id2)
                                   :: target (!! config) :: get_location (config id4) :: l')).
           { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, support_NoDupA. }
           inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
        -- intro. apply Hneq13. now subst.
        -- intro. apply Hneq23. now subst.
        -- intro. apply Hneq34. rewrite (Hex id3 id4) in Hid4; trivial; subst; intuition.
      - destruct (da.(activate) config id4) eqn:Hactive4.
        ** exists id4, id1, id2, id3. repeat split; trivial; [now do 4 econstructor| ..]; try (now subst); [].
           subst. repeat constructor; cbn in *; intuition.
        ** destruct (get_location (config id1) =?= target (!! config)) as [Heq1 | Heq1].
           ++ exists id1, id2, id3, id4. rewrite <- Heq1. subst. repeat split; trivial; intuition; [].
              repeat constructor; cbn in *; intuition.
           ++ destruct (get_location (config id2) =?= target (!! config)) as [Heq2 | Heq2].
              -- exists id2, id1, id3, id4. rewrite <- Heq2. subst.
                 repeat split; trivial;
                 solve [repeat constructor; cbn in *; intuition | now do 3 econstructor].
              -- destruct (get_location (config id3) =?= target (!! config)) as [Heq3 | Heq3].
                 *** exists id3, id1, id2, id4. rewrite <- Heq3. subst.
                     Time repeat split; trivial; (* 9 s.*)
                     solve [repeat constructor; cbn in *; intuition | now do 3 econstructor].
                 *** exists id4, id1, id2, id3. subst.
                     Time repeat split; trivial; (* 11 s. *)
                     solve [repeat constructor; cbn in *; intuition | now do 4 econstructor]. }
(* Finally, the old and new SEC are defined by the unchanging locations of these three robots *)
destruct Hperm_id as [id1' [id2' [id3' [id4' [Hperm_id [Hactive2' [Hactive3' [Hactive4' [Hnodup [? [? ?]]]]]]]]]]].
apply three_points_same_circle with (get_location (config id2')) (get_location (config id3')) (get_location (config id4')).
+ assumption.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : List.In id2' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id2' || easy; clear Hin; rewrite Hactive2' in *; subst; intuition.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : List.In id3' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id3' || easy; clear Hin; rewrite Hactive3' in *;subst; intuition.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : List.In id4' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id4' || easy; clear Hin; rewrite Hactive4' in *; subst; intuition.
+ assert (Hin : InA equiv (get_location (config id2')) (support (!! config))).
  { rewrite support_In. apply pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
+ assert (Hin : InA equiv (get_location (config id3')) (support (!! config))).
  { rewrite support_In. apply pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
+ assert (Hin : InA equiv (get_location (config id4')) (support (!! config))).
  { rewrite support_In. apply pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
Qed.

Lemma clean_generic_next_generic_same_target_and_clean : forall da config,
  generic_case config ->
  is_clean (!! config) = true ->
  generic_case (round gatherR2 da config) ->
  is_clean (!! (round gatherR2 da config)) = true
  /\ target (!! (round gatherR2 da config)) = target (!! config).
Proof.
intros da config Hcase Hclean Hcase'.
assert (HSEC := clean_generic_next_generic_same_SEC da Hcase Hcase').
assert (Hincl' := incl_clean_next da config Hclean).
rewrite is_clean_spec.
assert (Htarget : target (!! (round gatherR2 da config)) = target (!! config)).
{ do 2 (rewrite generic_target; trivial). now rewrite HSEC. }
split; trivial.
intros pt Hin. unfold SECT. rewrite Htarget. unfold on_SEC. rewrite HSEC.
assert (Hpt := Hincl' _ Hin). unfold on_SEC in Hpt. inversion_clear Hpt.
- now left.
- right. rewrite (filter_InA _). split; trivial. now rewrite  (filter_InA _) in H.
Qed.

(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Theorem round_lt_config : forall da config,
  ~invalid config -> moving gatherR2 da config <> nil ->
  lt_config (round gatherR2 da config) config.
Proof.
  intros da config Hvalid Hmove. unfold lt_config.
  unfold measure at 2.
  destruct (support (max (!! config))) as [| pt [| pt' smax]] eqn:Hmax.
  - (* No robots *)
    rewrite support_nil, max_empty in Hmax. elim (spect_non_nil _ Hmax).
  - (* A majority tower *)
    get_case config.
    apply (MajTower_at_forever da) in Hcase.
    rewrite MajTower_at_equiv in Hcase.
    unfold measure. rewrite Hcase.
    right.
    assert (Hle := multiplicity_le_nG pt (round gatherR2 da config)).
    cut ((!! config)[pt] < (!! (round gatherR2 da config))[pt]); try omega; [].
    apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
    assert (Hactive : da.(activate) config gmove = true).
    { apply moving_active in Hmove. now rewrite active_spec in Hmove. }
    rewrite moving_spec in Hmove.
    rewrite increase_move_iff. exists gmove.
    split; try (now intro; apply Hmove, no_info); [].
    get_case config.
    rewrite (round_simplify_Majority _ Hcase0 gmove).
    destruct (da.(activate) config gmove); try reflexivity; []. now elim Hactive.
  - (* Computing the SEC *)
    get_case config. clear Hmax pt pt' smax.
    destruct (is_clean (!! config)) eqn:Hclean.
    (* Clean case *)
    + assert (Hle := no_Majority_on_SEC_length Hmaj).
      destruct (on_SEC (support (!! config))) as [| pt1 [| pt2 [| pt3 [| pt4 sec]]]] eqn:Hsec;
      cbn in Hle; try omega; [| |].
      * (* Diameter case *)
        assert (Htarget : target (!! config) = middle pt1 pt2) by now apply diameter_target.
        assert (Hperm := diameter_clean_support Hvalid Hmaj Hclean Hsec).
        destruct (clean_diameter_next_maj_or_diameter da Hvalid Hmaj Hclean Hsec)
          as [[pt Hmaj'] | [Hmaj' HpermSEC']].
        -- (* A majority is present after one round *)
           unfold measure.
           rewrite MajTower_at_equiv in Hmaj'.
           rewrite Hmaj'.
           left. omega.
        -- (* Still in a diameter case after one round *)
           assert (Hperm' := diameter_round_same da Hmaj' Hperm).
           assert (Hcase : clean_diameter_case config).
           { repeat split; trivial; setoid_rewrite Hsec; do 2 eexists; reflexivity. }
           assert (Htarget' := diameter_next_target_same da Hvalid Hcase Hmaj').
           rewrite no_Majority_equiv in Hmaj'.
           destruct Hmaj' as [? [? [? Hmaj']]].
           unfold measure. rewrite Hmaj'.
           assert (Hlen' : length (on_SEC (support (!! (round gatherR2 da config)))) = 2).
           { now rewrite HpermSEC'. }
           destruct (on_SEC (support (!! (round gatherR2 da config)))) as [| ? [| ? [| ? ?]]] eqn:Hsec';
           cbn in Hlen'; omega || clear Hlen'.
           assert (Hclean' : is_clean (!! (round gatherR2 da config)) = true).
           { rewrite is_clean_spec. unfold SECT. now rewrite Hsec', HpermSEC', Hperm', Htarget', Htarget. }
           rewrite Hclean'.
           right.
           now apply solve_measure_clean.
      * (* Triangle cases *)
        get_case config.
        assert (HnextSEC := triangle_next_maj_or_diameter_or_triangle da Hvalid Hcase).
        rewrite Hsec in HnextSEC.
        destruct HnextSEC as [HnextSEC | [[Hmaj' [Htriangle [Hlen [Hclean' Hincl]]]] | [Hmaj' HpermSEC']]].
        -- (* There is a majority tower on the next round *)
           unfold measure.
           destruct (support (max (!! (round gatherR2 da config)))) as [| ? [| ? ?]];
           cbn in HnextSEC; try discriminate.
           destruct (classify_triangle pt1 pt2 pt3); left; omega.
        -- (* Equilateral case with the SEC changing *)
           unfold measure.
           assert (Hmax' := Hmaj'). rewrite no_Majority_equiv in Hmax'.
           destruct Hmax' as [? [? [? Hmax']]]. rewrite Hmax'.
           destruct (on_SEC (support (!! (round gatherR2 da config)))) as [| ? [| ? [| ? ?]]];
           cbn in Hlen; omega || clear Hlen.
           rewrite Hclean'.
           left. omega.
        -- (* Still the same triangle after one round *)
           unfold measure.
           assert (Hmax' := Hmaj'). rewrite no_Majority_equiv in Hmax'.
           destruct Hmax' as [? [? [? Hmax']]]. rewrite Hmax'.
           assert (Hlen' : length (on_SEC (support (!! (round gatherR2 da config)))) = 3)
             by now rewrite HpermSEC'.
           destruct (on_SEC (support (!! (round gatherR2 da config)))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec';
           cbn in Hlen'; omega || clear Hlen'.
           assert (Htarget' : target (!! (round gatherR2 da config)) = target (!! config)).
           { apply same_on_SEC_same_target. now rewrite Hsec, Hsec'. }
           assert (Hclean' : is_clean (!! (round gatherR2 da config)) = true).
           { assert (Hincl' := incl_clean_next da config Hclean).
             rewrite is_clean_spec. unfold SECT.
             now rewrite Hsec', HpermSEC', <- Hsec, Htarget'. }
           rewrite Hclean'.
           right.
           now apply solve_measure_clean.
      * (* Generic case *)
        unfold measure.
        destruct (support (max (!! (round gatherR2 da config)))) as [| pt [| ? ?]] eqn:Hmax';
        try (now left; omega); [].
        get_case config.
        get_case (round gatherR2 da config).
        destruct (on_SEC (support (!! (round gatherR2 da config))))
          as [| pt1' [| pt2' [| pt3' [| pt4' ?]]]] eqn:Hsec';
        try (now destruct (is_clean (!! (round gatherR2 da config))); left; omega); [].
        (* Still in the generic case after one round *)
        get_case (round gatherR2 da config).
        assert (Hgeneric := clean_generic_next_generic_same_target_and_clean da Hcase Hclean Hcase0).
        destruct Hgeneric as [Hclean' Htarget'].
        rewrite Hclean'.
        right.
        now apply solve_measure_clean.
    (* Dirty case *)
    + assert (HsameSEC := dirty_next_on_SEC_same da Hmaj Hclean).
      assert (Hle := no_Majority_on_SEC_length Hmaj).
      unfold measure.
      destruct (support (max (!! (round gatherR2 da config)))) as [| ? [| ? ?]] eqn:Hmax'.
      * (* Absurd: no robot after one round *)
        rewrite support_nil, max_empty in Hmax'. elim (spect_non_nil _ Hmax').
      * (* A majority tower after one round *)
        destruct (on_SEC (support (!! config))) as [| ? [| ? [| ? [| ? ?]]]];
        cbn in Hle; omega || left; omega.
      * (* Still no majority tower after one round *)
        get_case (round gatherR2 da config). rename Hmaj0 into Hmaj'.
        assert (Hle' := no_Majority_on_SEC_length Hmaj').
        assert (Hlen := PermutationA_length HsameSEC).
        destruct (on_SEC (support (!! config))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec,
                 (on_SEC (support (!! (round gatherR2 da config)))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec';
        cbn in Hle, Hle', Hlen; try omega; [| |];
        destruct (is_clean (!! (round gatherR2 da config))) eqn:Hclean';
        solve [ left; omega | right; now apply solve_measure_dirty ].
Qed.

(** ***  With the termination, the rest of the proof is easy  **)

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (get_location (config id)) config.
Proof.
intros config pt Hgather id g'. transitivity pt.
- apply Hgather.
- pattern id. apply no_byz. clear id. intro g. symmetry. apply Hgather.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (get_location (config id)) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, get_location (config id) =/= pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => R2dec_bool (get_location (config x)) pt) names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite R2dec_bool_true_iff in Hall. repeat rewrite Hall; reflexivity || apply In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, R2dec_bool_false_iff in Hid'. now exists id'.
Qed.

(** Correctness proof: given a non-gathered, non invalid configuration, then some robot will move some day. *)
Theorem OneMustMove : forall config id, ~ invalid config -> ~gathered_at (get_location (config id)) config ->
  exists gmove, forall da, List.In gmove (active da config) -> List.In gmove (moving gatherR2 da config).
Proof.
intros config id Hvalid Hgather.
destruct (support (max (!! config))) as [| pt [| pt' lmax]] eqn:Hmax.
* elim (support_max_non_nil _ Hmax).
* rewrite <- MajTower_at_equiv in Hmax.
  apply not_gathered_generalize with _ _ pt in Hgather.
  apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
  exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
  rewrite (round_simplify_Majority _ Hmax gmove).
  destruct_match.
  + intro Habs. apply Hmove. now rewrite <- Habs.
  + now elim Hactive.
* (* No majority tower *)
  get_case config.
  destruct (is_clean (!! config)) eqn:Hclean.
  + (* clean case *)
    apply not_gathered_generalize with _ _ (target (!! config)) in Hgather.
    apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive.
    now rewrite moving_spec, (round_simplify_clean da Hmaj Hclean gmove), Hactive.
  + (* dirty case *)
    assert (Hclean' := Hclean). unfold is_clean in Hclean'. clear Hmax pt pt' lmax.
    destruct (inclA_bool _ equiv_dec (support (!! config)) (SECT (!! config))) eqn:Hincl;
    try discriminate; [].
    rewrite inclA_bool_false_iff, (not_inclA _ equiv_dec) in Hincl.
    destruct Hincl as [pt [Hin Hin']].
    rewrite support_In, spect_from_config_In in Hin.
    destruct Hin as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite (round_simplify_dirty da Hmaj Hclean gmove).
    destruct (da.(activate) config gmove); try (now elim Hactive); [].
    destruct (mem equiv_dec (get_location (config gmove)) (SECT (!! config))) eqn:Htest.
    - rewrite mem_true_iff, Hmove in Htest.
      contradiction.
    - rewrite mem_false_iff, Hmove in Htest.
      assert (Htarget : InA equiv (target (!! config)) (SECT (!! config))) by now left.
      intro Habs. rewrite <- Habs, Hmove in *.
      contradiction.
Qed.

(** Given a k-fair demon, in any non gathered, non invalid configuration, a robot will be the first to move. *)
Theorem Fair_FirstMove : forall (d : similarity_demon), Fair d -> forall config id,
  ~invalid config -> ~gathered_at (get_location (config id)) config -> FirstMove gatherR2 d config.
Proof.
intro d. generalize (similarity_demon2prop d).
generalize (similarity_demon2demon d). clear d.
intros d Hprop [locallyfair Hfair] config id Hvalid Hgathered.
destruct (OneMustMove id Hvalid Hgathered) as [gmove Hmove].
specialize (locallyfair gmove).
revert config Hvalid Hgathered Hmove Hfair.
induction locallyfair as [d Hactive | d]; intros config Hvalid Hgathered Hmove Hfair.
+ apply MoveNow. intro Habs. specialize (Hactive config). simpl in Hactive.
  rewrite <- active_spec, <- (demon2demon Hprop) in Hactive.
  apply Hmove in Hactive. rewrite demon2similarity_hd in Hactive.
  simpl in Hactive. rewrite Habs in Hactive. inv Hactive.
+ destruct (moving gatherR2 (Stream.hd d) config) eqn:Hnil.
  - apply MoveLater; try exact Hnil.
    rewrite (no_moving_same_config _ _ _ Hnil).
    destruct Hprop, Hfair.
    now apply IHlocallyfair.
  - apply MoveNow. rewrite Hnil. discriminate.
Qed.


(** Define one robot to get the location whenever they are gathered. *)
Definition g1 : G.
Proof. exists 0. generalize size_G; abstract omega. Defined.

Lemma gathered_at_forever : forall da config pt, gathered_at pt config -> gathered_at pt (round gatherR2 da config).
Proof.
intros da config pt Hgather. rewrite (round_simplify_Majority).
+ intro g. destruct (da.(activate) config (Good g)); reflexivity || apply Hgather.
+ intros pt' Hdiff.
  assert (H0 : (!! config)[pt'] = 0).
  { rewrite spect_from_config_spec, config_list_spec.
    induction names as [| id l].
    + reflexivity.
    + cbn. R2dec_full.
      - elim Hdiff. rewrite <- Heq. pattern id. apply no_byz. intro g. apply Hgather.
      - apply IHl. }
  rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply pos_in_config.
Qed.

Lemma gathered_at_OK : forall (d : similarity_demon) config pt,
  gathered_at pt config -> Gather pt (execute gatherR2 d config).
Proof.
cofix Hind. intros d config pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.

(** The final theorem. *)
Theorem Gathering_in_R2 : forall d : similarity_demon, Fair d -> ValidSolGathering gatherR2 d.
Proof.
intro d. generalize (similarity_demon2prop d).
generalize (similarity_demon2demon d). clear d.
intros d Hprop Hfair config.
revert d Hprop Hfair. pattern config.
apply (well_founded_ind wf_lt_config). clear config.
intros config Hind d' Hprop Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (get_location (config (Good g1)))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (get_location (config (Good g1))).
  rewrite <- (demon2demon Hprop). now apply Stream.Now, gathered_at_OK.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  rewrite <- (demon2demon Hprop) in Hfair.
  apply (Fair_FirstMove _ Hfair (Good g1)) in Hmove; trivial.
  rewrite (demon2demon Hprop) in Hfair, Hmove.
  induction Hmove as [d config Hmove | d config Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    destruct (Hind (round gatherR2 (Stream.hd d) config)) with (Stream.tl d) as [pt Hpt].
    - rewrite <- (demon2demon Hprop). apply round_lt_config; assumption.
    - now destruct Hprop.
    - now destruct Hfair.
    - rewrite <- (demon2demon Hprop). now apply never_invalid.
    - exists pt. apply Stream.Later. rewrite execute_tail. apply Hpt.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_config in Heq.
    destruct Hrec as [pt Hpt].
    - setoid_rewrite Heq. apply Hind.
    - now destruct Hprop.
    - now destruct Hfair.
    - rewrite Heq. assumption.
    - exists pt. apply Stream.Later. rewrite execute_tail. apply Hpt.
Qed.

Print Assumptions Gathering_in_R2.


(* Let us change the assumption over the demon, it is no longer fair
   but instead activates at least a robot that should move at each round *)
Definition OKunfair r :=
  Stream.forever (Stream.instant (fun da => forall config, ~invalid config -> moving r da config <> nil)).

Theorem unfair_Gathering_in_R2 :
  forall d, OKunfair gatherR2 d -> ValidSolGathering gatherR2 d.
Proof.
intros d Hunfair config. revert d Hunfair. pattern config.
apply (well_founded_ind wf_lt_config). clear config.
intros config Hind d Hunfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (get_location (config (Good g1)))) as [Hmove | Hmove].
+ (* If so, not much to do *)
  exists (get_location (config (Good g1))). now apply Stream.Now, gathered_at_OK.
+ (* Otherwise, by assumption on the demon, a robot should move
     so we can use our well-founded induction hypothesis. *)
 destruct Hunfair as [Hactive Hunfair]. hnf in Hactive.
  destruct (Hind (round gatherR2 (Stream.hd d) config)) with (Stream.tl d) as [pt Hpt].
  - apply round_lt_config; auto.
  - assumption.
  - now apply never_invalid.
  - exists pt. apply Stream.Later. rewrite execute_tail. apply Hpt.
Qed.
