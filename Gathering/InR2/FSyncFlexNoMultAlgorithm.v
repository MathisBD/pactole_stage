(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
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
Require Import Pactole.Setting.
Require Import Pactole.Models.Flexible.
Require Import Pactole.Spectra.SetSpectrum.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Gathering.Definitions.


Set Implicit Arguments.
Typeclasses eauto := (bfs) 10.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter n : nat.
Axiom size_G : (2 <= n)%nat.

(** There are n good robots and no byzantine ones. *)
Instance MyRobots : Names := Robots n 0.

Instance Loc : Location := make_Location R2.
Instance Loc_VS : @RealVectorSpace location location_Setoid location_EqDec := R2_VS.
Instance Loc_ES : @EuclideanSpace location location_Setoid location_EqDec Loc_VS := R2_ES.
Remove Hints R2_Setoid R2_EqDec R2_VS R2_ES : typeclass_instances.

(* Refolding typeclass instances *)
Ltac changeR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change state_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change state_EqDec with location_EqDec in *;
  change R2_VS with Loc_VS in *;
  change R2_ES with Loc_ES in *.


(** We are in a flexible formalism with no other info than the location,
    so the demon only chooses the move ratio. *)
Instance FlexChoice : update_choice ratio := Flexible.OnlyFlexible.
(* NB: The inactive instance actually does not matter since we are in a FSYNC setting,
       so we could instead leave it as a parameter. *)
Instance InactiveChoice : inactive_choice unit := { inactive_choice_EqDec := unit_eqdec }.

(** The robots choose the path they want to follow to a target. *)
Instance Robot : robot_choice (path location) := { robot_choice_Setoid := path_Setoid location }.

(** In a flexible setting, the minimum distance that robots are allowed to move is delta. *)
Parameter delta : R.

Lemma inactive_proper : Proper (equiv ==> eq ==> equiv ==> equiv)
  (fun (config : configuration) (id : ident) (_ : unit) => config id).
Proof. repeat intro; subst; auto. Qed.

Instance UpdFun : update_function (path location) (similarity location) ratio :=
  FlexibleUpdate delta.

Instance InaFun : inactive_function unit := NoChoiceInaFun.

(* Trying to avoid notation problem with implicit arguments *)
Notation "!! config" := (@spect_from_config _ _ Info MyRobots set_spectrum config origin) (at level 1).
Notation "x == y" := (equiv x y).
Notation spectrum := (@spectrum location Loc Info MyRobots set_spectrum).
Notation robogram := (@robogram location Loc Info MyRobots set_spectrum).
Notation configuration := (@configuration Loc location Info MyRobots).
Notation config_list := (@config_list Loc location Info MyRobots).
Notation round := (@round location Loc Info MyRobots set_spectrum _ _ _ _ _).
Notation execution := (@execution location Loc Info MyRobots).
Notation Sadd := (FSetInterface.add).

Implicit Type config : configuration.
Implicit Type da : similarity_da.
Implicit Type d : similarity_demon.
Arguments origin : simpl never.
Arguments dist : simpl never.

(* The robot trajectories are straight paths. *)
Definition path_R2 := path location.
Definition paths_in_R2 : location -> path_R2 := local_straight_path.
Coercion paths_in_R2 : location >-> path_R2.

Instance paths_in_R2_compat : Proper (@equiv _ location_Setoid ==> equiv) paths_in_R2.
Proof. intros pt1 pt2 Heq. now rewrite Heq. Qed.

Lemma no_byz : forall P, (forall g, P (Good g)) -> forall id, P id.
Proof.
intros P Hconfig [g | b].
+ apply Hconfig.
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

Lemma config_list_alls : forall pt, config_list (fun _ => pt) = alls pt nG.
Proof.
intro. rewrite config_list_spec, map_cst.
setoid_rewrite names_length. simpl. now rewrite plus_0_r.
Qed.

(** Define one robot to get their location whenever they are gathered. *)
Definition g1 : G.
Proof.
exists 0%nat. abstract (pose (Hle := size_G); omega).
Defined.

(* Definition Spect_map f s := Spect.M.fold (fun e acc => Spect.M.add (f e) acc) s Spect.M.empty. *)

Lemma map_sim_elements : forall (sim : similarity location) s,
  PermutationA equiv (elements (map sim s)) (List.map sim (elements s)).
Proof. intros. apply map_injective_elements; autoclass; apply Similarity.injective. Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall config, !! config =/= empty.
Proof.
intros config Habs.
specialize (Habs (get_location (config (Good g1)))). rewrite empty_spec in Habs.
rewrite <- Habs. apply pos_in_config.
Qed.

Lemma elements_non_nil : forall config, elements (!! config) <> nil.
Proof. intro. rewrite elements_nil. apply spect_non_nil. Qed.

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall (config : configuration) pt,
  In pt (!! config) <-> InA (@equiv _ location_Setoid) pt (List.map get_location (config_list config))
 := fun config => spect_from_config_spec config origin.


(** **  Definition of the robogram  **)

Open Scope R_scope.
(* Open Scope VectorSpace_scope. *)

(** The robogram solving the gathering problem in R². *)
Definition ffgatherR2_pgm (s : spectrum) : @path location location_Setoid :=
  paths_in_R2 (isobarycenter (elements s)).

Instance ffgatherR2_pgm_compat : Proper (equiv ==> equiv) ffgatherR2_pgm.
Proof.
intros ? ? ?. unfold ffgatherR2_pgm, paths_in_R2.
now apply local_straight_path_compat, isobarycenter_compat, elements_compat.
Qed.

Definition ffgatherR2 : robogram := {| pgm := ffgatherR2_pgm |}.


(** **  Decreasing measure ensuring termination  **)

(** ***  Global decreasing measure  **)

Definition max_dist_spect (s : spectrum) : R :=
  max_dist_list_list (elements s) (elements s).

Instance max_dist_spect_compat : Proper (equiv ==> eq) max_dist_spect.
Proof. intros ? ? Heq. unfold max_dist_spect. now rewrite Heq. Qed.

Lemma max_dist_spect_le :
  forall (s : spectrum) pt0 pt1,
    InA equiv pt0 (elements s) ->
    InA equiv pt1 (elements s) ->
    dist pt0 pt1 <= max_dist_spect s.
Proof. intros. now apply max_dist_list_list_le. Qed.

Lemma max_dist_spect_ex :
  forall (s : spectrum),
    elements s <> nil ->
    exists pt0 pt1, 
      InA equiv pt0 (elements s)
      /\ InA equiv pt1 (elements s)
      /\ dist pt0 pt1 = max_dist_spect s.
Proof. intros. now apply max_dist_list_list_ex. Qed.


(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

(** A non-negative measure *)
Definition measure (conf: configuration) : R :=
  max_dist_spect (!! conf).

Instance measure_compat : Proper (equiv ==> eq) measure.
Proof. intros ? ? Heq. unfold measure. now rewrite Heq. Qed.

Lemma measure_nonneg : forall config, 0 <= measure config.
Proof.
intros config. unfold measure.
destruct (elements (!! config)) as [| pt l] eqn:Heq.
+ elim (elements_non_nil _ Heq).
+ rewrite <- (R2_dist_defined_2 pt). apply max_dist_spect_le; rewrite Heq; now left.
Qed.

(** The minimum value 0 is reached only on gathered configurations. *)
Lemma gathered_elements : forall config pt,
  gathered_at pt config <-> PermutationA (@equiv _ location_Setoid) (elements (!! config)) (pt :: nil).
Proof.
intros config pt.
split; intro H.
* apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply elements_NoDupA.
  + repeat constructor. intro Hin. inv Hin.
  + intro pt'.
    rewrite elements_spec, spect_from_config_spec, map_id, (@config_list_InA _ _ Info).
    split; intro Hin.
    - destruct Hin as [id Hid]. revert Hid. pattern id. apply no_byz. clear id; intros g Hid.
      specialize (H g). rewrite H in Hid. rewrite Hid. now left.
    - inv Hin; try (now rewrite InA_nil in *); [].
      exists (Good g1). now rewrite (H g1).
* intro id.
  assert (Hin : InA equiv (get_location (config (Good id))) (elements (!! config))).
  { simpl get_location. unfold Datatypes.id.
    rewrite elements_spec, spect_from_config_spec, map_id, (@config_list_InA _ _ Info).
    eexists; reflexivity. }
  rewrite H in Hin. now inv Hin.
Qed.

Lemma gathered_measure : forall config, measure config = 0%R <-> exists pt, gathered_at pt config.
Proof.
intros config. split; intro H.
* unfold measure, max_dist_spect in *.
  assert (Hnil := elements_non_nil config).
  assert (Hdup := elements_NoDupA (!! config)).
  setoid_rewrite gathered_elements.
  induction (elements (!! config)) as [| pt l]; try tauto; [].
  exists pt. destruct l as [| pt' l]; try reflexivity.
  inv Hdup. destruct IHl as [? Hperm]; discriminate || auto.
  + apply antisymmetry.
    - rewrite <- H. apply max_dist_list_list_cons_le.
    - rewrite <- (R2_dist_defined_2 pt'). apply max_dist_list_list_le; now left.
  + assert (l = nil).
    { rewrite <- length_zero_iff_nil.
      cut (length (pt' :: l) = length (x :: nil)); try (simpl; omega).
      f_equiv; eauto. }
    subst. rewrite PermutationA_1 in Hperm; autoclass; [].
    elim H2. left.
    cbn in H. do 2 rewrite R2_dist_defined_2 in H.
    cbn in H. setoid_rewrite (Rmax_comm 0)%R in H. rewrite (Rmax_left 0 0)%R in H; try reflexivity; [].
    rewrite dist_sym in H. repeat (rewrite (Rmax_left (dist pt' pt) 0) in H; try apply dist_nonneg).
    rewrite Rmax_left in H; try reflexivity; [].
    symmetry. now rewrite <- dist_defined.
* destruct H as [pt Hgather]. unfold measure.
  destruct (max_dist_spect_ex (!! config) (elements_non_nil config)) as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]].
  rewrite <- Heq, dist_defined. rewrite gathered_elements in Hgather. rewrite Hgather in *.
  inv Hpt1; inv Hpt2; try (now rewrite InA_nil in *); [].
  etransitivity; eauto.
Qed.

Lemma update_morph : forall (sim : similarity location) config g traj choice,
  @equiv location state_Setoid
    (@update _ _ _ _ _ _ _ _ _ _ UpdFun
       (map_config (projT1 (existT precondition sim I)) config) g sim (lift_path sim traj) choice)
    (lift (existT precondition sim I) (update config g Similarity.id traj choice)).
Proof.
intros sim config g traj choice.
simpl update. unfold id.
rewrite Rmult_1_l, Similarity.dist_prop, Rle_bool_mult_l; try apply Similarity.zoom_pos; [].
destruct_match_eq Hle; reflexivity.
Qed.

Lemma lift_update_swap : forall da config1 config2 g target,
  @equiv location _
    (lift (existT precondition (frame_choice_bijection (change_frame da config1 g ⁻¹))
                               (precondition_satisfied_inv da config1 g))
          (update config2
           g (change_frame da config1 g) target (choose_update da config2 g target)))
    (update (map_config (lift (existT precondition (frame_choice_bijection (change_frame da config1 g ⁻¹))
                                      (precondition_satisfied_inv da config1 g)))
                        config2)
            g Similarity.id
            (lift_path (frame_choice_bijection (change_frame da config1 g ⁻¹)) target)
            (choose_update da config2 g target)).
Proof.
intros da config1 config2 g target. cbn -[inverse]. unfold id.
rewrite Similarity.dist_prop, Rmult_1_l.
destruct_match_eq Hle; destruct_match_eq Hle'; try reflexivity; [|];
rewrite Rle_bool_true_iff, Rle_bool_false_iff in *;
exfalso; revert_one not; intro Hgoal; apply Hgoal.
- assert (Hzoom := Similarity.zoom_pos (change_frame da config1 g)).
  eapply Rmult_le_reg_l; eauto; []. simpl.
  rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l; trivial; [].
  changeR2. lra.
- assert (Hzoom := Similarity.zoom_pos (change_frame da config1 g ⁻¹)).
  eapply Rmult_le_reg_l; eauto; []. simpl.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; trivial; [].
  changeR2. generalize (Similarity.zoom_pos (change_frame da config1 g)). lra.
Qed.

(** Rewriting the [round] function in the global setting. *)
Theorem round_simplify : forall da config, FSYNC_da da ->
  round ffgatherR2 da config
  == fun id => match id with
                 | Byz b => config (Byz b) (* dummy case *)
                 | Good g => let global_trajectory := straight_path (get_location (config (Good g)))
                                                                    (isobarycenter (elements (!! config))) in
                             let choice := da.(choose_update) config g global_trajectory in
                             update config g Similarity.id global_trajectory choice
               end.
Proof.
intros da config Hfsync. rewrite FSYNC_round_simplify; trivial; [].
apply no_byz_eq. intro g. unfold round.
assert (supp_nonempty := elements_non_nil config).
assert (Hda := similarity_center da config g).
remember (change_frame da config g) as sim.
assert (Hsim : Proper (equiv ==> equiv) sim). { intros ? ? Heq. now rewrite Heq. }
Local Opaque lift. Local Opaque map_config.
assert (Hperm : PermutationA equiv (List.map sim (elements (!! config)))
                                   (elements (elt := location)
                                             (!! (map_config (lift (existT precondition sim I)) config)))).
{ rewrite <- map_injective_elements, spect_from_config_map, spect_from_config_ignore_snd;
  autoclass; reflexivity || apply Bijection.injective. }
rewrite spect_from_config_ignore_snd.
simpl pgm. unfold ffgatherR2_pgm. changeR2.
remember (elements (!! config)) as E.
remember (elements (!! (map_config (lift (State := OnlyLocation)
                                         (existT (fun _ : location -> location => True) sim I)) config))) as E'.
Time rewrite <- Hperm, isobarycenter_sim_morph; trivial; [].
rewrite get_location_lift. simpl precondition.
replace (precondition_satisfied (proj_sim_da da) config g) with I;
try (now destruct (precondition_satisfied (proj_sim_da da) config g)); [].
change (projT1 (existT _ ?x _)) with x.
assert (Hpath : paths_in_R2 (Bijection.section (Similarity.sim_f sim) (isobarycenter E))
                == lift_path sim (straight_path (Similarity.center sim) (isobarycenter E))).
{ intro r. cbn [path_f lift_path straight_path paths_in_R2 local_straight_path].
  rewrite sim_add, sim_mul, sim_add, sim_opp. changeR2.
  rewrite Similarity.center_prop, opp_origin, add_origin, add_origin_l.
  simpl; f_equal; simpl; field. }
(* rewrite Hpath.
intro. simpl. reflexivity.
rewrite update_morph.
rewrite lift_update_swap.
assert (lift_path (Bijection.inverse sim) (paths_in_R2 (sim (isobarycenter E)))
        == straight_path (get_location (config (Good g))) (isobarycenter E)).
{ intro r. cbn [path_f lift_path straight_path paths_in_R2 local_straight_path].
  rewrite (sim_mul (sim⁻¹)). changeR2.
  change (sim ⁻¹ (sim (isobarycenter E)))%VS with ((sim ⁻¹ ∘ sim) (isobarycenter E))%VS.
  rewrite Similarity.compose_inverse_l. change (Similarity.id (isobarycenter E)) with (isobarycenter E).
  rewrite Hda. unfold Rminus.
  rewrite mul_distr_add, <- add_morph, minus_morph, mul_opp, mul_1, 2 add_assoc.
  apply add_compat; try reflexivity; []. apply add_comm. }
apply get_location_compat, update_compat, choose_update_compat; auto.
Qed.
*) Admitted.

(** If possible, the measure decreases by at least delta at each step. *)
(* FIXME: cleanup! *)
Theorem round_lt_config : forall da config,
    delta > 0 ->
    FSYNC_da da ->
    delta <= measure config ->
    measure (round ffgatherR2 da config) <= measure config - delta.
Proof.
  intros da config Hdelta HFSync Hnotdone.
  set (elems := elements (!! config)).
  set (C := isobarycenter elems).
  remember (elements (!! (round ffgatherR2 da config))) as nxt_elems.

  assert (Hantec: forall KP, InA equiv KP nxt_elems ->
            exists Pid, InA equiv (get_location (config Pid)) elems /\ round ffgatherR2 da config Pid == KP).
  { intros [KP k'] HinKP.
    rewrite Heqnxt_elems, elements_spec, spect_from_config_In in HinKP.
    destruct HinKP as [Pid HPid].
    exists Pid. split; trivial; [].
    unfold elems. rewrite elements_spec, spect_from_config_In.
    now exists Pid. }

  assert (Hrobot_move_less_than_delta:
            forall id,
              InA equiv (get_location (config id)) elems ->
              delta > dist (get_location (config id)) C ->
              get_location (round ffgatherR2 da config id) == C).
  { intro id. pattern id. apply no_byz. clear id.
    intros g Hin HdeltaP.
    rewrite (round_simplify _ _ HFSync (Good g)).
    cbn zeta.
    edestruct (ratio_spec config g) as [Heq | [Heq Hle]]; try rewrite Heq.
    + rewrite straight_path_1. reflexivity.
    + exfalso.
      rewrite Heq in Hle. clear Heq.
      remember (move_ratio (choose_update da config g (straight_path
                 (get_location (config (Good g))) (isobarycenter (elements !! config))))) as r.
    cbn [straight_path path_f] in Hle.
    rewrite <- add_origin in Hle at 1. setoid_rewrite add_comm in Hle.
    rewrite dist_translation in Hle.
    rewrite mul_distr_add, mul_opp, dist_sym, <- R2dist_ref_0, dist_homothecy in Hle.
    assert (0 <= r <= 1) by apply ratio_bounds.
    rewrite Rabs_pos_eq in Hle; try tauto; [].
    apply (Rlt_irrefl delta). eapply Rle_lt_trans; [| eassumption].
    rewrite dist_sym. setoid_rewrite <- Rmult_1_l.
    etransitivity; try apply Hle; []. apply Rmult_le_compat_r.
    - apply dist_nonneg.
    - tauto. }

  assert (Hrobot_move:
            forall g,
              InA equiv (get_location (config (Good g))) elems ->
              delta <= dist (config (Good g)) C ->
              exists r : ratio, round ffgatherR2 da config (Good g)
                                == (config (Good g) + r * (C - (config (Good g))))%VS
                     /\ delta <= norm (r * (C - (config (Good g))))%VS).
  { intros g Hin HdeltaP.
    setoid_rewrite (round_simplify _ _ HFSync (Good g)).
    cbn zeta.
    edestruct (ratio_spec config g) as [Heq | [Heq Hle]]; try setoid_rewrite Heq.
    + exists ratio_1. setoid_rewrite straight_path_1.
      split; try reflexivity; [].
      now rewrite mul_1, <- norm_dist, dist_sym.
    + remember (move_ratio (choose_update da config g (straight_path
       (get_location (config (Good g))) (isobarycenter (elements !! config))))) as r.
      exists r. split; try reflexivity; [].
      rewrite Heq in Hle. cbn [straight_path path_f] in Hle.
      rewrite norm_dist, opp_distr_add, add_assoc, add_opp in Hle.
      rewrite add_comm, add_origin, norm_opp, Rmult_1_l in Hle. apply Hle. }

  assert (MainArgument: forall KP KQ, InA equiv KP nxt_elems -> InA equiv KQ nxt_elems ->
          dist KP KQ <= max_dist_spect (!! config) - delta).
  { intros KP KQ HinKP HinKQ.
    apply Hantec in HinKP.
    apply Hantec in HinKQ.
    destruct HinKP as [[Pid | []] [HinP HroundP]]; try omega; [].
    destruct HinKQ as [[Qid | []] [HinQ HroundQ]]; try omega; [].
    destruct (Rle_dec delta (dist (get_location (config (Good Pid))) C)),
             (Rle_dec delta (dist (get_location (config (Good Qid))) C)).
    * (* Both P and Q are more than delta away from C *)
      assert (HinPP := HinP).
      apply Hrobot_move in HinP; [|assumption].
      assert (HinQQ := HinQ).
      apply Hrobot_move in HinQ; [|assumption].
      destruct HinP as [kp [kp_def Hkplow]],
               HinQ as [kq [kq_def Hkqlow]].
      rewrite kp_def in HroundP.
      rewrite kq_def in HroundQ.

      assert (HPnotC : get_location (config (Good Pid)) =/= C).
      { intro H.
        apply (Rlt_irrefl 0).
        eapply Rlt_le_trans; eauto; [].
        apply dist_defined in H.
        now rewrite H in *. }
      assert (HQnotC: get_location (config (Good Qid)) =/= C).
      { intro H.
        apply (Rlt_irrefl 0).
        eapply Rlt_le_trans; eauto; [].
        apply dist_defined in H.
        now rewrite H in *. }

      assert (0 <= kp <= 1) by apply ratio_bounds.
      assert (0 <= kq <= 1) by apply ratio_bounds.
      (* Wlog. we assume that kp <= kq *)
      destruct (Rle_dec kp kq).
      + apply Rle_trans with (r2 := (1 - kp) * (max_dist_spect (!! config))).
        - rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
          apply distance_after_move; try assumption.
          ++ apply isobarycenter_dist_decrease.
             -- apply elements_non_nil.
             -- intros; now apply max_dist_spect_le.
             -- now subst elems.
          ++ apply max_dist_spect_le; now subst elems.
          ++ cut (proj_ratio kp <> 0%R); try lra.
             intro Habs. rewrite Habs, mul_0, norm_origin in Hkplow. lra.
          ++ tauto.
        - cut (delta <= kp * max_dist_spect !! config); try lra; [].
          apply (Rle_trans _ _ _ Hkplow).
          rewrite norm_mul, Rabs_pos_eq; try tauto; [].
          apply Rmult_le_compat_l; try tauto; [].
          rewrite <- norm_dist, dist_sym.
          apply isobarycenter_dist_decrease.
          ++ apply elements_non_nil.
          ++ intros. apply max_dist_spect_le; now subst elems.
          ++ assumption.
      + apply Rle_trans with (r2 := (1 - kq) * (max_dist_spect (!! config))).
        - rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
          rewrite dist_sym.
          apply distance_after_move; try assumption || lra.
          ++ apply isobarycenter_dist_decrease.
             -- apply elements_non_nil.
             -- intros. apply max_dist_spect_le; now subst elems.
             -- assumption.
          ++ apply max_dist_spect_le; now subst elems.
          ++ cut (proj_ratio kq <> 0%R); try lra.
             intro Habs. rewrite Habs, mul_0, norm_origin in Hkqlow. lra.
        - cut (delta <= kq * max_dist_spect !! config); try lra; [].
          apply (Rle_trans _ _ _ Hkqlow).
          rewrite norm_mul, Rabs_pos_eq; try tauto; [].
          apply Rmult_le_compat_l; try tauto; [].
          rewrite <- norm_dist, dist_sym.
          apply isobarycenter_dist_decrease.
          ++ apply elements_non_nil.
          ++ intros. apply max_dist_spect_le; now subst elems.
          ++ assumption.
    * (* Q is close to C but not P *)
      assert (HinPP := HinP).
      apply Hrobot_move in HinP; [|assumption].
      assert (HinQQ := HinQ).
      apply Hrobot_move_less_than_delta in HinQ; try lra; [].
      destruct HinP as [kp [kp_def Hkplow]].
      assert (0 <= kp <= 1) by apply ratio_bounds.
      rewrite kp_def in HroundP.
      rewrite HinQ in HroundQ.
      rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
      apply Rle_trans with (r2 := dist (config (Good Pid)) C - delta).
      + rewrite norm_dist.
        assert (Heq : (config (Good Pid) + kp * (C - config (Good Pid)) - C
                       == (1 + - kp) * -(C - config (Good Pid)))%VS).
        { symmetry. rewrite <- add_morph, mul_1.
          now rewrite mul_opp, minus_morph, opp_opp, <- add_assoc, opp_distr_add, opp_opp,
                      (add_comm (-C)), <- add_assoc, (add_comm (-C)). }
        rewrite Heq, norm_mul, norm_opp, dist_sym, norm_dist, Rabs_pos_eq,
                Rmult_plus_distr_r, Rmult_1_l, <- Ropp_mult_distr_l; try lra; [].
        apply Rplus_le_compat_l, Ropp_le_contravar.
        rewrite norm_mul, Rabs_pos_eq in Hkplow; trivial; lra.
      + apply Rplus_le_compat_r.
        apply isobarycenter_dist_decrease.
        - apply elements_non_nil.
        - intros. apply max_dist_spect_le; now subst elems.
        - assumption.
    * (* P is close to C but not Q *)
      assert (HinPP := HinP).
      apply Hrobot_move_less_than_delta in HinP; try lra; [].
      assert (HinQQ := HinQ).
      apply Hrobot_move in HinQ; [|assumption].
      destruct HinQ as [kq [kq_def Hkqlow]].
      assert (0 <= kq <= 1) by apply ratio_bounds.
      rewrite HinP in HroundP.
      rewrite kq_def in HroundQ.
      rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
      apply Rle_trans with (r2 := dist (config (Good Qid)) C - delta).
      + rewrite dist_sym, norm_dist.
        assert (Heq : (config (Good Qid) + kq * (C - config (Good Qid)) - C
                       == (1 + - kq) * -(C - config (Good Qid)))%VS).
        { symmetry. rewrite <- add_morph, mul_1.
          now rewrite mul_opp, minus_morph, opp_opp, <- add_assoc, opp_distr_add, opp_opp,
                      (add_comm (-C)), <- add_assoc, (add_comm (-C)). }
        rewrite Heq, norm_mul, norm_opp, dist_sym, norm_dist, Rabs_pos_eq,
                Rmult_plus_distr_r, Rmult_1_l, <- Ropp_mult_distr_l; try lra; [].
        apply Rplus_le_compat_l, Ropp_le_contravar.
        rewrite norm_mul, Rabs_pos_eq in Hkqlow; trivial; lra.
      + apply Rplus_le_compat_r.
        apply isobarycenter_dist_decrease.
        - apply elements_non_nil.
        - intros. apply max_dist_spect_le; now subst elems.
        - assumption.
    * (* Both P and Q are close to C *)
      apply Hrobot_move_less_than_delta in HinP; try lra; [].
      apply Hrobot_move_less_than_delta in HinQ; try lra; [].
      rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
      rewrite HinP, HinQ.
      assert (Heq0 : dist C C = 0) by now rewrite dist_defined.
      rewrite Heq0.
      unfold measure in Hnotdone. lra. }

  unfold measure.
  generalize (max_dist_spect_ex (!! (round ffgatherR2 da config))).
  intros Hmax_dist_ex.
  assert (Hspect_non_nil : nxt_elems <> nil).
  { rewrite Heqnxt_elems. apply elements_non_nil. }
  rewrite <- Heqnxt_elems in Hmax_dist_ex.
  destruct (Hmax_dist_ex Hspect_non_nil) as [pt0 [pt1 [Hin0 [Hin1 Hdist]]]].
  rewrite <- Hdist.
  now auto.
Qed.

(** If the measure is too small, it saturates at 0. *)
Theorem round_last_step : forall da config,
    delta > 0 ->
    FSYNC_da da ->
    measure config <= delta ->
    measure (round ffgatherR2 da config) == 0.
Proof.
intros da config Hdelta HFSync Hlt.
unfold measure.
set (elems := (elements (!! config))).
set (C := isobarycenter elems).
pose (nxt_elems := elements (!! (round ffgatherR2 da config))).
assert (Hantec : forall KP, InA equiv KP nxt_elems ->
                   exists g, InA equiv (get_location (config (Good g))) elems
                          /\ get_location (round ffgatherR2 da config (Good g)) == KP).
{ intros [KP k'] HinKP.
  unfold nxt_elems in HinKP. rewrite elements_spec, spect_from_config_In in HinKP.
  destruct HinKP as [id Hid].
  destruct id as [g | b]; try (destruct b; omega); [].
  exists g. split; trivial; [].
  unfold elems. rewrite elements_spec, spect_from_config_In.
  now exists (Good g). }
assert (HonlyC: forall KP, InA equiv KP nxt_elems -> KP == C).
{ intros KP HinKP.
  destruct (Hantec KP HinKP) as [g [Hin Hround]].
  rewrite <- Hround in *. clear Hround KP.
  rewrite (round_simplify _ _ HFSync (Good g)).
  cbn zeta.
  edestruct (ratio_spec config g) as [Hupdate | Hupdate]; try rewrite Hupdate.
  + (* valid case: mvt smaller than delta *)
    rewrite straight_path_1. reflexivity.
  + (* mvt at least delta: it is exactly delta *)
    destruct Hupdate as [Hupdate Hle]. rewrite Hupdate in *.
    remember (move_ratio (choose_update da config g
               (straight_path (get_location (config (Good g))) (isobarycenter (elements !! config))))) as r.
    cbn [straight_path path_f] in Hle.
    rewrite <- add_origin in Hle at 1. setoid_rewrite add_comm in Hle.
    rewrite dist_translation in Hle.
    rewrite mul_distr_add, mul_opp, dist_sym, <- R2dist_ref_0, dist_homothecy in Hle.
    assert (0 <= r <= 1) by apply ratio_bounds.
    rewrite Rabs_pos_eq in Hle; try tauto; [].
    assert (Hmeasure : forall p1 p2, InA equiv p1 elems -> InA equiv p2 elems -> dist p1 p2 <= measure config).
    { intros p1 p2 Hin1 Hin2. now apply max_dist_spect_le. }
    assert (Hle' := isobarycenter_dist_decrease elems (measure config) (elements_non_nil config) Hmeasure _ Hin).
    clear Hupdate Heqr Hmeasure. rewrite dist_sym in Hle'.
    assert (Hr : r == ratio_1).
    { apply (Rmult_eq_reg_r delta); try lra; [].
      rewrite Rmult_1_l. apply antisymmetry.
      - rewrite <- Rmult_1_l. apply Rmult_le_compat_r; lra || tauto.
      - rewrite Rmult_1_l in Hle. etransitivity; eauto; [].
        apply Rmult_le_compat_l; try tauto; []. etransitivity; eauto. }
    rewrite Hr. rewrite straight_path_1. reflexivity. }
destruct (max_dist_spect_ex _ (elements_non_nil (round ffgatherR2 da config)))
  as [pt0 [pt1 [Hinpt0 [Hinpt1 Hdist]]]].
rewrite <- Hdist, HonlyC, (HonlyC pt1); try (now subst); [].
now apply dist_defined.
Qed.

Definition lt_config delta x y :=
  lt (Z.to_nat (up (measure x / delta))) (Z.to_nat (up (measure y / delta))).

Lemma wf_lt_config (delta: R) (Hdeltapos: delta > 0) : well_founded (lt_config delta).
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply lt_wf.
Qed.

Lemma lt_config_decrease : forall delta config1 config2, 0 < delta ->
  measure config1 <= measure config2 - delta -> lt_config delta config1 config2.
Proof.
intros delta config1 config2 Hdelta Hle. unfold lt_config.
rewrite <- Z2Nat.inj_lt.
+ apply Zup_lt. field_simplify; try lra. unfold Rdiv. apply Rmult_le_compat.
  - apply measure_nonneg.
  - apply Rlt_le. now apply Rinv_0_lt_compat.
  - lra.
  - reflexivity.
+ apply le_IZR. transitivity (measure config1 / delta).
  - simpl. apply Rdiv_le_0_compat; trivial. apply measure_nonneg.
  - apply Rlt_le, (proj1 (archimed _)).
+ apply le_IZR. transitivity (measure config2 / delta).
  - simpl. apply Rdiv_le_0_compat; trivial. apply measure_nonneg.
  - apply Rlt_le, (proj1 (archimed _)).
Qed.

(** ***  With the termination, the rest of the proof is easy  **)

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (config id) config.
Proof.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. revert id. apply no_byz, Hgather.
Qed.
(*
Corollary not_gathered_generalize : forall config id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, ~config id == pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => R2dec_bool (config x) pt) names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite R2dec_bool_true_iff in Hall.
  hnf. repeat rewrite Hall; trivial; apply In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']].
  rewrite negb_true_iff, R2dec_bool_false_iff in Hid'.
  now exists id'.
Qed.
*)
Lemma gathered_at_elements : forall config pt,
  gathered_at pt config -> PermutationA equiv (elements (!! config)) (pt :: nil).
Proof.
intros config pt Hgather.
apply NoDupA_equivlistA_PermutationA; autoclass.
+ apply elements_NoDupA.
+ repeat constructor. now rewrite InA_nil.
+ intro x.
  rewrite elements_spec, spect_from_config_spec, map_id, (@config_list_InA _ _ Info).
  split; intro Hin.
  - destruct Hin as [id Hid]. left. rewrite Hid. pattern id. apply no_byz. intro. now rewrite <- Hgather.
  - exists (Good g1). inv Hin; try (now rewrite InA_nil in *); [].
    transitivity pt; trivial; []. symmetry. now rewrite <- Hgather.
Qed.

Lemma gathered_at_forever : forall da config pt, FSYNC_da da ->
  gathered_at pt config -> gathered_at pt (round ffgatherR2 da config).
Proof.
intros da config pt Hda Hgather g.
rewrite round_simplify; trivial; []. cbn zeta.
rewrite (gathered_at_elements Hgather), isobarycenter_singleton.
rewrite Hgather, update_no_move; autoclass.
Qed.

Lemma gathered_at_OK : forall d conf pt, FSYNC (similarity_demon2demon d) ->
  gathered_at pt conf -> Gather pt (execute ffgatherR2 d conf).
Proof.
cofix Hind. intros d conf pt [] Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind; now try apply gathered_at_forever.
Qed.

(*
Lemma not_isobarycenter_moves:
  forall d config gid,
    delta > 0 ->
    FullySynchronous d ->
    config gid =/= isobarycenter (elements (!! config)) ->
    round ffgatherR2 (Stream.hd d) config gid =/= config gid.
Proof.
intros d config id. pattern id. apply no_byz. clear id.
intros g Hdelta HFSync Hnotbary Hnotmove.
apply Hnotbary. clear Hnotbary. revert Hnotmove.
rewrite round_simplify.
destruct HFSync as [Hd _]. rewrite <- similarity2demon_hd, Hd.
cbn zeta. cbn -[dist add opp mul equiv].
destruct_match.
+ rewrite <- (add_origin (config (Good g))) at 4.
  intro Heq. apply add_reg_l in Heq. apply mul_integral in Heq.
  destruct Heq as [Heq | Heq].
  - match goal with H : delta <= _ |- _ => rename H into Hle end.
    rewrite Heq, mul_0, add_origin, R2_dist_defined_2 in Hle. lra.
  - now rewrite R2sub_origin in Heq.
+ rewrite mul_1. unfold id. rewrite <- (add_origin (config (Good g))) at 3.
  intro Heq. apply add_reg_l in Heq. now rewrite R2sub_origin in Heq.
Qed.
*)

(** The final theorem. *)
Theorem FSGathering_in_R2 :
  forall d, delta > 0 -> FSYNC (similarity_demon2demon d) -> FullSolGathering ffgatherR2 d.
Proof.
intros d Hdelta HFS config. revert d HFS. pattern config.
apply (well_founded_ind (wf_lt_config Hdelta)). clear config.
intros config Hind [da d] [Hda HFS].
(* Are we already gathered? *)
destruct (gathered_at_dec config (config (Good g1))) as [Hmove | Hmove];
[| destruct (gathered_at_dec (round ffgatherR2 da config)
                             (round ffgatherR2 da config (Good g1))) as [Hmove' | Hmove']].
* (* If we are already gathered, not much to do *)
  exists (config (Good g1)). now apply Stream.Now, gathered_at_OK.
* (* If we are gathered at the next step, not much to do either. *)
  exists (round ffgatherR2 da config (Good g1)).
  apply Stream.Later, Stream.Now. rewrite execute_tail. now apply gathered_at_OK.
* (* General case, use [round_lt_config] *)
  assert (delta <= measure config).
  { apply Rnot_lt_le. intro Habs. destruct HFS.
    eapply Rlt_le, (round_last_step da) in Habs; eauto; [].
    simpl equiv in Habs. rewrite gathered_measure in Habs. destruct Habs as [pt Habs].
    apply Hmove'. apply (gathered_precise Habs (Good g1)). }
  destruct HFS, (Hind (round ffgatherR2 da config)) with d as [pt Hpt].
  + apply lt_config_decrease; trivial; [].
    change da with (Stream.hd (Stream.cons da d)).
    now apply round_lt_config.
  + now constructor.
  + exists pt. apply Stream.Later. apply Hpt.
Qed.

Print Assumptions FSGathering_in_R2.
(* FIXME: find and eliminate the use of Classical_Prop.classic
          It comes from a bug in intuition/tauto. See set_spectrum.v. *)
