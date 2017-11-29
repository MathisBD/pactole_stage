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
Require Pactole.Spaces.R. (* for R_Setoid, R_EqDec *)
Require Import Pactole.Spaces.R2.
Require Import Pactole.Gathering.Definitions.


Set Implicit Arguments.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter n : nat.
Axiom size_G : (2 <= n)%nat.

(* FIXME: remove when FSetList is done *)
Context {FS : FSet R2}.
Context {FSpec : FSetSpecs FS}.

(** There are n good robots and no byzantine ones. *)
Instance MyRobots : Names := Robots n 0.

Existing Instance R2_Setoid.
Existing Instance R2_EqDec.
Existing Instance R2_RMS.

(* We are in a flexible formalism with no other info than the location,
   so the demon only chooses the move ratio. *)
Instance FlexChoice : update_choice ratio := Flexible.OnlyFlexible.

Parameter delta : R.

Instance UpdFun : update_function ratio := {|
  update := fun config g trajectory ρ => let pt' := trajectory ρ in
              if Rle_dec delta (dist (config (Good g)) pt') then pt' else trajectory ratio_1 |}.
Proof.
intros ? ? Hconfig ? g ? ? ? Hpt [? Hρ1] [ρ Hρ2] Heq.
simpl in Heq. subst. rewrite Hpt, Hconfig. cbn zeta.
assert (Heq : y0 (exist (fun x : R => 0 <= x <= 1) ρ Hρ1)%R
           == y0 (exist (fun x : R => 0 <= x <= 1) ρ Hρ2)%R) by f_equiv.
rewrite Heq. now destruct_match; f_equiv.
Defined.

Instance Flex : Flexible.FlexibleUpdate delta.
Proof.
split. intros da config g target. cbn -[dist].
destruct_match; unfold id; tauto.
Qed.

(* Trying to avoid notation problem with implicit arguments *)
Notation "!! config" := (@spect_from_config R2 R2 _ _ _ _ _ _ set_spectrum config origin) (at level 1).
(* (@spect_from_config R2 Datatypes.unit _ _ _ _ _ _ multiset_spectrum) (at level 1). *)
Notation "x == y" := (equiv x y).
Notation spectrum := (@spectrum R2 R2 _ R2_EqDec _ R2_EqDec _ MyRobots set_spectrum).
Notation robogram := (@robogram R2 R2 _ _ _ _ _ MyRobots set_spectrum).
Notation configuration := (@configuration R2 _ _ _ _).
Notation config_list := (@config_list R2 _ _ _ _).
Notation round := (@round R2 R2 _ _ _ _ _ _ _ _).
Notation execution := (@execution R2 R2 _ _ _ _ _).
Notation Sadd := (FSetInterface.add).

Implicit Type config : configuration.
Implicit Type da : similarity_da.
Implicit Type d : similarity_demon.
Arguments origin : simpl never.
Arguments dist : simpl never.

(* The robot trajectories are straight paths. *)
Definition path_R2 := path R2.
Definition paths_in_R2 : R2 -> path_R2 := local_straight_path.
Coercion paths_in_R2 : R2 >-> path_R2.

Instance paths_in_R2_compat : Proper (equiv ==> equiv) paths_in_R2.
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
exists 0. abstract (pose (Hle := size_G); omega).
Defined.

(* Definition Spect_map f s := Spect.M.fold (fun e acc => Spect.M.add (f e) acc) s Spect.M.empty. *)

Lemma map_sim_support : forall (sim : similarity R2) s,
  PermutationA equiv (elements (map sim s)) (List.map sim (elements s)).
Proof. intros. apply map_injective_elements; autoclass; apply Similarity.injective. Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall config, !! config =/= empty.
Proof.
intros config Habs.
specialize (Habs (get_location (config (Good g1)))). rewrite empty_spec in Habs.
rewrite <- Habs. apply pos_in_config.
Qed.

Lemma support_non_nil : forall config, elements (!! config) <> nil.
Proof. intro. rewrite elements_nil. apply spect_non_nil. Qed.

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall (config : configuration) pt,
  In pt (!! config) <-> InA equiv pt (List.map get_location (config_list config))
 := fun config => @spect_from_config_spec R2 R2 _ _ _ _ _ _ _ config origin.


(** **  Definition of the robogram  **)

Open Scope R_scope.

(** The robogram solving the gathering problem in R². *)
Definition ffgatherR2_pgm (s : spectrum) : path R2 :=
  paths_in_R2 (barycenter (elements s)).

Instance ffgatherR2_pgm_compat : Proper (equiv ==> equiv) ffgatherR2_pgm.
Proof.
intros ? ? ?. unfold ffgatherR2_pgm, paths_in_R2.
now apply local_straight_path_compat, barycenter_compat, elements_compat.
Qed.

Definition ffgatherR2 : robogram := {| pgm := ffgatherR2_pgm |}.

Close Scope R_scope.


(** **  Decreasing measure ensuring termination  **)

(** ***  Global decreasing measure  **)


Open Scope R_scope.

(* Coercion Spect.Names.names : list Spect.Names.Internals.ident >-> list Spect.Names.ident. *)

Definition max_dist_R2_pt_list (pt : R2) (s : list R2) : R :=
  fold_right (fun pt1 max => Rmax (dist pt pt1) max) 0 s.


(* Lemma max_dist_R2_pt_list_compat : Proper (R2.eq ==> PermutationA R2.eq ==> Logic.eq) max_dist_R2_pt_list. *)

Lemma max_dist_R2_pt_list_le : forall pt l pt1,
  InA equiv pt1 l -> dist pt pt1 <= max_dist_R2_pt_list pt l.
Proof.
intros pt l pt1 Hin1.
induction l as [| e l].
+ now rewrite InA_nil in *.
+ simpl.
  inv Hin1.
  - match goal with H : _ == _ |- _ => rewrite H end.
    apply Rmax_l.
  - unfold max_dist_R2_pt_list in *. simpl.
    eapply Rle_trans; [now apply IHl | apply Rmax_r].
Qed.

Lemma max_dist_not_first :
  forall pt pt1 l,
    max_dist_R2_pt_list pt (pt1 :: l) <> dist pt pt1 ->
    l <> nil /\
    max_dist_R2_pt_list pt (pt1 :: l) = max_dist_R2_pt_list pt l.
Proof.
  intros pt pt1 l Hnotfirst.
  unfold max_dist_R2_pt_list in Hnotfirst.
  simpl in Hnotfirst.
  unfold Rmax at 1 in Hnotfirst.
  unfold max_dist_R2_pt_list at 1. simpl.
  unfold Rmax at 1.
  destruct (Rle_dec (dist pt pt1)
                  (fold_right (fun (pt1 : R2) (max : R) => Rmax (dist pt pt1) max) 0 l)).
  split.
  intro.
  apply Hnotfirst.
  rewrite H in *.
  simpl in *.
  assert (0 <= dist pt pt1).
  apply dist_pos.
  destruct H0.
  assert (dist pt pt1 < dist pt pt1).
  now apply Rle_lt_trans with (r2 := 0).
  exfalso.
  apply (Rlt_irrefl _ H1).
  assumption.
  reflexivity.
  now elim Hnotfirst.
Qed.

Lemma max_dist_R2_pt_list_ex :
  forall pt l,
    l <> nil ->
    exists pt1, InA equiv pt1 l /\ dist pt pt1 = max_dist_R2_pt_list pt l.
Proof.
  intros pt l Hl.
  induction l.
  + now elim Hl.
  + destruct (Req_dec (dist pt a) (max_dist_R2_pt_list pt (a :: l))).
    - exists a.
      split.
      now left.
      assumption.
    - assert (Hmax: max_dist_R2_pt_list pt (a::l) = max_dist_R2_pt_list pt l).
      { apply max_dist_not_first.
        intro. apply H. now rewrite H0. }
      assert (Hlnotnil: l <> nil).
      { generalize (max_dist_not_first pt a l).
        intro.
        apply H0.
        intro. apply H. now rewrite H1. }
      destruct (IHl Hlnotnil). destruct H0.
      exists x.
      split.
      now right.
      now rewrite Hmax.
Qed.

Lemma max_dist_R2_pt_list_0 : forall pt l, max_dist_R2_pt_list pt l = 0 <-> forall x, InA equiv x l -> x == pt.
Proof.
intros pt l. destruct l as [| pt' l].
* cbn. setoid_rewrite InA_nil. tauto.
* split; intro H.
  + intros x Hin. assert (Hle := max_dist_R2_pt_list_le pt Hin).
    rewrite H in Hle. symmetry. rewrite <- dist_defined. apply antisymmetry; trivial. apply dist_pos.
  + destruct (@max_dist_R2_pt_list_ex pt (pt' :: l) ltac:(discriminate)) as [? [Hin Heq]].
    apply H in Hin. subst. rewrite <- Heq, dist_defined. now symmetry.
Qed.

Definition max_dist_R2_list_list (l1: list R2) (l2: list R2): R :=
  fold_right (fun pt0 max => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1.

Lemma max_dist_R2_list_list_le :
  forall pt1 l1 pt2 l2,
    InA equiv pt1 l1 -> InA equiv pt2 l2 -> dist pt1 pt2 <= max_dist_R2_list_list l1 l2.
Proof.
  intros pt1 l1 pt2 l2 Hin1 Hin2.
  induction l1.
  + now rewrite InA_nil in Hin1.
  + inv Hin1.
    - unfold max_dist_R2_list_list. simpl.
      apply Rle_trans with (r2 := max_dist_R2_pt_list pt1 l2).
      now apply max_dist_R2_pt_list_le.
      match goal with H : _ == _ |- _ => rewrite H end.
      now apply Rmax_r.
    - unfold max_dist_R2_list_list. simpl.
      eapply Rle_trans; [now apply IHl1 | apply Rmax_l].
Qed.

Lemma max_dist_R2_list_list_ex :
  forall l1 l2,
    l1 <> nil ->
    l2 <> nil ->
    exists pt1 pt2, InA equiv pt1 l1 /\ InA equiv pt2 l2 /\ dist pt1 pt2 = max_dist_R2_list_list l1 l2.
Proof.
  intros l1 l2 Hl1notnil Hl2notnil.
  induction l1.
  + now elim Hl1notnil.
  + unfold max_dist_R2_list_list.
    simpl.
    unfold Rmax at 1.
    destruct (Rle_dec (fold_right (fun (pt0 : R2) (max : R) => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1)
         (max_dist_R2_pt_list a l2)).
    - exists a.
      destruct (max_dist_R2_pt_list_ex a Hl2notnil) as [? [? ?]].
      exists x. split.
      now left.
      now split.
    - clear Hl1notnil.
      assert (Hl1notnil: l1 <> nil).
      { intro. subst. simpl in *.
        match goal with H : ~ _ |- _ => apply H end.
        induction l2.
        unfold max_dist_R2_pt_list. simpl. apply Rle_refl.
        simpl. apply Rle_trans with (r2 := dist a a0).
        apply dist_pos.
        apply Rmax_l. }
      destruct (IHl1 Hl1notnil) as [? [? [? [? ?]]]].
      exists x, x0.
      split.
      now right.
      now split.
Qed.

Lemma max_dist_R2_list_list_cons_le : forall pt l,
  max_dist_R2_list_list l l <= max_dist_R2_list_list (pt :: l) (pt :: l).
Proof.
intros pt [| pt' l].
- cbn. rewrite R2_dist_defined_2. now repeat rewrite Rmax_left.
- destruct (@max_dist_R2_list_list_ex (pt' :: l) (pt' :: l))
    as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]]; try discriminate; [].
  rewrite <- Heq. apply max_dist_R2_list_list_le; now right.
Qed.

Definition max_dist_spect (s : spectrum) : R :=
  max_dist_R2_list_list (elements s) (elements s).

Lemma max_dist_spect_le :
  forall (s : spectrum) pt0 pt1,
    InA equiv pt0 (elements s) ->
    InA equiv pt1 (elements s) ->
    dist pt0 pt1 <= max_dist_spect s.
Proof. intros. now apply max_dist_R2_list_list_le. Qed.

Lemma max_dist_spect_ex :
  forall (s : spectrum),
    elements s <> nil ->
    exists pt0 pt1, 
      InA equiv pt0 (elements s)
      /\ InA equiv pt1 (elements s)
      /\ dist pt0 pt1 = max_dist_spect s.
Proof. intros. now apply max_dist_R2_list_list_ex. Qed.


(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Definition measure (conf: configuration) : R :=
  max_dist_spect (!! conf).

Lemma measure_nonneg : forall config, 0 <= measure config.
Proof.
intros config. unfold measure.
destruct (elements (!! config)) as [| pt l] eqn:Heq.
+ elim (support_non_nil _ Heq).
+ rewrite <- (R2_dist_defined_2 pt). apply max_dist_spect_le; rewrite Heq; now left.
Qed.

Lemma gathered_support : forall config pt,
  gathered_at pt config <-> PermutationA equiv (elements (!! config)) (pt :: nil).
Proof.
intros config pt.
split; intro H.
* apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply elements_NoDupA.
  + repeat constructor. intro Hin. inv Hin.
  + intro pt'.
    rewrite elements_spec, spect_from_config_spec, map_id, config_list_InA.
    split; intro Hin.
    - destruct Hin as [id Hid]. revert Hid. pattern id. apply no_byz. clear id; intros g Hid.
      specialize (H g). rewrite H in Hid. rewrite Hid. now left.
    - inv Hin; try (now rewrite InA_nil in *); [].
      exists (Good g1). now rewrite (H g1).
* intro id.
  assert (Hin : InA equiv (get_location (config (Good id))) (elements (!! config))).
  { simpl get_location. unfold Datatypes.id.
    rewrite elements_spec, spect_from_config_spec, map_id, config_list_InA. eexists; reflexivity. }
  rewrite H in Hin. now inv Hin.
Qed.

Lemma gathered_measure : forall config, measure config = 0 <-> exists pt, gathered_at pt config.
Proof.
intros config. split; intro H.
* unfold measure, max_dist_spect in *.
  assert (Hnil := support_non_nil config).
  assert (Hdup := elements_NoDupA (!! config)).
  setoid_rewrite gathered_support.
  induction (elements (!! config)) as [| pt l]; try tauto; [].
  exists pt. destruct l as [| pt' l]; try reflexivity.
  inv Hdup. destruct IHl; discriminate || auto.
  + apply antisymmetry.
    - rewrite <- H. apply max_dist_R2_list_list_cons_le.
    - rewrite <- (R2_dist_defined_2 pt'). apply max_dist_R2_list_list_le; now left.
  + assert (l = nil).
    { rewrite <- length_zero_iff_nil.
      cut (length (pt' :: l) = length (x :: nil)); try (simpl; omega).
      f_equiv; eauto. }
    subst. rewrite PermutationA_1 in H0; autoclass; []. subst.
    elim H2. left.
    cbn in H. do 2 rewrite R2_dist_defined_2 in H.
    cbn in H. setoid_rewrite (Rmax_comm 0) in H. rewrite (Rmax_left 0 0) in H; try reflexivity; [].
    rewrite dist_sym in H. repeat (rewrite (Rmax_left (dist pt pt') 0) in H; try apply dist_pos).
    rewrite Rmax_left in H; try reflexivity; [].
    now rewrite <- dist_defined.
* destruct H as [pt Hgather]. unfold measure.
  destruct (max_dist_spect_ex (!! config) (support_non_nil config)) as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]].
  rewrite <- Heq, dist_defined. rewrite gathered_support in Hgather. rewrite Hgather in *.
  inv Hpt1; inv Hpt2; try (now rewrite InA_nil in *); [].
  etransitivity; eauto.
Qed.

Lemma fold_mult_plus_distr : forall (f : R2 -> R) coeff E init,
  fold_left (fun acc pt => acc + coeff * (f pt)) E (coeff * init) =
  coeff * (fold_left (fun acc pt => acc + (f pt)) E init).
Proof.
  intros f coeff E.
  induction E; intro init.
  + now simpl.
  + simpl.
    rewrite <- Rmult_plus_distr_l.
    now apply IHE.
Qed.

Lemma dist_prop_retraction : forall (sim : similarity R2) (x y : R2),
  dist ((sim ⁻¹) x) ((sim ⁻¹) y) = /(Similarity.zoom sim) * dist x y.
Proof. intros sim x y. rewrite Similarity.dist_prop. now simpl. Qed.

Theorem round_simplify : forall da config,
  round ffgatherR2 da config
  == fun id => if da.(activate) id
               then match id with
                      | Byz b => config (Byz b) (* dummy case *)
                      | Good g => let global_trajectory :=
                                    straight_path (get_location (config (Good g)))
                                                  (barycenter (elements (!! config))) in
                                  let choice := da.(choose_update) config g global_trajectory in
                                  update config g global_trajectory choice
                    end
               else config id.
Proof.
intros da config. apply no_byz_eq. intro g. hnf. unfold round.
assert (supp_nonempty := support_non_nil config).
remember (frame_choice_bijection (change_frame da config g)) as sim.
destruct (activate da (Good g)) eqn:Hstep; trivial; [].
assert (Hsim : Proper (equiv ==> equiv) sim). { intros ? ? Heq. now rewrite Heq. }
Local Opaque app. Local Opaque map_config.
simpl pgm. unfold ffgatherR2_pgm.
assert (Hperm : PermutationA equiv (List.map sim (elements (!! config)))
                            (elements (!! (map_config (app sim) config)))).
{ rewrite <- map_injective_elements, spect_from_config_map, spect_from_config_ignore_snd;
  autoclass; reflexivity || apply Bijection.injective. }
repeat rewrite spect_from_config_ignore_snd.
remember (elements (!! config)) as E.
remember (elements (!! (map_config (app sim) config))) as E'.
unfold update. cbn -[add opp mul lift_path].
rewrite R2norm_mul.
rewrite <- R2norm_dist.
assert (Hsimbary : (sim ⁻¹) (barycenter E') = barycenter E).
{ rewrite HeqE' in *.
  rewrite <- barycenter_sim.
  + apply barycenter_compat.
    rewrite <- Spect.map_injective_elements; autoclass.
    - rewrite Spect.from_config_map, Config.map_merge; autoclass.
      rewrite HeqE. do 2 f_equiv.
      rewrite <- (Config.map_id config) at 2. f_equiv.
      intros x y Hxy.
      rewrite <- (Config.app_id y); try reflexivity; [].
      change (Config.app id y) with (Config.app Sim.id y).
      rewrite <- (Sim.compose_inverse_l sim).
      symmetry. simpl. apply Config.app_compose; autoclass; now symmetry.
    - apply Sim.injective.
  + rewrite <- length_zero_iff_nil, <- Spect.from_config_map; autoclass.
    rewrite Spect.map_injective_elements; autoclass; try apply Sim.injective.
    now rewrite map_length, <- HeqE, length_zero_iff_nil. }
assert (Htest : Rle_bool delta (R2.dist ((sim ⁻¹) (r * barycenter E')%R2) pt)
                = Rle_bool delta (Rabs r * R2.dist (barycenter E) pt)).
{ f_equal.
  assert (Heq_pt : pt = (sim ⁻¹) (sim pt)).
  { simpl. rewrite Bijection.retraction_section; autoclass. }
  assert (Hsim_pt : R2.eq (sim pt) (r * (sim pt))).
  { generalize (Sim.center_prop sim).
    intro Hzero.
    apply step_center with (c := pt) in Hstep.
    simpl in Hstep. rewrite <- Heqsim in Hstep.
    now rewrite <- Hstep, Hzero, R2.mul_origin. }
  rewrite Heq_pt at 1.
  rewrite dist_prop_retraction, Hsim_pt, R2mul_dist, <- Rmult_assoc.
  pattern (/ Sim.zoom sim * Rabs r).
  rewrite Rmult_comm, Rmult_assoc. f_equal.
  rewrite <- dist_prop_retraction, <- Heq_pt. f_equal. assumption. }
rewrite Htest.
destruct (Rle_bool delta (Rabs r * R2.dist (barycenter E) pt)); trivial; [].
apply Bijection.Inversion.
simpl Bijection.retraction. change Common.Sim.sim_f with Sim.sim_f.
rewrite sim_add, sim_mul, sim_add, sim_opp.
do 2 rewrite R2.mul_distr_add.
assert (Hsim_pt_0 : R2.eq (sim pt) R2.origin).
{ apply (step_center da (Good g) pt) in Hstep.
  rewrite <- sim.(Sim.center_prop), <- Hstep. cbn. now subst sim. }
rewrite Hsim_pt_0.
rewrite (R2.add_comm R2.origin), R2.add_origin.
setoid_rewrite <- R2.add_origin at 25. repeat rewrite <- R2.add_assoc. f_equiv.
+ f_equiv. rewrite Bijection.Inversion. apply Hsimbary.
+ rewrite R2.opp_origin, R2.add_origin.
  setoid_rewrite <- R2.mul_1 at 9 15. repeat rewrite <- ?R2.minus_morph, ?R2.mul_morph, ?R2.add_morph.
  ring_simplify (r * 2 + (r * -1 + (1 - r + -1))). apply R2.mul_0.
Qed.


(* FIXME: cleanup! *)
Theorem round_lt_config : forall d config,
    delta > 0 ->
    FullySynchronous d ->
    delta <= measure config ->
    measure (round ffgatherR2 (Stream.hd d) config) <= measure config - delta.
Proof.
  intros d config Hdelta HFSync Hnotdone.
  destruct (elements (!! config)) as [| pt [| pt' ?]] eqn:Hmax.
  - (* No robots *)
    exfalso. now apply (support_non_nil config).
  - (* Done *)
    assert (Habs : measure config = 0).
    { rewrite gathered_measure. exists pt. now rewrite gathered_support, Hmax. }
    rewrite Habs in *. elim (Rlt_irrefl delta). now apply Rle_lt_trans with 0.
  - (* Now to some real work. *)
    remember (Stream.hd d) as da.
    remember (elements (!! config)) as elems.
    set (C := barycenter elems).
    remember (elements (!! (round ffgatherR2 da config))) as nxt_elems.
    assert (Hantec: forall KP, InA equiv KP nxt_elems ->
              exists Pid, InA equiv (get_location (config Pid)) elems /\ round ffgatherR2 da config Pid == KP).
    { intros KP HinKP.
      rewrite Heqnxt_elems in HinKP.
      rewrite elements_spec in HinKP.
      generalize (spect_from_config_spec (round ffgatherR2 da config)).
      intro Hok. unfold spect_is_ok in Hok.
      rewrite Hok in HinKP. clear Hok.
      rewrite InA_map_iff in HinKP; autoclass; []. setoid_rewrite config_list_InA in HinKP.
      destruct HinKP as [state [Hstate [Pid HPid]]].
      exists Pid.
      split; [| now rewrite <- Hstate, HPid].
      rewrite Heqelems, elements_spec. apply pos_in_config.
    }

    assert (Hrobot_move_less_than_delta:
              forall Pid,
                InA equiv (get_location (conf Pid)) elems ->
                delta > dist (config Pid) C ->
                round ffgatherR2 da config Pid == C).
    { intros Pid HinP HdeltaP.
      rewrite (round_simplify _ _ _ Pid).
      remember (step da Pid) as Pact.
      destruct Pact.
      + simpl.
        destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems.
          destruct p.
          unfold Rle_bool.
          destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))) as [ Hdmove | Hdmove ].
          * assert (Hr: 0 <= snd (t, r) <= 1).
            { apply (step_flexibility da Pid). now symmetry. } simpl in Hr.
            destruct Hr as [Hr0 Hr1].
            destruct Hr1.
            ++ exfalso.
               rewrite R2norm_mul in Hdmove.
               rewrite <- R2norm_dist in Hdmove.
               rewrite R2.dist_sym in Hdmove.
               apply Rlt_irrefl with (r := delta).
               apply (Rle_lt_trans _ _ _ Hdmove).
               apply Rgt_lt in HdeltaP.
               apply Rlt_trans with (r2 := R2.dist (conf Pid) C);
                 [ | assumption].
               rewrite <- Rmult_1_l.
               apply Rmult_lt_compat_r.
               -- apply Rlt_le_trans with (r2 := delta).
                  ** now apply Rgt_lt.
                  ** apply (Rle_trans _ _ _ Hdmove).
                     rewrite <- Rmult_1_l.
                     apply Rmult_le_compat_r.
                     +++ apply R2.dist_pos.
                     +++ apply Rabs_le.
                         split.
                     --- apply Rle_trans with (r2 := -0).
                         apply Ropp_ge_le_contravar.
                         apply Rle_ge.
                         apply Rle_0_1.
                         now rewrite Ropp_0.
                     --- now left.
               -- apply Rabs_def1. assumption. apply Rlt_le_trans with (r2 := 0).
                  apply Rlt_le_trans with (r2 := -0).
                  apply Ropp_gt_lt_contravar.
                  apply Rlt_gt.
                  apply Rlt_0_1.
                  now rewrite Ropp_0.  assumption.
            ++ subst r. rewrite R2.mul_1.
               rewrite R2.add_assoc.
               pattern (conf Pid + barycenter elems)%R2.
               rewrite R2.add_comm.
               rewrite <- R2.add_assoc.
               rewrite R2.add_opp.
               rewrite R2.add_origin.
               now subst C.
          * now subst C.
      + unfold FullySynchronous in HFSync.
        unfold FullySynchronousInstant in HFSync.
        destruct d.
        simpl in Heqda.
        destruct HFSync.
        destruct (H Pid).
        simpl.
        subst d.
        now symmetry.
    }

    assert (Hrobot_move:
              forall Pid,
                In (Config.loc (conf Pid)) elems ->
                delta <= R2.dist (conf Pid) C ->
                exists k, R2.eq (round delta ffgatherR2 da conf Pid)
                                (conf Pid + k * (C - (conf Pid)))%R2
                       /\ 0 <= k <= 1
                       /\ delta <= R2norm (k * (C - (conf Pid)))).
    { intros Pid HinP HdeltaP.
      setoid_rewrite (round_simplify _ _ _ Pid).
      remember (step da Pid) as Pact.
      destruct Pact.
      + destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems.
          destruct p.
          unfold Rle_bool.
          destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))) as [ Hdmove | Hdmove ].
          * assert (Hr: 0 <= snd (t, r) <= 1).
            { apply (step_flexibility da Pid). now symmetry. } simpl in Hr.
            exists r.
            repeat split; tauto.
          * exists 1.
            repeat split.
            ++ rewrite R2.mul_1.
               rewrite R2.add_comm.
               rewrite <- R2.add_assoc.
               pattern (- conf Pid + conf Pid)%R2.
               now rewrite R2.add_comm, R2.add_opp, R2.add_origin.
            ++ apply Rle_0_1.
            ++ apply Rle_refl.
            ++ now rewrite R2.mul_1, <- R2norm_dist, R2.dist_sym.
      + unfold FullySynchronous in HFSync.
        unfold FullySynchronousInstant in HFSync.
        destruct d.
        simpl in Heqda.
        destruct HFSync.
        destruct (H Pid).
        simpl.
        subst d.
        now symmetry.
    }

    assert (MainArgument: forall KP KQ, In KP nxt_elems -> In KQ nxt_elems ->
            R2.dist KP KQ <= max_dist_spect (!! conf) - delta).
    { intros KP KQ HinKP HinKQ.
      apply Hantec in HinKP.
      apply Hantec in HinKQ.
      destruct HinKP as [Pid [HinP HroundP]].
      destruct HinKQ as [Qid [HinQ HroundQ]].

      destruct (Rle_dec delta (R2.dist (conf Pid) C)), (Rle_dec delta (R2.dist (conf Qid) C)).
      + generalize HinP.
        apply Hrobot_move in HinP; [|assumption].
        intro HinPP.
        generalize HinQ.
        apply Hrobot_move in HinQ; [|assumption].
        intro HinQQ.
        destruct HinP as [kp [kp_def [Hkple1 Hkplow]]].
        destruct HinQ as [kq [kq_def [Hkqle1 Hkqlow]]].
        rewrite kp_def in HroundP.
        rewrite kq_def in HroundQ.

        assert (HPnotC: ~ R2.eq (conf Pid) C).
        { intro.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (r2 := delta).
          assumption.
          apply R2.dist_defined in H.
          rewrite H in r.
          assumption. }
        assert (HQnotC: ~ R2.eq (conf Qid) C).
        { intro.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (r2 := delta).
          assumption.
          apply R2.dist_defined in H.
          rewrite H in r0.
          assumption. }

        destruct (Rle_dec kp kq).
        - apply Rle_trans with (r2 := (1 - kp) * (max_dist_spect (!! conf))).
          * rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
            apply distance_after_move; try assumption.
            apply barycenter_dist_decrease with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            clear r1.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            destruct (Rlt_dec 0 kp); try assumption.
            exfalso.
            apply n.
            destruct Hkple1 as [[Hkplt0 | Hkpeq0] _].
            assumption.
            subst kp.
            apply Rlt_le_trans with (r2 := delta).
            assumption.
            rewrite R2.mul_0 in Hkplow.
            rewrite R2norm_origin in Hkplow.
            assumption.
            now destruct Hkqle1.
          * rewrite Rmult_comm.
            rewrite Rmult_minus_distr_l.
            rewrite Rmult_1_r.
            apply Rplus_le_compat_l.
            apply Ropp_ge_le_contravar.
            apply Rle_ge.
            apply (Rle_trans _ _ _ Hkplow).
            rewrite R2norm_mul.
            rewrite Rabs_pos_eq.
            rewrite Rmult_comm.
            apply Rmult_le_compat_r.
            now destruct Hkple1.
            rewrite <- R2norm_dist.
            rewrite R2.dist_sym.
            apply barycenter_dist_decrease with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            now destruct Hkple1.
        - apply Rle_trans with (r2 := (1 - kq) * (max_dist_spect (!! conf))).
          * rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
            rewrite R2.dist_sym.
            apply distance_after_move; try assumption.
            apply barycenter_dist_decrease with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            clear n.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            destruct (Rlt_dec 0 kq); try assumption.
            exfalso.
            apply n0.
            destruct Hkqle1 as [[Hkqlt0 | Hkqeq0] _].
            assumption.
            subst kq.
            apply Rlt_le_trans with (r2 := delta).
            assumption.
            rewrite R2.mul_0 in Hkqlow.
            rewrite R2norm_origin in Hkqlow.
            assumption.
            left. now apply Rnot_le_lt.
            now destruct Hkple1.
          * rewrite Rmult_comm.
            rewrite Rmult_minus_distr_l.
            rewrite Rmult_1_r.
            apply Rplus_le_compat_l.
            apply Ropp_ge_le_contravar.
            apply Rle_ge.
            apply (Rle_trans _ _ _ Hkqlow).
            rewrite R2norm_mul.
            rewrite Rabs_pos_eq.
            rewrite Rmult_comm.
            apply Rmult_le_compat_r.
            now destruct Hkqle1.
            rewrite <- R2norm_dist.
            rewrite R2.dist_sym.
            apply barycenter_dist_decrease with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            now destruct Hkqle1.

      + generalize HinP.
        apply Hrobot_move in HinP; [|assumption].
        intro HinPP.
        generalize HinQ.
        apply Hrobot_move_less_than_delta in HinQ.
        intro HinQQ.
        destruct HinP as [kp [kp_def [Hkple1 Hkplow]]].
        rewrite kp_def in HroundP.
        rewrite HinQ in HroundQ.

        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
        apply Rle_trans with (r2 := R2.dist (conf Pid) C - delta).
        rewrite R2norm_dist.
        assert (conf Pid + kp * (C - conf Pid) - C = (1 + - kp) * (conf Pid - C))%R2.
        { symmetry. rewrite <- R2.add_morph.
          rewrite R2.mul_1.
          replace (conf Pid - C)%R2 with (- (C - conf Pid))%R2 at 2.
          rewrite R2.mul_opp.
          rewrite R2.minus_morph.
          rewrite R2.opp_opp.
          rewrite <- R2.add_assoc.
          rewrite R2.add_comm with (u := (-C)%R2).
          now rewrite R2.add_assoc.
          rewrite R2.opp_distr_add.
          rewrite R2.opp_opp.
          now rewrite R2.add_comm.
        }
        rewrite H.
        rewrite R2norm_mul.
        rewrite R2norm_dist.
        rewrite Rabs_pos_eq.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <- Ropp_mult_distr_l.
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite <- R2norm_dist.
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        rewrite <- Rabs_pos_eq with (x := kp).
        now rewrite <- R2norm_mul.
        now destruct Hkple1.
        apply Rplus_le_reg_r with (r := kp).
        rewrite Rplus_0_l.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        now destruct Hkple1.
        apply Rplus_le_compat_r.
        apply barycenter_dist_decrease with (E := elems).
        subst elems.
        rewrite Hmax; intro; discriminate.
        intros. apply max_dist_spect_le.
        now subst elems.
        now subst elems.
        now subst C.
        assumption.
        now apply Rnot_le_gt.

      + generalize HinQ.
        apply Hrobot_move in HinQ; [|assumption].
        intro HinQQ.
        generalize HinP.
        apply Hrobot_move_less_than_delta in HinP.
        intro HinPP.
        destruct HinQ as [kq [kq_def [Hkqle1 Hkqlow]]].
        rewrite kq_def in HroundQ.
        rewrite HinP in HroundP.

        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
        apply Rle_trans with (r2 := R2.dist (conf Qid) C - delta).
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        assert (conf Qid + kq * (C - conf Qid) - C = (1 + - kq) * (conf Qid - C))%R2.
        { symmetry. rewrite <- R2.add_morph.
          rewrite R2.mul_1.
          replace (conf Qid - C)%R2 with (- (C - conf Qid))%R2 at 2.
          rewrite R2.mul_opp.
          rewrite R2.minus_morph.
          rewrite R2.opp_opp.
          rewrite <- R2.add_assoc.
          rewrite R2.add_comm with (u := (-C)%R2).
          now rewrite R2.add_assoc.
          rewrite R2.opp_distr_add.
          rewrite R2.opp_opp.
          now rewrite R2.add_comm.
        }
        rewrite H.
        rewrite R2norm_mul.
        rewrite R2norm_dist.
        rewrite Rabs_pos_eq.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <- Ropp_mult_distr_l.
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite <- R2norm_dist.
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        rewrite <- Rabs_pos_eq with (x := kq).
        now rewrite <- R2norm_mul.
        now destruct Hkqle1.
        apply Rplus_le_reg_r with (r := kq).
        rewrite Rplus_0_l.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        now destruct Hkqle1.
        apply Rplus_le_compat_r.
        apply barycenter_dist_decrease with (E := elems).
        subst elems.
        rewrite Hmax; intro; discriminate.
        intros. apply max_dist_spect_le.
        now subst elems.
        now subst elems.
        now subst C.
        assumption.
        now apply Rnot_le_gt.

      + apply Hrobot_move_less_than_delta in HinP.
        apply Hrobot_move_less_than_delta in HinQ.
        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
        rewrite HinP, HinQ.
        assert (R2.dist C C = 0).
        { rewrite R2.dist_defined. apply R2.eq_equiv. }
        rewrite H.
        apply Rplus_le_reg_r with (r := delta).
        rewrite Rplus_0_l.
        assert (max_dist_spect (!! conf) - delta + delta = max_dist_spect (!! conf)) by ring.
        rewrite H0.
        apply Hnotdone.
        now apply Rnot_le_gt.
        now apply Rnot_le_gt.
    }

    unfold measure.
    generalize (max_dist_spect_ex (!!(round delta ffgatherR2 da conf))).
    intros Hmax_dist_ex.
    assert (Hspect_non_nil: nxt_elems <> nil).
    { rewrite Heqnxt_elems.
      apply support_non_nil. }
    rewrite <- Heqnxt_elems in Hmax_dist_ex.
    destruct (Hmax_dist_ex Hspect_non_nil) as [pt0 [pt1 [Hin0 [Hin1 Hdist]]]].
    rewrite <- Hdist.
    now auto.
Qed.

(* FIXME: cleanup! *)
Theorem round_last_step : forall d config,
    delta > 0 ->
    FullySynchronous d ->
    measure config <= delta ->
    measure (round ffgatherR2 (Stream.hd d) config) = 0.
Proof.
intros [da d] config Hdelta HFS Hlt.
unfold measure.
remember (elements (!! config)) as elems.
set (C := barycenter elems).
remember (elements (!! (round ffgatherR2 da config))) as nxt_elems.
assert (Hantec: forall KP, InA equiv KP nxt_elems ->
                  exists Pid, InA equiv (get_location (config Pid)) elems /\ round ffgatherR2 da config Pid == KP).
{ intros KP HinKP.
  rewrite Heqnxt_elems, elements_spec in HinKP.
  generalize (spect_from_config_spec (round ffgatherR2 da config)).
  intro Hok. unfold spect_is_ok in Hok.
  rewrite Hok in HinKP. clear Hok.
  rewrite InA_map_iff in HinKP; autoclass; []. setoid_rewrite config_list_InA in HinKP.
  destruct HinKP as [state [Hstate [Pid HPid]]].
  exists Pid.
  split; [|now rewrite <- Hstate, HPid].
  rewrite Heqelems, elements_spec. apply pos_in_config.
}

assert (HonlyC: forall KP, In KP nxt_elems -> KP == C).
{ intros KP HinKP.
  destruct (Hantec KP HinKP) as [Pid [HinP HroundP]].
  rewrite <- HroundP in *. clear HroundP KP.
  rewrite (round_simplify _ _ _ Pid).
  destruct (step da Pid) eqn:HeqPact.
  * destruct p. simpl.
    rewrite <- Heqelems.
    unfold Rle_bool.
    destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))).
    + assert (Hr: 0 <= snd (t, r) <= 1).
      { apply step_flexibility with da Pid. now symmetry. }
      simpl in Hr.
      destruct Hr as [Hr0 Hr1].
      destruct Hr1 as [Hrlt1 | Hreq1].
      - exfalso.
        apply Rlt_irrefl with delta.
        apply (Rle_lt_trans _ _ _ r0).
        rewrite R2norm_mul.
        rewrite (Rabs_pos_eq _ Hr0).
        rewrite <- R2norm_dist.
        assert (Hle : R2.dist (barycenter elems) (conf Pid) <= delta).
        { rewrite R2.dist_sym.
          apply Rle_trans with (measure conf); trivial; [].
          apply barycenter_dist_decrease with elems; auto; [|].
          - rewrite Heqelems, <- Spect.MProp.MP.elements_Empty.
            intro Hempty. now apply Spect.MProp.MP.empty_is_empty_1, spect_non_nil in Hempty.
          - intros. unfold measure. apply max_dist_spect_le; now rewrite <- Heqelems. }
        (* There should be a lemma for this in standard library. *)
        rewrite <- Rmult_1_l.
        destruct Hle.
        -- apply Rmult_le_0_lt_compat; try assumption.
           apply R2.dist_pos.
        -- subst delta.
           apply Rmult_lt_compat_r.
           now apply Rlt_gt.
           assumption.
      - subst r.
        rewrite R2.mul_1, R2.add_comm, <- R2.add_assoc.
        pattern (- conf Pid + conf Pid)%R2.
        rewrite R2.add_comm, R2.add_opp, R2.add_origin.
        now unfold C.
    + now unfold C.
  * unfold FullySynchronous in HFS.
    inversion HFS.
    unfold FullySynchronousInstant in H.
    destruct (H Pid). now symmetry. }
destruct (max_dist_spect_ex (!! (round delta ffgatherR2 da conf)))
as [pt0 [pt1 [Hinpt0 [Hinpt1 Hdist]]]].
apply support_non_nil.
simpl. rewrite <- Hdist.
rewrite HonlyC.
rewrite (HonlyC pt1).
now apply R2.dist_defined.
now subst nxt_elems.
now subst nxt_elems.
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

Lemma gathered_at_elements : forall config pt,
  gathered_at pt config -> PermutationA equiv (elements (!! config)) (pt :: nil).
Proof.
intros config pt Hgather.
apply NoDupA_equivlistA_PermutationA; autoclass.
+ apply elements_NoDupA.
+ repeat constructor. now rewrite InA_nil.
+ intro x.
  rewrite elements_spec, spect_from_config_spec, map_id, config_list_InA.
  split; intro Hin.
  - destruct Hin as [id Hid]. left. rewrite Hid. pattern id. apply no_byz. intro. now rewrite <- Hgather.
  - exists (Good g1). inv Hin; try (now rewrite InA_nil in *); [].
    transitivity pt; trivial; []. symmetry. now rewrite <- Hgather.
Qed.

Lemma gathered_at_forever : forall da config pt,
  gathered_at pt config -> gathered_at pt (round ffgatherR2 da config).
Proof.
intros da config pt Hgather g. rewrite round_simplify.
cbn zeta.
rewrite (gathered_at_elements Hgather), barycenter_singleton.
now destruct_match; rewrite Hgather, ?update_no_move.
Qed.

Lemma gathered_at_OK : forall d conf pt,
  gathered_at pt conf -> Gather pt (execute ffgatherR2 d conf).
Proof.
cofix Hind. intros d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.


Lemma not_barycenter_moves:
  forall d config gid,
    delta > 0 ->
    FullySynchronous d ->
    config gid =/= barycenter (elements (!! config)) ->
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

(** The final theorem. *)
Theorem FSGathering_in_R2 :
  forall d, delta > 0 -> FullySynchronous d -> FullSolGathering ffgatherR2 d.
Proof.
intros d Hdelta HFS config. revert d HFS. pattern config.
apply (well_founded_ind (wf_lt_config Hdelta)). clear config.
intros config Hind [da d] HFS.
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
  { apply Rnot_lt_le. intro Habs. eapply Rlt_le, round_last_step in Habs; eauto; [].
    rewrite gathered_measure in Habs. destruct Habs as [pt Habs]. simpl in Habs.
    apply Hmove'. apply (gathered_precise Habs (Good g1)). }
  destruct (Hind (round ffgatherR2 da config)) with d as [pt Hpt].
  + apply lt_config_decrease; trivial; [].
    change da with (Stream.hd (Stream.cons da d)).
    now apply round_lt_config.
  + now destruct HFS.
  + exists pt. apply Stream.Later. apply Hpt.
Qed.

Print Assumptions FSGathering_in_R2.

End GatheringinR2.
