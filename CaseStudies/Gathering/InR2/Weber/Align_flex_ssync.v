
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* Author : Mathis Bouverot-Dupuis (June 2022).

 * This file implements an algorithm to ALIGN all robots on an arbitrary 
 * axis, in the plane (R²). The algorithm assumes there are no byzantine robots,
 * and works in a FLEXIBLE and SEMI-SYNCHRONOUS setting. 

 * The algorithm is as follows : all robots go towards the 'weber point' of 
 * the configuration. The weber point, also called geometric median, is unique 
 * if the robots are not aligned, and has the property that moving any robot
 * towards the weber point in a straight line doesn't change the weber point. 
 * It thus remains at the same place throughout the whole execution.  *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Lia Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import FunInd.
Require Import FMapFacts.

(* Helping typeclass resolution avoid infinite loops. *)
Typeclasses eauto := (bfs).

(* Pactole basic definitions *)
Require Export Pactole.Setting.
(* Specific to R^2 topology *)
Require Import Pactole.Spaces.R2.
(* Specific to gathering *)
Require Pactole.CaseStudies.Gathering.WithMultiplicity.
Require Import Pactole.CaseStudies.Gathering.Definitions.
(* Specific to multiplicity *)
Require Import Pactole.Observations.MultisetObservation.
(* Specific to flexibility *)
Require Import Pactole.Models.Flexible.
(* Specific to settings with no Byzantine robots *)
Require Import Pactole.Models.NoByzantine.
(* Utility lemmas. *)
Require Import Pactole.CaseStudies.Gathering.InR2.Weber.Utils.
(* Specific to definition and properties of the weber point. *)
Require Import Pactole.CaseStudies.Gathering.InR2.Weber.Weber_point.

(* User defined *)
Import Permutation.
Import Datatypes.


Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.


Section Alignment.
Local Existing Instances dist_sum_compat.

(* We assume the existence of a function that calculates a weber point of a collection
 * (even when the weber point is not unique).
 * This is a very strong assumption : such a function may not exist in closed form, 
 * and the Weber point can only be approximated. *)
Axiom weber_calc : list R2 -> R2.
Axiom weber_calc_correct : forall ps, Weber ps (weber_calc ps).
(* We also suppose this function doesn't depend on the order of the points. 
* This is probably not necessary (we can show that it holds when the points aren't colinear) 
* but simplifies the proof a bit. *)
Axiom weber_calc_compat : Proper (PermutationA equiv ==> equiv) weber_calc.
Local Existing Instance weber_calc_compat.
  
(* The number of robots *)
Variables n : nat.
Hypothesis lt_0n : 0 < n.

(* There are no byzantine robots. *)
Local Instance N : Names := Robots n 0.
Local Instance NoByz : NoByzantine.
Proof using . now split. Qed.

Lemma list_in_length_n0 {A : Type} x (l : list A) : List.In x l -> length l <> 0.
Proof using . intros Hin. induction l as [|y l IH] ; cbn ; auto. Qed.

Lemma byz_impl_false : B -> False.
Proof using . 
intros b. assert (Hbyz := In_Bnames b). 
apply list_in_length_n0 in Hbyz. 
rewrite Bnames_length in Hbyz.
cbn in Hbyz. intuition.
Qed.

(* Use this tactic to solve any goal
 * provided there is a byzantine robot as a hypothesis. *)
Ltac byz_exfalso :=
  match goal with 
  | b : ?B |- _ => exfalso ; apply (byz_impl_false b)
  end.

(* Since all robots are good robots, we can define a function
 * from identifiers to good identifiers. *)
Definition unpack_good (id : ident) : G :=
  match id with 
  | Good g => g 
  | Byz _ => ltac:(byz_exfalso)
  end.

Lemma good_unpack_good id : Good (unpack_good id) == id.
Proof using . unfold unpack_good. destruct_match ; [auto | byz_exfalso]. Qed.

Lemma unpack_good_good g : unpack_good (Good g) = g.
Proof using . reflexivity. Qed.  

(* The robots are in the plane (R^2). *)
Local Instance Loc : Location := make_Location R2.
Local Instance LocVS : RealVectorSpace location := R2_VS.
Local Instance LocES : EuclideanSpace location := R2_ES.

(* Refolding typeclass instances *)
Ltac foldR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change state_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change state_EqDec with location_EqDec in *;
  change R2_VS with LocVS in *;
  change R2_ES with LocES in *.

(* Robots don't have a state (and thus no memory) apart from their location. *)
Local Instance St : State location := OnlyLocation (fun f => True).
(* Robots choose their destination and also the path they take to this destination. *)
Local Instance RobotC : robot_choice (path location) := {| robot_choice_Setoid := @path_Setoid _ location_Setoid |}.

(* Robots view the other robots' positions up to a similarity. *)
Local Instance FrameC : frame_choice (similarity location) := FrameChoiceSimilarity.
Local Instance UpdateC : update_choice ratio := OnlyFlexible.
Local Instance InactiveC : inactive_choice unit := NoChoiceIna.

(* In a flexible setting, the minimum distance that robots are allowed to move is delta. *)
Variables delta : R.
Hypothesis delta_g0 : (0 < delta)%R.

(* We are in a flexible and semi-synchronous setting (for now). *)
Local Instance UpdateF : update_function (path location) (similarity location) ratio := 
  FlexibleUpdate delta. 
(* We are in a semi-synchronous setting : inactive robots don't move. *)
Local Instance InactiveF : inactive_function _.
  refine {| inactive := fun config id _ => config id |}.
Proof using . repeat intro. now subst. Defined.

(* The support of a multiset, but elements are repeated 
 * a number of times equal to their multiplicity. 
 * This is needed to convert an observation from multiset to list format, 
 * so that we can use functions [colinear_dec] and [weber_calc]. *)
Definition multi_support {A} `{EqDec A} (s : multiset A) :=
  List.flat_map (fun '(x, mx) => alls x mx) (elements s).

Local Instance multi_support_compat {A} `{EqDec A} : Proper (equiv ==> PermutationA equiv) (@multi_support A _ _).
Proof using . 
intros s s' Hss'. unfold multi_support. f_equiv.
+ intros [x mx] [y my] Hxy. inv Hxy. simpl in H0, H1. now rewrite H0, H1.
+ now apply elements_compat.
Qed.


(* The main algorithm : just move towards the weber point
 * (in a straight line) until all robots are aligned. *)
Definition gatherW_pgm obs : path location := 
  if aligned_dec (multi_support obs) 
  (* Don't move (the robot's local frame is always centered on itself, i.e. its position is at the origin). *)
  then local_straight_path origin 
  (* Go towards the weber point. *)
  else local_straight_path (weber_calc (multi_support obs)).

Local Instance gatherW_pgm_compat : Proper (equiv ==> equiv) gatherW_pgm.
Proof using .
intros s1 s2 Hs. unfold gatherW_pgm.
repeat destruct_match.
+ reflexivity.
+ rewrite Hs in a. now intuition.
+ rewrite Hs in n0. now intuition.
+ f_equiv. apply weber_unique with (multi_support s1) ; auto.
  - rewrite Hs. now apply weber_calc_correct.
  - now apply weber_calc_correct.
Qed.

Definition gatherW : robogram := {| pgm := gatherW_pgm |}.


Lemma multi_support_add {A : Type} `{EqDec A} s x k : ~ In x s -> k > 0 ->
  PermutationA equiv (multi_support (add x k s)) (alls x k ++ multi_support s).
Proof using . 
intros Hin Hk. unfold multi_support. 
transitivity (flat_map (fun '(x0, mx) => alls x0 mx) ((x, k) :: elements s)).
+ f_equiv.
  - intros [a ka] [b kb] [H0 H1]. cbn in H0, H1. now rewrite H0, H1.
  - apply elements_add_out ; auto.
+ now cbn -[elements].
Qed.

Lemma multi_support_countA {A : Type} `{eq_dec : EqDec A} s x :
  countA_occ equiv eq_dec x (multi_support s) == s[x]. 
Proof using .
pattern s. apply MMultisetFacts.ind.
+ intros m m' Hm. f_equiv. 
  - apply countA_occ_compat ; autoclass. now rewrite Hm.
  - now rewrite Hm.
+ intros m x' n' Hin Hn IH. rewrite add_spec, multi_support_add, countA_occ_app by auto.
  destruct_match.
  - now rewrite <-e, countA_occ_alls_in, Nat.add_comm, IH ; autoclass.
  - now rewrite countA_occ_alls_out, IH, Nat.add_0_l ; auto.  
+ now reflexivity.
Qed.

(* This is the main result about multi_support. *)
Lemma multi_support_config config id : 
  PermutationA equiv 
    (multi_support (obs_from_config config (config id))) 
    (config_list config).
Proof using .
cbv -[multi_support config_list equiv make_multiset List.map]. rewrite List.map_id.
apply PermutationA_countA_occ. intros x. rewrite multi_support_countA. now apply make_multiset_spec.
Qed. 

Corollary multi_support_map f config id : 
  Proper (equiv ==> equiv) (projT1 f) ->
  PermutationA equiv 
    (multi_support (obs_from_config (map_config (lift f) config) (lift f (config id))))
    (List.map (projT1 f) (config_list config)).
Proof using .  
intros H. destruct f as [f Pf]. cbn -[equiv config_list multi_support]. 
change (f (config id)) with (map_config f config id).
now rewrite multi_support_config, config_list_map.
Qed.


Lemma lift_update_swap da config1 config2 g target :
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
Proof using .
cbn -[inverse dist equiv]. unfold id.
rewrite Similarity.dist_prop, Rmult_1_l.
destruct_match_eq Hle; destruct_match_eq Hle' ; try reflexivity ; [|];
rewrite Rle_bool_true_iff, Rle_bool_false_iff in *;
exfalso; revert_one not; intro Hgoal; apply Hgoal.
- assert (Hzoom := Similarity.zoom_pos (change_frame da config1 g)).
  eapply Rmult_le_reg_l; eauto; []. simpl.
  rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l; trivial; [].
  foldR2. lra.
- assert (Hzoom := Similarity.zoom_pos (change_frame da config1 g ⁻¹)).
  eapply Rmult_le_reg_l; eauto; []. simpl.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; trivial; [].
  foldR2. generalize (Similarity.zoom_pos (change_frame da config1 g)). lra.
Qed.

(* Simplify the [round] function and express it in the global frame of reference. *)
(* All the proofs below use this simplified version. *)
Lemma round_simplify da config : similarity_da_prop da -> 
  exists r : G -> ratio,
  round gatherW da config == 
  fun id => if activate da id then 
              if aligned_dec (config_list config) then config id 
              else 
                let trajectory := straight_path (config id) (weber_calc (config_list config)) in
                update config (unpack_good id) Similarity.id trajectory (r (unpack_good id))
            else config id.
Proof using . 
intros Hsim. eexists ?[r]. intros id. unfold round. 
destruct_match ; [|reflexivity].
destruct_match ; [|byz_exfalso].
cbn -[inverse equiv lift precondition frame_choice_bijection config_list origin update].
rewrite (lift_update_swap da config _ g). 
pose (f := existT precondition
  (change_frame da config g)
  (precondition_satisfied da config g)). 
pose (f_inv := existT (fun _ : location -> location => True)
  ((change_frame da config g) ⁻¹)
  (precondition_satisfied_inv da config g)).
pose (obs := obs_from_config (map_config (lift f) config) (lift f (config (Good g)))).
change_LHS (update 
  (map_config (lift f_inv) (map_config (lift f) config)) g Similarity.id
  (lift_path
    (frame_choice_bijection (change_frame da config g ⁻¹))
    (gatherW_pgm obs))
  (choose_update da
    (map_config (lift f) config) g (gatherW_pgm obs))).
assert (Proper (equiv ==> equiv) (projT1 f)) as f_compat.
{ unfold f ; cbn -[equiv]. intros x y Hxy ; now rewrite Hxy. }
assert (Halign_loc_glob : aligned (config_list config) <-> aligned (multi_support obs)).
{ unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[config_list]. apply aligned_similarity. }
destruct_match.
(* The robots are aligned. *)
+ unfold gatherW_pgm. destruct_match ; [|intuition].
  cbn -[equiv lift dist mul inverse]. unfold id.
  repeat rewrite mul_origin. destruct_match ; apply Hsim.
(* The robots aren't aligned. *)
+ unfold gatherW_pgm. destruct_match ; [intuition|].
  pose (sim := change_frame da config g). foldR2. fold sim.
  assert (Hweb : weber_calc (multi_support obs) == sim (weber_calc (config_list config))).
  {
    unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[equiv config_list].
    foldR2. fold sim. 
    apply weber_unique with (List.map sim (config_list config)).
    - now rewrite <-aligned_similarity.
    - apply weber_similarity, weber_calc_correct.
    - apply weber_calc_correct.
  }
  change location_Setoid with state_Setoid. apply update_compat ; auto.
  - intros r. cbn -[equiv]. rewrite Bijection.retraction_section. reflexivity.
  - intros r. rewrite Hweb. 
    pose (w := weber_calc (config_list config)). fold w. 
    pose (c := config (Good g)). fold c.
    cbn -[equiv w c opp RealVectorSpace.add mul inverse].
    rewrite sim_mul.  
    assert (Hcenter : (sim ⁻¹) 0%VS == c).
    { foldR2. change_LHS (center sim). apply Hsim. }
    assert (Hsim_cancel : forall x, (inverse sim) (sim x) == x).
    { cbn -[equiv]. now setoid_rewrite Bijection.retraction_section. }
    rewrite Hcenter, Hsim_cancel. simplifyR2. 
    rewrite 2 RealVectorSpace.add_assoc. f_equiv. now rewrite RealVectorSpace.add_comm.
  - rewrite Hweb. 
    instantiate (r := fun g => choose_update da (map_config ?[sim] config) g
      (local_straight_path (?[sim'] (weber_calc (config_list config))))).
    cbn -[equiv config_list]. reflexivity.
Qed.
  
(* This is the goal (for all demons and configs). *)
Definition eventually_aligned config (d : demon) (r : robogram) := 
  Stream.eventually 
    (Stream.forever (Stream.instant (fun c => aligned (config_list c)))) 
    (execute r d config).

(* If the robots are aligned, they stay aligned. *)
Lemma round_preserves_aligned da config : similarity_da_prop da ->
  aligned (config_list config) -> aligned (config_list (round gatherW da config)).
Proof using . 
intros Hsim Halign. assert (round gatherW da config == config) as H.
{ intros id. destruct (round_simplify config Hsim) as [r Hround].
  rewrite Hround. repeat destruct_match ; auto. }
now rewrite H.
Qed.

Lemma aligned_over config (d : demon) :
  Stream.forever (Stream.instant similarity_da_prop) d ->
  aligned (config_list config) -> 
  Stream.forever (Stream.instant (fun c => aligned (config_list c))) (execute gatherW d config).
Proof using .
revert config d. 
cofix Hind. intros config d Hsim Halign. constructor.
+ cbn -[config_list]. apply Halign.
+ cbn -[config_list]. simple apply Hind ; [apply Hsim |]. 
  apply round_preserves_aligned ; [apply Hsim | apply Halign].
Qed.


(* This would have been much more pleasant to do with mathcomp's tuples. *)
Lemma config_list_In_combine x x' c c' : 
  List.In (x, x') (combine (config_list c) (config_list c')) <-> 
  exists id, x == c id /\ x' == c' id.
Proof using lt_0n.
assert (g0 : G).
{ change G with (fin n). apply (exist _ 0). lia. }
split.
+ intros Hin. apply (@In_nth (location * location) _ _ (c (Good g0), c' (Good g0))) in Hin.
  destruct Hin as [i [Hi Hi']]. 
  rewrite combine_nth in Hi' by now repeat rewrite config_list_length. inv Hi'.
  assert (i < n) as Hin.
  { 
    eapply Nat.lt_le_trans ; [exact Hi|]. rewrite combine_length.
    repeat rewrite config_list_length. rewrite Nat.min_id. cbn. lia. 
  }
  pose (g := exist (fun x => x < n) i Hin).
  change (fin n) with G in *. exists (Good g) ;
  split ; rewrite config_list_spec, map_nth ; f_equiv ; unfold names ;
    rewrite app_nth1, map_nth by (now rewrite map_length, Gnames_length) ;
    f_equiv ; cbn ; change G with (fin n) ; apply nth_enum.  
+ intros [[g|b] [Hx Hx']]. 
  - assert ((x, x') = nth (proj1_sig g) (combine (config_list c) (config_list c')) (c (Good g0), c' (Good g0))) as H.
    { 
      rewrite combine_nth by now repeat rewrite config_list_length.
      destruct g as [g Hg].
      repeat rewrite config_list_spec, map_nth. rewrite Hx, Hx'. unfold names.
      repeat rewrite app_nth1, map_nth by now rewrite map_length, Gnames_length.
      repeat f_equal ; cbn ; change G with (fin n) ; erewrite nth_enum ; reflexivity.   
    }
    rewrite H. apply nth_In. rewrite combine_length. repeat rewrite config_list_length.
    rewrite Nat.min_id. cbn. destruct g. cbn. lia.
  - exfalso. assert (Hbyz := In_Bnames b). apply list_in_length_n0 in Hbyz. rewrite Bnames_length in Hbyz. auto.
Qed.

(* This measure counts how many robots aren't on the weber point. *)
Definition measure_count config : R := 
  let ps := config_list config in 
  (*INR (n - countA_occ equiv R2_EqDec (weber_calc ps) ps).*)
  list_sum (List.map (fun x => if x =?= weber_calc ps then 0%R else 1%R) ps).

(* This measure counts the total distance from the robots to the weber point. *)
Definition measure_dist config : R :=
  let ps := config_list config in 
  dist_sum ps (weber_calc ps).

(* This measure is positive, and decreases whenever a robot moves. *)
Definition measure config := (measure_count config + measure_dist config)%R.

Local Instance measure_compat : Proper (equiv ==> equiv) measure.
Proof using . 
intros c c' Hc. unfold measure, measure_count, measure_dist.
assert (Rplus_compat : Proper (equiv ==> equiv ==> equiv) Rplus).
{ intros x x' Hx y y' Hy. now rewrite Hx, Hy. } 
apply Rplus_compat.
+ apply list_sum_compat, eqlistA_PermutationA. f_equiv ; [| now rewrite Hc].
  intros ? ? H. repeat destruct_match ; rewrite H, Hc in * ; intuition.
+ now rewrite Hc.
Qed.

Lemma measure_nonneg config : (0 <= measure config)%R.
Proof using . 
unfold measure. apply Rplus_le_le_0_compat.
+ unfold measure_count. apply list_sum_ge_0. rewrite Forall_map, Forall_forall.
  intros x _. destruct_match ; lra.
+ unfold measure_dist. apply list_sum_ge_0. rewrite Forall_map, Forall_forall.
  intros x _. apply dist_nonneg.   
Qed.

(* All the magic is here : when the robots move 
 * they go towards the weber point so it is preserved. 
 * This still holds in an asynchronous setting.
 * The point calculated by weber_calc thus stays the same during an execution,
 * until the robots are colinear. *)
Lemma round_preserves_weber config da w :
  similarity_da_prop da -> Weber (config_list config) w -> 
    Weber (config_list (round gatherW da config)) w.
Proof using lt_0n. 
intros Hsim Hweb. apply weber_contract with (config_list config) ; auto.
unfold contract. rewrite Forall2_Forall, Forall_forall by now repeat rewrite config_list_length.
intros [x x']. rewrite config_list_In_combine.
intros [id [Hx Hx']]. destruct (round_simplify config Hsim) as [r Hround].
revert Hx'. rewrite Hround. 
repeat destruct_match ; intros Hx' ; rewrite Hx, Hx' ; try apply segment_end.
assert (w == weber_calc (config_list config)) as Hw.
{ apply weber_unique with (config_list config) ; auto. apply weber_calc_correct. }
cbn zeta. rewrite <-Hw. cbn -[dist straight_path]. unfold Datatypes.id.
pose (c := config id). fold c.
destruct_match ; rewrite segment_sym ; apply segment_straight_path.
Qed.

(* If the robots don't end up colinear, then the point calculated by weber_calc doesn't change. *)
Corollary round_preserves_weber_calc config da :
  similarity_da_prop da -> ~aligned (config_list (round gatherW da config)) -> 
  weber_calc (config_list (round gatherW da config)) == weber_calc (config_list config). 
Proof using lt_0n. 
intros Hsim HNalign.
apply weber_unique with (config_list (round gatherW da config)) ; auto.
+ apply round_preserves_weber ; [auto | apply weber_calc_correct].
+ apply weber_calc_correct.
Qed.

Lemma Forall2_le_count_weber config da : 
  similarity_da_prop da -> ~aligned (config_list (round gatherW da config)) ->
  Forall2 Rle
    (List.map
      (fun x : R2 => if x =?= weber_calc (config_list (round gatherW da config)) then 0%R else 1%R) 
      (config_list (round gatherW da config)))
    (List.map
      (fun x : R2 => if x =?= weber_calc (config_list config) then 0%R else 1%R)
      (config_list config)).
Proof using lt_0n. 
intros Hsim RNcol.  
assert (Hweb := round_preserves_weber_calc config Hsim RNcol).
rewrite Forall2_Forall, combine_map, Forall_map, Forall_forall by now repeat rewrite map_length, config_list_length.
intros [x' x] Hin. apply config_list_In_combine in Hin. destruct Hin as [id [Hx Hx']].
repeat destruct_match ; try lra. rewrite Hx, Hx', Hweb in *.
assert (H : round gatherW da config id == weber_calc (config_list config)).
{ 
  destruct (round_simplify config Hsim) as [r Hround].
  rewrite Hround. repeat destruct_match ; auto.
  cbn zeta. rewrite <-e. cbn -[equiv dist mul opp RealVectorSpace.add]. 
  simplifyR2. now destruct_match.
}
rewrite <-H in e. intuition.
Qed.

Lemma Forall2_le_dist_weber config da : 
  similarity_da_prop da -> ~aligned (config_list (round gatherW da config)) ->
  Forall2 Rle
    (List.map 
      (dist (weber_calc (config_list (round gatherW da config))))
      (config_list (round gatherW da config)))
    (List.map 
      (dist (weber_calc (config_list config))) 
      (config_list config)).
Proof using lt_0n. 
intros Hsim RNcol.
assert (Hweb := round_preserves_weber_calc config Hsim RNcol).
rewrite Forall2_Forall, combine_map, Forall_map, Forall_forall by now repeat rewrite map_length, config_list_length.
intros [x' x] Hin. apply config_list_In_combine in Hin. destruct Hin as [id [Hx' Hx]].
rewrite Hx, Hx', Hweb. destruct (round_simplify config Hsim) as [r Hround].
rewrite Hround. repeat destruct_match ; try lra.
cbn zeta. pose (w := weber_calc (config_list config)). fold w. rewrite <-Hx.
pose (ri := r (unpack_good id)). fold ri.
cbn -[dist RealVectorSpace.add mul opp w ri]. destruct_match.
+ repeat rewrite norm_dist. rewrite R2_opp_dist, RealVectorSpace.add_assoc.
  rewrite <-(mul_1 (w - x)) at 1. rewrite <-minus_morph, add_morph, norm_mul.
  rewrite <-Rmult_1_l. apply Rmult_le_compat_r ; try apply norm_nonneg.
  unfold Rabs. destruct_match ; generalize (ratio_bounds ri) ; lra.
+ rewrite mul_1, (RealVectorSpace.add_comm w), RealVectorSpace.add_assoc.
  simplifyR2. rewrite dist_same. apply dist_nonneg.
Qed.

(* If a robot moves, either the measure strictly decreases or the robots become colinear. *)
Lemma round_decreases_measure config da : 
  similarity_da_prop da ->
  moving gatherW da config <> nil -> 
    aligned (config_list (round gatherW da config)) \/ 
    (measure (round gatherW da config) <= measure config - Rmin delta 1)%R.
Proof using lt_0n. 
intros Hsim Hmove. 
destruct (aligned_dec (config_list (round gatherW da config))) as [Rcol | RNcol] ; [now left|right].
assert (Hweb := round_preserves_weber_calc config Hsim RNcol).
destruct (not_nil_In Hmove) as [i Hi]. apply moving_spec in Hi.
destruct (round gatherW da config i =?= weber_calc (config_list config)) as [Hreached | HNreached].
(* The robot that moved reached its destination. *)
+ transitivity (measure config - 1)%R ; [|generalize (Rmin_r delta 1%R) ; lra].
  unfold measure, Rminus. rewrite Rplus_assoc, (Rplus_comm _ (-1)%R), <-Rplus_assoc.
  apply Rplus_le_compat.
  - unfold measure_count. apply list_sum_le_eps ; [now apply Forall2_le_count_weber|].
    rewrite combine_map, Exists_map. apply Exists_exists. 
    exists (round gatherW da config i, config i).
    split ; [apply config_list_In_combine ; exists i ; intuition |].
    repeat destruct_match ; solve [lra | rewrite Hreached in * ; intuition]. 
  - unfold measure_dist. apply list_sum_le. now apply Forall2_le_dist_weber.
(* The robots that moved didn't reach its destination. *)
+ transitivity (measure config - delta)%R ; [|generalize (Rmin_l delta 1%R) ; lra].
  unfold measure, Rminus. rewrite Rplus_assoc. 
  apply Rplus_le_compat.
  - unfold measure_count. apply list_sum_le. now apply Forall2_le_count_weber.
  - unfold measure_dist. apply list_sum_le_eps ; [now apply Forall2_le_dist_weber|].
    rewrite combine_map, Exists_map. apply Exists_exists. 
    exists (round gatherW da config i, config i).
    split ; [apply config_list_In_combine ; exists i ; intuition |].
    rewrite Hweb. destruct (round_simplify config Hsim) as [r Hround].
    rewrite Hround. destruct_match_eq Hact ; [destruct_match_eq Halign|].
    * exfalso. now apply RNcol, round_preserves_aligned.
    * cbn zeta. 
      pose (w := weber_calc (config_list config)). foldR2. fold w. 
      pose (x := config i). fold x.
      pose (ri := r (unpack_good i)). fold ri.
      cbn -[dist RealVectorSpace.add mul opp w ri]. rewrite Rmult_1_l, mul_1.
      destruct_match_eq Hdelta ; unfold id in * ; rewrite good_unpack_good in * ; fold x in Hdelta.
      --rewrite Rle_bool_true_iff in Hdelta. repeat rewrite norm_dist in *.
        rewrite R2_opp_dist, RealVectorSpace.add_assoc in Hdelta |- *. 
        rewrite add_opp, add_origin_l, norm_opp, norm_mul, Rabs_pos_eq in Hdelta by (generalize (ratio_bounds ri) ; lra).
        rewrite <-(mul_1 (w - x)) at 1. rewrite <-minus_morph, add_morph, norm_mul.
        rewrite Rabs_pos_eq ; [|generalize (ratio_bounds ri) ; lra].
        rewrite Rmult_plus_distr_r, Rmult_1_l.
        simpl location in Hdelta |- *.
        apply Rplus_le_compat ; try lra.
        rewrite <-Ropp_mult_distr_l. now apply Ropp_le_contravar.
      --exfalso. apply HNreached. rewrite Hround. destruct_match ; [|intuition].
        cbn -[config_list dist mul opp RealVectorSpace.add].
        rewrite Rmult_1_l, good_unpack_good ; unfold id ; fold x ; fold ri ; foldR2 ; fold w.
        destruct_match ; intuition. 
        rewrite mul_1, (RealVectorSpace.add_comm w), RealVectorSpace.add_assoc. 
        now simplifyR2.
    * exfalso. apply Hi. rewrite Hround. destruct_match ; intuition.
Qed.

Lemma gathered_aligned ps x : 
  (Forall (fun y => y == x) ps) -> aligned ps.
Proof using . 
rewrite Forall_forall. intros Hgathered.
unfold aligned. rewrite ForallTriplets_forall.
intros a b c Ha Hb Hc.
apply Hgathered in Ha, Hb, Hc. rewrite Ha, Hb, Hc, add_opp.
apply colinear_origin_r.
Qed.

(* If the robots aren't aligned yet then there exists at least one robot which, 
 * if activated, will move. 
 * Any robot that isn't on the weber point will do the trick. *)
Lemma one_must_move config : ~aligned (config_list config) ->
  exists i, forall da, similarity_da_prop da -> activate da i = true ->
                       round gatherW da config i =/= config i.
Proof using delta_g0.
intros Nalign.
pose (w := weber_calc (config_list config)).
cut (exists i, config i =/= w). 
{
  intros [i Hi]. exists i. intros da Hsim Hact. 
  destruct (round_simplify config Hsim) as [r Hround]. rewrite Hround.
  repeat destruct_match ; try intuition. clear Hact.
  cbn -[opp mul RealVectorSpace.add dist config_list equiv complement].
  rewrite Rmult_1_l, mul_1, good_unpack_good ; unfold id ; fold w.
  destruct_match_eq Hdelta.
  + intros H. 
    rewrite <-(add_origin_r (config i)) in H at 3 ; apply add_reg_l in H.
    rewrite mul_eq0_iff in H. destruct H as [H1|H2].
    - rewrite H1, mul_0, add_origin_r, dist_same, Rle_bool_true_iff in Hdelta. lra.
    - rewrite R2sub_origin in H2. intuition.
  + rewrite (RealVectorSpace.add_comm w), RealVectorSpace.add_assoc.
    simplifyR2. intuition.
}
assert (List.Exists (fun x => x =/= weber_calc (config_list config)) (config_list config)) as HE.
{ 
  apply neg_Forall_Exists_neg ; [intros ; apply equiv_dec|].
  revert Nalign. apply contra. apply gathered_aligned.
}
rewrite Exists_exists in HE. destruct HE as [x [Hin Hx]].
apply (@In_InA R2 equiv _) in Hin. 
foldR2. change location_Setoid with state_Setoid in *. rewrite config_list_InA in Hin.
destruct Hin as [r Hr]. exists r. now rewrite <-Hr.
Qed.

(* Fairness entails progress. *)
Lemma fair_first_move (d : demon) config : 
  Fair d -> Stream.forever (Stream.instant similarity_da_prop) d ->
  ~(aligned (config_list config)) -> FirstMove gatherW d config.
Proof using delta_g0.
intros Hfair Hsim Nalign.
destruct (one_must_move config Nalign) as [id Hmove].
destruct Hfair as [locallyfair Hfair].
specialize (locallyfair id).
revert config Nalign Hmove.
induction locallyfair as [d Hnow | d] ; intros config Nalign Hmove.
* apply MoveNow. apply Hmove in Hnow.
  + rewrite <-(moving_spec gatherW (Stream.hd d) config id) in Hnow.
    intros Habs. now rewrite Habs in Hnow.   
  + apply Hsim.
* destruct (moving gatherW (Stream.hd d) config) as [| id' mov] eqn:Hmoving.
  + apply MoveLater ; trivial.
    apply IHlocallyfair.
    - apply Hfair.
    - apply Hsim.
    - apply no_moving_same_config in Hmoving. now rewrite Hmoving.
    - intros da Hda Hactive. apply no_moving_same_config in Hmoving.
      rewrite (Hmoving id).
      apply (round_compat (reflexivity gatherW) (reflexivity da)) in Hmoving. 
      rewrite (Hmoving id).
      now apply Hmove.
  + apply MoveNow. rewrite Hmoving. discriminate.
Qed.

(* This is the well founded relation we will perform induction on. *)
Definition lt_config eps c c' := 
  (0 <= measure c <= measure c' - eps)%R. 

Local Instance lt_config_compat : Proper (equiv ==> equiv ==> equiv ==> iff) lt_config.
Proof using . intros e e' He c1 c1' Hc1 c2 c2' Hc2. unfold lt_config. now rewrite He, Hc1, Hc2. Qed.

(* We proove this using the well-foundedness of lt on nat. *)
Lemma lt_config_wf eps : (eps > 0)%R -> well_founded (lt_config eps).
Proof using . 
intros Heps. unfold well_founded. intros c.
pose (f := fun x : R => Z.to_nat (up (x / eps))).
remember (f (measure c)) as k. generalize dependent c. 
pattern k. apply (well_founded_ind lt_wf). clear k.
intros k IH c Hk. apply Acc_intro. intros c' Hc'. apply IH with (f (measure c')) ; auto.
rewrite Hk ; unfold f ; unfold lt_config in Hc'.
rewrite <-Z2Nat.inj_lt.
+ apply Zup_lt. unfold Rdiv. rewrite <-(Rinv_r eps) by lra. 
  rewrite <-Rmult_minus_distr_r. apply Rmult_le_compat_r ; intuition.
+ apply up_le_0_compat, Rdiv_le_0_compat ; intuition. 
+ apply up_le_0_compat, Rdiv_le_0_compat ; intuition.
  transitivity eps ; intuition. 
  apply (Rplus_le_reg_r (- eps)). rewrite Rplus_opp_r. etransitivity ; eauto.
Qed.

(* The proof is essentially a well-founded induction on [measure config].
 * Fairness ensures that the measure must decrease at some point. *)
Theorem weber_correct config : forall d,
  Fair d -> Stream.forever (Stream.instant similarity_da_prop) d ->
  eventually_aligned config d gatherW.
Proof using delta_g0 lt_0n.
assert (Hdelta1 : (Rmin delta 1 > 0)%R).
{ unfold Rmin. destruct_match ; lra. }
induction config as [config IH] using (well_founded_ind (lt_config_wf Hdelta1)).
intros d Hfair Hsim.
destruct (aligned_dec (config_list config)) as [align | Nalign] ;
  [now apply Stream.Now, aligned_over|].
induction (fair_first_move config Hfair Hsim Nalign) as [d config Hmove | d config Hmove FM IH_FM] ;
  destruct Hsim as [Hsim_hd Hsim_tl] ; cbn in Hsim_hd ; apply Stream.Later.
+ destruct (round_decreases_measure config Hsim_hd Hmove) as [Ralign | Rmeasure].
  - now apply Stream.Now, aligned_over.
  - apply IH.
    * unfold lt_config. split ; [apply measure_nonneg | apply Rmeasure].  
    * apply Hfair. 
    * apply Hsim_tl. 
+ apply no_moving_same_config in Hmove. cbn -[config_list].
  apply IH_FM.
  - intros c' Hc' d' Hfair' Hsim'. rewrite Hmove in Hc'. apply IH ; auto.
  - apply Hfair.
  - apply Hsim_tl.
  - now rewrite Hmove.
Qed.  

End Alignment.
