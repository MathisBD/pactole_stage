
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* Author : Mathis Bouverot-Dupuis (June 2022).

 * This file implements an algorithm to GATHER all robots in the plane (R²). 
 * The algorithm assumes there are no byzantine robots,
 * and works in a FLEXIBLE and ASYNCHRONOUS setting. 

 * The algorithm is as follows : all robots go towards the 'weber point' of 
 * the configuration.
 * The algorithm works on initial configurations where the weber point is unique.
 * Thanks to a property of the weber point (see the thesis of Zohir Bouzid, 
 * corollary 3.1.1), it remains unique and at the same place throughout the whole execution. *)
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
Require Import Pactole.Spaces.RealMetricSpace.
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


Section Gathering.
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

(* - This is what represents a robot's state.
 * The first location is the robot's start position (where it performed its last 'compute').
 * The second location is the robot's destination (what the robogram computed).
 * The ratio indicates how far the robot has moved along the straight path
 * from start to destination.
 * - The robogram doesn't have access to all of this information : 
 * when we create an observation, this state gets reduced to 
 * only the current position of the robot.
 * - I would have prefered to use a path instead of a (start, destination) pair,
 * but we need an EqDec instance on [info]. *)
Definition info := ((location * location) * ratio)%type.

Local Instance info_Setoid : Setoid info := 
  prod_Setoid (prod_Setoid location_Setoid location_Setoid) ratio_Setoid.
Local Instance info_EqDec : EqDec info_Setoid := 
  prod_EqDec (prod_EqDec location_EqDec location_EqDec) ratio_EqDec.

Local Instance St : State info.
simple refine {|
  get_location := fun '(start, dest, r) => straight_path start dest r ; 
  state_Setoid := info_Setoid ;
  state_EqDec := info_EqDec ;
  precondition f := sigT (fun sim : similarity location => Bijection.section sim == f) ; 
  lift f := fun '(start, dest, r) => ((projT1 f) start, (projT1 f) dest, r) 
|} ; autoclass.
Proof using .
+ abstract (intros H [[start dest] r] ; reflexivity).
+ abstract (intros [f [sim Hf]] [[start dest] r] ; cbn -[equiv straight_path] ;
            rewrite <-Hf ; apply straight_path_similarity).
+ abstract (intros [[s d] r] [[s' d'] r'] [[Hs Hd] Hr] ; 
            cbn -[equiv location] in * |- ; now rewrite Hs, Hd, Hr).
+ abstract (intros [f Hf] [g Hg] ; cbn -[equiv] ; intros Hfg [[s d] r] [[s' d'] r'] [[Hs Hd] Hr] ;
            cbn -[equiv location] in * |- ; repeat split ; cbn -[equiv] ; auto).
Defined.

Definition get_start (i : info) := let '(s, _, _) := i in s.

Local Instance get_start_compat : Proper (equiv ==> equiv) get_start.
Proof using . intros [[? ?] ? ] [[? ?] ?] [[H _] _]. cbn -[equiv] in *. now rewrite H. Qed.

Definition get_destination (i : info) := let '(_, d, _) := i in d.

Local Instance get_destination_compat : Proper (equiv ==> equiv) get_destination.
Proof using . intros [[? ?] ? ] [[? ?] ?] [[_ H] _]. cbn -[equiv] in *. now rewrite H. Qed.

(* Refolding typeclass instances *)
Ltac foldR2 :=
  change R2 with location in * ;
  change R2_Setoid with location_Setoid in * ;
  change R2_EqDec with location_EqDec in * ;
  change R2_VS with LocVS in * ;
  change R2_ES with LocES in * ;
  change info_Setoid with state_Setoid in * ;
  change info_EqDec with state_EqDec in *.

(* Robots choose their destination.
 * They will move to this destination along a straight path. *)
Local Instance RobotC : robot_choice location := 
  { robot_choice_Setoid := location_Setoid }.

(* Robots view the other robots' positions up to a similarity. *)
Local Instance FrameC : frame_choice (similarity location) := FrameChoiceSimilarity.
(* The demon doesn't perform any other choice for activated robots. *)
Local Instance UpdateC : update_choice unit := NoChoice.
(* The demon chooses how far to move inactive robots towards their destination. 
 * The ratio chosen by the demon is ADDED to the ratio stored in the robot state
 * (the result is clamped at 1 of course). *)
Local Instance InactiveC : inactive_choice ratio := { inactive_choice_Setoid := ratio_Setoid }.

(* In a flexible setting, delta is the minimum distance that robots
 * are allowed to move before being reactivated. *)
Variables delta : R.
Hypothesis delta_g0 : (0 < delta)%R.

(* This is the property that must be verified in a flexible setting. *)
Definition flex_da_prop da := 
  forall id (config : configuration), activate da id = true -> 
    get_location (config id) == get_destination (config id) \/ 
    (delta <= dist (get_start (config id)) (get_location (config id)))%R.

(* We are in a flexible and semi-synchronous setting. *)
Local Instance UpdateF : update_function location (similarity location) unit.
simple refine {| 
  update config g _ target _ := (get_location (config (Good g)), target, ratio_0)
|} ; autoclass.
Proof using .
intros c c' Hc g g' Hg _ _ _ t t' Ht _ _ _.
assert (H : c (Good g) == c' (Good g')) by now rewrite Hg, Hc.
destruct (c (Good g)) as [[start dest] r].
destruct (c' (Good g')) as [[start' dest'] r'].
destruct H as [[Hstart Hdest] Hr]. cbn -[equiv] in Hstart, Hdest, Hr.
repeat split ; cbn -[equiv get_location] ; auto.
foldR2. apply get_location_compat. now repeat split ; cbn -[equiv].
Defined.


Local Instance InactiveF : inactive_function ratio.
simple refine {| inactive config id r_demon := 
  let '(start, dest, r) := config id in (start, dest, add_ratio r r_demon) 
|} ; autoclass.
Proof using . 
intros c c' Hc i i' Hi rd rd' Hrd.
assert (H : c i == c' i') by now rewrite Hi, Hc.
destruct (c i) as [[start dest] r].
destruct (c' i') as [[start' dest'] r'].
destruct H as [[Hstart Hdest] Hr]. cbn -[equiv] in Hstart, Hdest, Hr.
repeat split ; cbn -[equiv] ; auto.
f_equiv ; auto.
Defined.

(* This is a shorthand for the list of positions of robots in a configuration. *)
Definition pos_list (config : configuration) : list location := 
  List.map get_location (config_list config).

(* The support of a multiset, but elements are repeated 
 * a number of times equal to their multiplicity. 
 * This is needed to convert an observation from multiset to list format, 
 * so that we can use functions such as [weber_calc]. *)
Definition multi_support {A} `{EqDec A} (s : multiset A) :=
  List.flat_map (fun '(x, mx) => alls x mx) (elements s).

Local Instance multi_support_compat {A} `{EqDec A} : Proper (equiv ==> PermutationA equiv) (@multi_support A _ _).
Proof using . 
intros s s' Hss'. unfold multi_support. f_equiv.
+ intros [x mx] [y my] Hxy. inv Hxy. simpl in H0, H1. now rewrite H0, H1.
+ now apply elements_compat.
Qed.

(* The main algorithm : just move towards the weber point
 * (in a straight line) until all robots are gathered.
 * Note that [obs] describes the positions of the robots in the 
 * LOCAL frame of reference. *)
Definition gatherW_pgm obs : location := 
  weber_calc (multi_support obs).

Local Instance gatherW_pgm_compat : Proper (equiv ==> equiv) gatherW_pgm.
Proof using . intros ? ? H. unfold gatherW_pgm. now rewrite H. Qed. 

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
(* RMK : typeclass instance inference seems to be EXTREMELY slow in this proof.
 * Thankfully I found that the 'change' tactic is fast here. *)
Lemma multi_support_config (config : configuration) (id : ident) : 
  @PermutationA location equiv 
    (@multi_support location _ _ (obs_from_config config (config id))) 
    (pos_list config).
Proof using . 
pose (l := pos_list config). fold l.
change (obs_from_config config (config id)) with (make_multiset l).
apply PermutationA_countA_occ. intros x. rewrite multi_support_countA. now apply make_multiset_spec.
Qed. 

Corollary multi_support_map f config id : 
  Proper (equiv ==> equiv) (projT1 f) ->
  PermutationA (@equiv location _) 
    (@multi_support location _ _ (obs_from_config (map_config (lift f) config) (lift f (config id))))
    (List.map (fun x => (projT1 f) (get_location x)) (config_list config)).
Proof using .  
intros H. destruct f as [f Pf].
change (lift (existT precondition f Pf) (config id)) with (map_config (lift (existT precondition f Pf)) config id).
rewrite multi_support_config. unfold pos_list. rewrite config_list_map, map_map.
+ apply eqlistA_PermutationA. f_equiv. intros [[s d] r] [[s' d'] r'] Hsdr. inv Hsdr.
  cbn -[equiv straight_path]. destruct Pf as [sim Hsim]. rewrite <-Hsim. apply straight_path_similarity.
+ intros [[s d] r] [[s' d'] r'] [[Hs Hd] Hr]. cbn -[equiv] in H, Hs, Hd, Hr |- *. 
  repeat split ; cbn -[equiv] ; auto.
Qed.

Lemma lift_update_swap da config1 config2 g target :
  @equiv info _
    (lift (existT precondition (frame_choice_bijection (change_frame da config1 g ⁻¹))
                               (precondition_satisfied_inv da config1 g))
          (update config2
           g (change_frame da config1 g) target (choose_update da config2 g target)))
    (update (map_config (lift (existT precondition (frame_choice_bijection (change_frame da config1 g ⁻¹))
                                      (precondition_satisfied_inv da config1 g)))
                        config2)
            g Similarity.id
            ((frame_choice_bijection (change_frame da config1 g ⁻¹)) target)
            (choose_update da config2 g target)).
Proof using .
pose (sim := change_frame da config1 g). fold sim.
cbn -[inverse equiv straight_path]. destruct (config2 (Good g)) as [[start dest] r].
now rewrite straight_path_similarity.
Qed.

(* Simplify the [round] function and express it in the global frame of reference.
 * This simplification only works when the weber point is unique.
 * All the proofs below use this simplified version. *)
Lemma round_simplify da config w : 
  similarity_da_prop da ->
  OnlyWeber (pos_list config) w ->
  exists r : ident -> ratio,
  round gatherW da config == 
  fun id => if activate da id 
            then (get_location (config id), w, ratio_0)
            else inactive config id (r id).
Proof using . 
intros Hsim [Hw HwU]. eexists ?[r]. intros id. unfold round. 
destruct_match ; [|reflexivity].
destruct_match ; [|byz_exfalso].
cbn -[inverse equiv lift precondition frame_choice_bijection config_list origin update get_location].
rewrite (lift_update_swap da config _ g). 
pose (f := existT precondition
  (change_frame da config g)
  (precondition_satisfied da config g)). 
pose (f_inv := existT precondition
  ((change_frame da config g) ⁻¹)
  (precondition_satisfied_inv da config g)).
pose (obs := obs_from_config (map_config (lift f) config) (lift f (config (Good g)))).
change_LHS (update 
  (map_config (lift f_inv) (map_config (lift f) config)) g Similarity.id
  (frame_choice_bijection (change_frame da config g ⁻¹)
    (gatherW_pgm obs))
  (choose_update da
    (map_config (lift f) config) g (gatherW_pgm obs))).
assert (Hcancel : map_config (lift f_inv) (map_config (lift f) config) == config).
{ intros id. cbn -[equiv]. destruct (config id) as [[start dest] r]. now rewrite 2 Bijection.retraction_section. }
rewrite Hcancel.
assert (Proper (equiv ==> equiv) (projT1 f)) as f_compat.
{ unfold f ; cbn -[equiv]. intros x y Hxy ; now rewrite Hxy. }
unfold gatherW_pgm.
pose (sim := change_frame da config g). foldR2. fold sim.
assert (Hw_sim : OnlyWeber (List.map sim (pos_list config)) (sim w)).
{
  split ; [now apply weber_similarity|]. 
  intros w' Hw'. rewrite <-(Bijection.section_retraction sim w') in Hw' |- *. 
  f_equiv. apply HwU. now rewrite <-weber_similarity in Hw'.
}
assert (Hweb : weber_calc (multi_support obs) == sim w).
{
  unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[equiv config_list get_location].
  foldR2. fold sim. rewrite <-map_map. change (List.map get_location (config_list config)) with (pos_list config).
  apply Hw_sim, weber_calc_correct.
}
rewrite Hweb. cbn -[equiv config_list straight_path get_location].
rewrite Bijection.retraction_section. reflexivity.
Qed.

(* This is the property : all robots stay where they are. 
 * This is what should be verified in the initial configuration. *)
Definition config_stay (config : configuration) : Prop := 
  forall id, let '(start, dest, _) := config id in dest == start.

Local Instance config_stay_compat : Proper (equiv ==> iff) config_stay.
Proof using . 
intros c c' Hc. unfold config_stay. 
assert (H : forall id, c id == c' id) by (intros id ; now specialize (Hc id)).
split ; intros H1 id ; specialize (H1 id) ; specialize (H id) ;
  destruct (c id) as [[s d] r] ; destruct (c' id) as [[s' d'] r'] ;
  destruct H as [[Hs Hd] _] ; cbn -[equiv] in Hs, Hd.
+ now rewrite <-Hs, <-Hd.
+ now rewrite Hs, Hd.    
Qed.

(* This is the property : all robots stay where they are OR 
 * go towards point p. *)
Definition config_stay_or_go (config : configuration) p : Prop := 
  forall id, let '(start, dest, _) := config id in dest == start \/ dest == p.

Local Instance config_stay_or_go_compat : Proper (equiv ==> equiv ==> iff) config_stay_or_go.
Proof using . 
intros c c' Hc p p' Hp. unfold config_stay_or_go. 
assert (H : forall id, c id == c' id) by (intros id ; now specialize (Hc id)).
split ; intros H1 id ; specialize (H1 id) ; specialize (H id) ;
  destruct (c id) as [[s d] r] ; destruct (c' id) as [[s' d'] r'] ;
  destruct H as [[Hs Hd] _] ; cbn -[equiv] in Hs, Hd ; case H1 as [Hstay | Hgo].
+ left. now rewrite <-Hs, <-Hd.
+ right. now rewrite <-Hd, <-Hp.
+ left. now rewrite Hs, Hd.
+ right. now rewrite Hd, Hp.      
Qed.
  
Lemma config_stay_impl_config_stg config :
  config_stay config -> forall p, config_stay_or_go config p.
Proof using .
unfold config_stay, config_stay_or_go. intros Hstay p i. specialize (Hstay i). 
destruct (config i) as [[start dest] _]. now left.
Qed.

(* This would have been much more pleasant to do with mathcomp's tuples. *)
Lemma config_list_InA_combine x x' c c' : 
  InA equiv (x, x') (combine (config_list c) (config_list c')) <-> 
  exists id, x == c id /\ x' == c' id.
Proof using lt_0n.
assert (g0 : G).
{ change G with (fin n). apply (exist _ 0). lia. }
split.
+ intros Hin.
  apply (@InA_nth (info * info) equiv (c (Good g0), c' (Good g0))) in Hin.
  destruct Hin as [i [[y y'] [Hi [Hxy Hi']]]]. 
  rewrite combine_nth in Hi' by now repeat rewrite config_list_length. 
  inv Hi'. inv Hxy ; cbn -[equiv config_list] in * |-.
  setoid_rewrite H. setoid_rewrite H0.
  assert (i < n) as Hin.
  { 
    eapply Nat.lt_le_trans ; [exact Hi|]. rewrite combine_length.
    repeat rewrite config_list_length. rewrite Nat.min_id. cbn. lia. 
  }
  pose (g := exist (fun x => x < n) i Hin).
  change (fin n) with G in *. exists (Good g).
  split ; rewrite config_list_spec, map_nth ; f_equiv ; unfold names ;
    rewrite app_nth1, map_nth by (now rewrite map_length, Gnames_length) ;
    f_equiv ; cbn ; change G with (fin n) ; apply nth_enum.  
+ intros [[g|b] [Hx Hx']] ; [|byz_exfalso]. 
  assert (H : (x, x') == nth (proj1_sig g) (combine (config_list c) (config_list c')) (c (Good g0), c' (Good g0))).
  { 
    rewrite combine_nth by now repeat rewrite config_list_length.
    destruct g as [g Hg].
    repeat rewrite config_list_spec, map_nth. unfold names.
    repeat rewrite app_nth1, map_nth by now rewrite map_length, Gnames_length.
    split ; cbn -[equiv].
    * rewrite Hx. repeat f_equiv. change G with (fin n). erewrite nth_enum. reflexivity.
    * rewrite Hx'. repeat f_equiv. change G with (fin n). erewrite nth_enum. reflexivity.
  }
  rewrite H. apply nth_InA ; autoclass. rewrite combine_length. repeat rewrite config_list_length.
  rewrite Nat.min_id. cbn. destruct g. cbn. lia.
Qed.

Lemma pos_list_InA_combine x x' c c' : 
  InA equiv (x, x') (combine (pos_list c) (pos_list c')) <-> 
  exists id, x == get_location (c id) /\ x' == get_location (c' id).
Proof using lt_0n.
unfold pos_list. rewrite combine_map. rewrite (@InA_map_iff _ _ equiv equiv) ; autoclass.
+ split.
  - intros [[y y'] [[Hx Hx'] Hin]]. cbn -[equiv get_location] in Hx, Hx'.
    rewrite config_list_InA_combine in Hin. destruct Hin as [id [Hy Hy']].
    exists id. rewrite <-Hy, <-Hy', Hx, Hx'. auto.
  - intros [id [Hx Hx']].
    exists (c id, c' id). rewrite <-Hx, Hx'. split ; [auto|].
    rewrite config_list_InA_combine. exists id. auto.
+ intros [? ?] [? ?] [H1 H2]. cbn -[equiv] in H1, H2. split ; cbn -[equiv get_location].
  - now rewrite H1.
  - now rewrite H2.
Qed. 

Lemma pos_list_InA x c : 
  InA equiv x (pos_list c) <-> exists id, x == get_location (c id).
Proof using . 
unfold pos_list. rewrite (@InA_map_iff _ _ equiv equiv) ; autoclass.
+ split.
  - intros [y [Hx Hin]]. foldR2. rewrite config_list_InA in Hin.
    destruct Hin as [id Hy]. exists id. now rewrite <-Hx, <-Hy.   
  - intros [id Hx]. exists (c id). rewrite <-Hx. split ; [auto|].
    foldR2. rewrite config_list_InA. exists id. auto. 
+ foldR2. apply get_location_compat.
Qed. 

    
(* This is the main invariant : the robots are alway headed towards the unique weber point. *)
Definition invariant w config : Prop := 
  config_stay_or_go config w /\ OnlyWeber (pos_list config) w. 

Local Instance invariant_compat : Proper (equiv ==> equiv ==> iff) invariant.
Proof using . intros w w' Hw c c' Hc. unfold invariant. now rewrite Hc, Hw. Qed. 

(* A technical lemma used to prove the fact that the configuration always
 * contracts towards the weber point. *)
Lemma segment_progress a b r1 r2 : 
  segment b (straight_path a b r1) (straight_path a b (add_ratio r1 r2)).
Proof using .
assert (Hr1 := ratio_bounds r1).
assert (Hr2 := ratio_bounds r2).  
unfold add_ratio. case (Rle_dec R1 (r1 + r2)) as [Hle | HNle].
+ rewrite straight_path_1. apply segment_start.
+ change R1 with 1%R in HNle. cbn -[mul opp RealVectorSpace.add].
 unfold segment. exists (r2 / (1 - r1))%R. split.
 - split ; [apply Rdiv_le_0_compat | apply Rdiv_le_1] ; lra.
 - apply mul_reg_l with (1 - r1)%R ; [lra|].
   repeat rewrite (mul_distr_add (1 - r1)). repeat rewrite mul_morph.
   unfold Rdiv. rewrite <-Rmult_assoc, Rinv_r_simpl_m by lra.
   rewrite Rmult_minus_distr_l, Rmult_1_r, <-Rmult_assoc, Rinv_r_simpl_m by lra.
   assert (H : (a + r1 * (b - a) == r1 * b + (1 - r1) * a)%VS).
   { unfold Rminus. rewrite mul_distr_add, <-add_morph, mul_1, 2 RealVectorSpace.add_assoc.
     rewrite minus_morph, mul_opp. f_equiv. rewrite RealVectorSpace.add_comm. reflexivity. }
   rewrite H, (RealVectorSpace.add_comm ((1 - r1) * a)), 2 mul_distr_add.
   rewrite <-RealVectorSpace.add_assoc, (RealVectorSpace.add_assoc (r2 * b)). f_equiv.
   * rewrite mul_morph, add_morph. f_equiv. lra.
   * rewrite mul_opp, <-minus_morph, add_morph, mul_morph. f_equiv. lra. 
Qed.

(* The invariant is preserved. *)
Lemma round_preserves_invariant config da w : similarity_da_prop da -> 
  invariant w config -> invariant w (round gatherW da config).
Proof using lt_0n.
unfold invariant. intros Hsim [Hstg Hweb]. destruct (round_simplify config Hsim Hweb) as [r Hround].
split.
+ rewrite Hround. intros i. destruct_match ; [now right|].
  specialize (Hstg i). cbn -[equiv]. now destruct (config i) as [[s d] _].   
+ revert Hweb. apply weber_contract_unique. unfold contract. 
  rewrite Forall2_Forall, Forall_forall by (now unfold pos_list ; repeat rewrite map_length, config_list_length).
  intros [x x'] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
  rewrite pos_list_InA_combine in Hin. destruct Hin as [id [Hx Hx']].
  rewrite Hx, Hx', (Hround id).
  destruct_match.
  (* Activated robots don't move. *)
  * destruct (config id) as [[s d] ri]. cbn -[straight_path RealVectorSpace.add opp].
    rewrite straight_path_0. apply segment_end.
  (* Inactive robots move along a straight line towards w. *)
  * cbn -[straight_path mul opp RealVectorSpace.add]. 
    specialize (Hstg id). destruct (config id) as [[s d] ri].
    case Hstg as [Hstay | Hgo].
    --rewrite Hstay, 2 straight_path_same. apply segment_end.
    --rewrite Hgo. apply segment_progress.
Qed.

(* If the robots are gathered at the weber point, they don't move. *)
Lemma round_preserves_gathered config da w : 
  similarity_da_prop da -> invariant w config ->
  gathered_at w config -> gathered_at w (round gatherW da config).
Proof using .
intros Hsim [Hstg Hweb] Hgather g. destruct (round_simplify config Hsim Hweb) as [r Hround].
rewrite (Hround (Good g)). destruct_match.
+ rewrite Hgather. cbn -[equiv straight_path]. now rewrite straight_path_same.
+ cbn -[equiv straight_path]. specialize (Hstg (Good g)). specialize (Hgather g). 
  destruct (config (Good g)) as [[s d] rg]. cbn -[straight_path equiv] in Hgather.
  case Hstg as [Hstay | Hgo].
  - rewrite Hstay in *. now rewrite straight_path_same in *.
  - rewrite Hgo in *. rewrite straight_path_end in Hgather.
    case Hgather as [Hsw | Hrg].
    * now rewrite Hsw, straight_path_same.
    * unfold add_ratio. destruct_match.
      ++ now rewrite straight_path_1.
      ++exfalso. change R1 with 1%R in *. rewrite Hrg in *. 
        generalize (ratio_bounds (r (Good g))). lra.
Qed.
    
Lemma gathered_over config d w : 
  Stream.forever (Stream.instant similarity_da_prop) d -> 
  invariant w config -> 
  gathered_at w config -> 
  Gather w (execute gatherW d config).
Proof using lt_0n. 
revert config d.
cofix Hind. intros config d Hsim Hinv Hgather. constructor.
+ cbn. exact Hgather.
+ cbn. apply Hind.
  - apply Hsim.
  - now apply round_preserves_invariant ; [apply Hsim|].
  - now apply round_preserves_gathered ; [apply Hsim| |].
Qed.   

(* We say that a robot is looping when its start and destination points are equal. *)
Definition is_looping (robot : info) : bool := 
  if get_start robot =?= get_destination robot then true else false.

Local Instance is_looping_compat : Proper (equiv ==> eq) is_looping. 
Proof using . intros [[? ?] ?] [[? ?] ?] [[H1 H2] _]. cbn -[equiv] in *. now rewrite H1, H2. Qed.     

Lemma is_looping_ratio start dest r1 r2 : 
  is_looping (start, dest, r1) = is_looping (start, dest, r2).
Proof using . now unfold is_looping. Qed. 

(* Boolean function to test whether a robot is on a point. *)
Definition is_on x (robot : info) : bool :=
  if get_location robot =?= x then true else false.

Local Instance is_on_compat : Proper (equiv ==> equiv ==> eq) is_on.
Proof using . 
intros ? ? H1 ? ? H2. unfold is_on. 
repeat destruct_match ; rewrite H1, H2 in * ; intuition. 
Qed.

Definition BtoR : bool -> R := fun b => if b then 1%R else 0%R.

(* This measure counts how many robots are [not on the weber point] and [looping]. *)
Definition measure_loop_nonweb config : R :=
  let w := weber_calc (pos_list config) in
  list_sum (List.map 
    (fun r => BtoR (is_looping r && negb (is_on w r))) 
    (config_list config)).

(* This measure counts how many robots are not [looping on the weber point]. *)
Definition measure_loop_web config : R :=
  let w := weber_calc (pos_list config) in
  list_sum (List.map 
    (fun r => BtoR (negb (is_looping r && is_on w r)))
    (config_list config)).

(* This measure counts the total distance from the weber point to 
 * the last update position of each robot. 
 * RMK : this is NOT the distance from the weber point to the 
 * current position of each robot. *)
Definition measure_dist config : R := 
  dist_sum 
    (List.map get_start (config_list config)) 
    (weber_calc (pos_list config)).

(* The resulting measure is well-founded, and decreases whenever a robot is activated. *)
Definition measure config : R := 
  measure_loop_nonweb config + measure_loop_web config + measure_dist config.

Local Instance measure_compat : Proper (equiv ==> equiv) measure.
Proof using . 
intros c c' Hc. unfold measure.
f_equiv ; [f_equiv|].
+ unfold measure_loop_nonweb. apply list_sum_compat, eqlistA_PermutationA. 
  f_equiv ; [| now rewrite Hc].
  intros i i' Hi. now rewrite Hi, Hc.
+ unfold measure_loop_web. apply list_sum_compat, eqlistA_PermutationA. 
  f_equiv ; [| now rewrite Hc].
  intros i i' Hi. now rewrite Hi, Hc.
+ unfold measure_dist. f_equiv ; [|now rewrite Hc]. apply eqlistA_PermutationA. 
  apply map_eqlistA_compat with equiv ; autoclass.
  now rewrite Hc.
Qed.

(* The measure is trivially non-negative. *)
Lemma measure_nonneg config : (0 <= measure config)%R.
Proof using .
unfold measure. repeat apply Rplus_le_le_0_compat.
+ apply list_sum_ge_0. rewrite Forall_map, Forall_forall.
  intros x _. unfold BtoR. destruct_match ; lra.
+ apply list_sum_ge_0. rewrite Forall_map, Forall_forall.
  intros x _. unfold BtoR. destruct_match ; lra.
+ unfold measure_dist. apply list_sum_ge_0. rewrite Forall_map, Forall_forall.
  intros x _. apply dist_nonneg.   
Qed.

Section MeasureDecreaseLemmas.
Variables (config : configuration) (da : demonic_action) (w : location).
Hypothesis (Hsim : similarity_da_prop da).
Hypothesis (Hinv : invariant w config).

Lemma HRinv : invariant w (round gatherW da config).
Proof using Hinv Hsim lt_0n. now apply round_preserves_invariant. Qed. 

Lemma HRw : w == weber_calc (pos_list (round gatherW da config)).
Proof using Hinv Hsim lt_0n.
symmetry. apply HRinv, weber_calc_correct. 
Qed.

Lemma Hw : w == weber_calc (pos_list config).
Proof using Hinv Hsim. 
symmetry. apply Hinv, weber_calc_correct. 
Qed. 

Lemma BtoR_le b1 b2 : (b1 = true -> b2 = true) <-> (BtoR b1 <= BtoR b2)%R.
Proof using . unfold BtoR. repeat destruct_match ; lra. Qed.

Lemma BtoR_le_1 b1 b2 : (b1 = false /\ b2 = true) <-> (BtoR b1 <= BtoR b2 - 1)%R.
Proof using . unfold BtoR. repeat destruct_match ; lra. Qed.

Lemma weber_dist_decreases id :
  (dist w (get_start (round gatherW da config id)) <= dist w (get_start (config id)))%R.
Proof using Hinv Hsim. 
destruct Hinv as [Hstg Hweb].
destruct (round_simplify config Hsim Hweb) as [r Hround].
rewrite (Hround id). destruct_match. 
+ cbn -[dist straight_path]. specialize (Hstg id).
  destruct (config id) as [[s d] ri]. cbn [get_start].
  case Hstg as [Hstay | Hgo].
  - rewrite Hstay, straight_path_same. reflexivity.
  - rewrite Hgo. rewrite straight_path_dist_end, dist_sym. 
    rewrite <-Rmult_1_l. apply Rmult_le_compat_r ; [apply dist_nonneg|].
    generalize (ratio_bounds ri). lra.
+ cbn -[dist straight_path]. destruct (config id) as [[s d] ri]. cbn [get_start]. reflexivity.
Qed.

Lemma weber_dist_decreases_strong id :
  activate da id = true -> 
  get_destination (config id) == w ->
  get_location (config id) =/= w ->
  flex_da_prop da ->
  (dist w (get_start (round gatherW da config id)) <= dist w (get_start (config id)) - delta)%R.
Proof using Hinv Hsim.
intros Hact Hdest Hloc Hflex. specialize (Hflex id config Hact).
destruct Hinv as [Hstg Hweb].
destruct (round_simplify config Hsim Hweb) as [r Hround]. rewrite (Hround id). 
foldR2. change FrameChoiceSimilarity with FrameC in *. destruct_match_eq H ; [|intuition]. 
cbn -[dist straight_path]. specialize (Hstg id).
destruct (config id) as [[s d] ri]. cbn -[dist equiv straight_path] in Hdest, Hloc, Hflex |- *.
case Hstg as [Hstay | Hgo].
+ exfalso. rewrite Hstay, straight_path_same in *. intuition.
+ rewrite Hgo in *. case Hflex as [Hreached | Hdelta] ; [intuition|].
  transitivity (dist w s - dist s (straight_path s w ri))%R.
  - rewrite straight_path_dist_end, straight_path_dist_start, <-(Rmult_1_l (dist w s)), dist_sym.
    rewrite <-Rmult_minus_distr_r. reflexivity.
  - unfold Rminus. apply Rplus_le_compat_l, Ropp_le_contravar. exact Hdelta.
Qed.
  
Lemma measure_dist_decreases : 
  (measure_dist (round gatherW da config) <= measure_dist config)%R.
Proof using Hinv Hsim lt_0n. 
apply list_sum_le. rewrite Forall2_Forall by (now repeat rewrite map_length ; repeat rewrite config_list_length).
rewrite combine_map, Forall_map, Forall_forall.
intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
rewrite combine_map, (@InA_map_iff _ _ equiv equiv) in Hin ; autoclass.
+ destruct Hin as [[y' y] [[Hy' Hy] Hin]]. cbn -[equiv] in Hy, Hy'.
  rewrite config_list_InA_combine in Hin. destruct Hin as [id [Hx' Hx]].
  rewrite <-Hw, <-HRw, <-Hy, <-Hy', Hx, Hx'. apply weber_dist_decreases ; auto.
+ intros [? ?] [? ?] [H1 H2]. now rewrite H1, H2.
Qed.

Lemma contra_bool b1 b2 : (b2 = true -> b1 = true) -> (negb b1 = true -> negb b2 = true).
Proof using . case b1 ; case b2 ; intuition. Qed.

Lemma loop_web_decreases id : 
  (BtoR (negb (is_looping (round gatherW da config id) && is_on w (round gatherW da config id))) <=  
  BtoR (negb (is_looping (config id) && is_on w (config id))))%R.
Proof using Hinv Hsim. 
destruct Hinv as [Hstg Hweb]. specialize (Hstg id).
apply BtoR_le. apply contra_bool. rewrite 2 andb_true_iff. intros [Hloop Hon]. revert Hloop Hon.
destruct (round_simplify config Hsim Hweb) as [r Hround]. rewrite (Hround id).
destruct_match.
+ unfold is_looping, is_on. cbn -[straight_path equiv_dec].
  destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
  rewrite straight_path_0. intuition.
+ unfold is_looping, is_on. cbn -[straight_path equiv_dec]. 
  destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
  repeat (case ifP_sumbool ; try now intuition).
  intros H1 H2 Hsd. exfalso. revert H1 H2. rewrite Hsd, 2 straight_path_same.
  now intuition.
Qed.

Lemma loop_web_decreases_strong id :
  activate da id = true -> 
  get_location (config id) == w -> 
  get_start (config id) =/= w ->
  (BtoR (negb (is_looping (round gatherW da config id) && is_on w (round gatherW da config id))) <=  
  BtoR (negb (is_looping (config id) && is_on w (config id))) - 1)%R.
Proof using Hinv Hsim.
destruct Hinv as [Hstg Hweb]. specialize (Hstg id).
intros Hact Hloc Hstart. apply BtoR_le_1. 
rewrite negb_true_iff, negb_false_iff, andb_true_iff, andb_false_iff.
destruct (round_simplify config Hsim Hweb) as [r Hround]. rewrite (Hround id).
foldR2. change FrameChoiceSimilarity with FrameC.
revert Hact. case ifP_bool ; [intros Hact _ | discriminate].
revert Hloc Hstart. unfold is_looping, is_on. cbn -[straight_path equiv equiv_dec].
destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
case Hstg as [Hstay | Hgo].
+ rewrite Hstay. repeat rewrite straight_path_same. intuition.
+ rewrite Hgo. rewrite straight_path_0. intros -> Hsw.
  repeat (case ifP_sumbool ; try now intuition).
Qed.

Lemma measure_loop_web_decreases : 
  (measure_loop_web (round gatherW da config) <= measure_loop_web config)%R.
Proof using Hinv Hsim lt_0n. 
apply list_sum_le. rewrite Forall2_Forall by (now repeat rewrite map_length ; repeat rewrite config_list_length).
rewrite combine_map, Forall_map, Forall_forall.
intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
rewrite config_list_InA_combine in Hin. destruct Hin as [id [Hx' Hx]].
rewrite <-Hw, <-HRw, Hx, Hx'. apply loop_web_decreases ; auto.
Qed.

Lemma loop_nonweb_decreases id :
  (BtoR (is_looping (round gatherW da config id) && negb (is_on w (round gatherW da config id))) <=
  BtoR (is_looping (config id) && negb (is_on w (config id))))%R.
Proof using Hinv Hsim.
destruct Hinv as [Hstg Hweb]. specialize (Hstg id).
apply BtoR_le. rewrite 2 andb_true_iff, 2 negb_true_iff.
intros [Hloop Hon]. revert Hloop Hon.
destruct (round_simplify config Hsim Hweb) as [r Hround]. rewrite (Hround id).
destruct_match.
+ unfold is_looping, is_on. cbn -[straight_path equiv_dec].
  destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
  rewrite straight_path_0. intros ->. intuition.
+ unfold is_looping, is_on. cbn -[straight_path equiv_dec].
  destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
  case ifP_sumbool ; case ifP_sumbool ; try discriminate.
  intros H1 Hsd _ _. split ; [intuition|]. revert H1. rewrite Hsd, 2 straight_path_same.
  case ifP_sumbool ; intuition.
Qed.

Lemma loop_nonweb_decreases_strong id :
  activate da id = true -> 
  get_destination (config id) =/= w -> 
  (BtoR (is_looping (round gatherW da config id) && negb (is_on w (round gatherW da config id))) <=
  BtoR (is_looping (config id) && negb (is_on w (config id))) - 1)%R.
Proof using Hinv Hsim. 
destruct Hinv as [Hstg Hweb]. specialize (Hstg id).
intros Hact Hdest. apply BtoR_le_1. 
rewrite andb_true_iff, andb_false_iff, negb_false_iff, negb_true_iff.
destruct (round_simplify config Hsim Hweb) as [r Hround]. rewrite (Hround id).
foldR2. change FrameChoiceSimilarity with FrameC. 
revert Hact. case ifP_bool ; [|discriminate].
revert Hdest. unfold is_looping, is_on. cbn -[straight_path equiv equiv_dec].
destruct (config id) as [[s d] ri]. cbn [get_start get_destination].
rewrite straight_path_0. 
case Hstg as [Hstay | Hgo].
+ rewrite Hstay. repeat rewrite straight_path_same. repeat destruct_match ; intuition.
+ intuition.
Qed.

Lemma measure_loop_nonweb_decreases : 
  (measure_loop_nonweb (round gatherW da config) <= measure_loop_nonweb config)%R.
Proof using Hinv Hsim lt_0n. 
apply list_sum_le. rewrite Forall2_Forall by (now repeat rewrite map_length ; repeat rewrite config_list_length).
rewrite combine_map, Forall_map, Forall_forall.
intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
rewrite config_list_InA_combine in Hin. destruct Hin as [id [Hx' Hx]].
rewrite <-Hw, <-HRw, Hx, Hx'. apply loop_nonweb_decreases ; auto.
Qed.

End MeasureDecreaseLemmas.
    
Lemma In_InA_is_leibniz {A : Type} (eqA : relation A) x l : 
  (forall x y, eqA x y <-> x = y) -> (InA eqA x l <-> List.In x l).
Proof using . 
intros H. induction l as [|y l IH].
+ cbn. split ; [intros Hnil ; inv Hnil | intuition].
+ cbn. split.
  - intros HinA. rewrite InA_cons in HinA. destruct HinA as [Heq | HinA].
    * left. symmetry. now rewrite <-H.
    * right. now rewrite <-IH.
  - intros [Heq | Hin].
    * apply InA_cons_hd. now rewrite H.
    * apply InA_cons_tl. now rewrite IH.
Qed.

Lemma round_decrease_measure config da w :
  similarity_da_prop da ->
  invariant w config ->
    (measure (round gatherW da config) <= measure config)%R. 
Proof using lt_0n.
intros Hsim Hinv.
unfold measure. repeat apply Rplus_le_compat.
+ apply measure_loop_nonweb_decreases with w ; auto.
+ apply measure_loop_web_decreases with w ; auto.
+ apply measure_dist_decreases with w ; auto.
Qed. 
 
Lemma Rplus_le_compat3_1 x y z x' y' z' eps : 
  (x <= x' - eps)%R -> (y <= y')%R -> (z <= z')%R -> (x + y + z <= x' + y' + z' - eps)%R.
Proof using . lra. Qed.

Lemma Rplus_le_compat3_2 x y z x' y' z' eps : 
  (x <= x')%R -> (y <= y' - eps)%R -> (z <= z')%R -> (x + y + z <= x' + y' + z' - eps)%R.
Proof using . lra. Qed.

Lemma Rplus_le_compat3_3 x y z x' y' z' eps : 
  (x <= x')%R -> (y <= y')%R -> (z <= z' - eps)%R -> (x + y + z <= x' + y' + z' - eps)%R.
Proof using . lra. Qed. 


(* If a robot that is not [looping on the weber point] is activated, 
 * the measure strictly decreases. *)
Lemma round_decreases_measure_strong config da w : 
  similarity_da_prop da -> 
  flex_da_prop da ->
  invariant w config -> 
  (exists id, activate da id = true /\ is_looping (config id) && is_on w (config id) = false) -> 
    (measure (round gatherW da config) <= measure config - Rmin delta 1)%R.
Proof using lt_0n. 
intros Hsim Hflex Hinv [id [Hact Hnlw]].
assert (H := Hinv). destruct H as [Hstg Hweb]. specialize (Hstg id). 
assert (HRw : w == weber_calc (pos_list (round gatherW da config))).
{ symmetry. apply (round_preserves_invariant Hsim Hinv). apply weber_calc_correct. }
assert (Hw : w == weber_calc (pos_list config)).
{ symmetry. apply Hinv. apply weber_calc_correct. }
rewrite andb_false_iff in Hnlw. 
case (Sumbool.sumbool_of_bool (is_looping (config id))) as [Hloop | HNloop]. 
+ destruct Hnlw as [HNloop | HNon] ; [now rewrite Hloop in HNloop |].
  transitivity (measure config - 1)%R ; [|generalize (Rmin_r delta 1%R) ; lra].
  apply Rplus_le_compat3_1 ; [| eapply measure_loop_web_decreases ; eauto | eapply measure_dist_decreases ; eauto].
  apply list_sum_le_eps ; rewrite <-Hw, <-HRw.
  * rewrite Forall2_Forall, combine_map, Forall_map, Forall_forall 
      by now repeat rewrite map_length, config_list_length.
    intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
    rewrite config_list_InA_combine in Hin. destruct Hin as [id' [-> ->]].
    now apply loop_nonweb_decreases.
  * pose (f := fun r0 => BtoR (is_looping r0 && negb (is_on w r0))). fold f. 
    rewrite Exists_exists, combine_map.
    setoid_rewrite <-(@In_InA_is_leibniz _ equiv) ; autoclass.
    setoid_rewrite (@InA_map_iff _ _ equiv equiv) ; autoclass.
    ++eexists (?[x], ?[x']). 
      split. 
      --exists (round gatherW da config id, config id). split ; [reflexivity|].
        rewrite config_list_InA_combine. now exists id.
      --unfold f. apply loop_nonweb_decreases_strong ; auto.
        destruct (config id) as [[s d] ri]. revert HNon Hloop. unfold is_on, is_looping.
        case ifP_sumbool ; case ifP_sumbool ; try discriminate.
        cbn -[equiv straight_path]. intros ->. now rewrite straight_path_same.
    ++intros [? ?] [? ?] [H1 H2]. unfold f. rewrite H1, H2. reflexivity.
    ++intros [? ?] [? ?]. split ; auto.
+ unfold is_looping in HNloop. destruct (config id) as [[s d] r] eqn:Econfig. simpl in HNloop.
  case (s =?= d) as [Hsd | Hsd] ; [exfalso ; revert HNloop ; destruct_match ; intuition |].
  case Hstg as [Hstay | Hgo] ; [intuition|]. clear HNloop.
  case (get_location (config id) =?= w) as [HReached | HNreached].
  - transitivity (measure config - 1)%R ; [|generalize (Rmin_r delta 1%R) ; lra].
    apply Rplus_le_compat3_2 ; [eapply measure_loop_nonweb_decreases ; eauto | | eapply measure_dist_decreases ; eauto].
    apply list_sum_le_eps ; rewrite <-Hw, <-HRw.
    * rewrite Forall2_Forall, combine_map, Forall_map, Forall_forall 
        by now repeat rewrite map_length, config_list_length.
      intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
      rewrite config_list_InA_combine in Hin. destruct Hin as [id' [-> ->]].
      now apply loop_web_decreases.
    * pose (f := fun r0 => BtoR (negb (is_looping r0 && is_on w r0))). fold f. 
      rewrite Exists_exists, combine_map.
      setoid_rewrite <-(@In_InA_is_leibniz _ equiv) ; autoclass.
      setoid_rewrite (@InA_map_iff _ _ equiv equiv) ; autoclass.
      ++eexists (?[x], ?[x']). 
        split. 
        --exists (round gatherW da config id, config id). split ; [reflexivity|].
          rewrite config_list_InA_combine. now exists id.
        --unfold f. apply loop_web_decreases_strong ; auto. now rewrite Econfig, <-Hgo.
      ++intros [? ?] [? ?] [H1 H2]. unfold f. rewrite H1, H2. reflexivity.
      ++intros [? ?] [? ?] ; split ; auto.
  - transitivity (measure config - delta)%R ; [|generalize (Rmin_l delta 1%R) ; lra].
    apply Rplus_le_compat3_3 ; [eapply measure_loop_nonweb_decreases ; eauto | eapply measure_loop_web_decreases ; eauto |].
    apply list_sum_le_eps ; rewrite <-Hw, <-HRw.
    * rewrite Forall2_Forall, 2 map_map, combine_map, Forall_map, Forall_forall 
        by now repeat rewrite map_map, map_length, config_list_length.
      intros [x' x] Hin. apply (@In_InA _ equiv) in Hin ; autoclass.
      rewrite config_list_InA_combine in Hin. destruct Hin as [id' [-> ->]].
      now apply weber_dist_decreases.
    * rewrite 2 map_map, Exists_exists, combine_map.
      setoid_rewrite <-(@In_InA_is_leibniz _ equiv) ; autoclass.
      setoid_rewrite (@InA_map_iff _ _ equiv equiv) ; autoclass.
      ++eexists (?[x], ?[x']). 
        split. 
        --exists (round gatherW da config id, config id). split ; [reflexivity|].
          rewrite config_list_InA_combine. now exists id.
        --apply weber_dist_decreases_strong ; auto. now rewrite Econfig, <-Hgo.
      ++intros [? ?] [? ?] [H1 H2]. rewrite H1, H2. reflexivity.
      ++intros [? ?] [? ?] ; split ; auto.  
Qed.

(* This inductive proposition counts how many turns are left before
 * a robot that isn't [looping on w] is activated.
 * This is analoguous to FirstMove in the SSYNC case. *)
Inductive FirstActivNLW w : demon -> configuration -> Prop :=
  | FirstActivNLW_Now : forall d config id, 
    activate (Stream.hd d) id = true -> is_looping (config id) && is_on w (config id) = false -> 
      FirstActivNLW w d config
  | FirstActivNLW_Later : forall d config,
    FirstActivNLW w (Stream.tl d) (round gatherW (Stream.hd d) config) -> 
      FirstActivNLW w d config. 
    
(* If the robots aren't gathered yet, there exists a robot that isn't [looping on w]. *)
Lemma exists_non_webloop config w : 
  ~gathered_at w config ->
  invariant w config -> 
  exists id, is_looping (config id) && is_on w (config id) = false.
Proof using lt_0n. 
intros HNgather Hinv.
assert (H := Forall_dec (fun id => is_looping (config id) && is_on w (config id) = true)).
feed H ; [intros id ; case (is_looping (config id) && is_on w (config id)) ; intuition |].
case (H names) as [HT | HF] ; clear H.
+ exfalso. apply HNgather. unfold gathered_at. 
  rewrite Forall_forall in HT. intros g.
  specialize (HT (Good g)). feed HT ; [apply In_names |].
  rewrite andb_true_iff in HT. destruct HT as [_ Hon].
  revert Hon. unfold is_on. case ifP_sumbool ; try discriminate. auto. 
+ rewrite <-Exists_Forall_neg, Exists_exists in HF.
  - destruct HF as [id [_ Hnwl]]. apply not_true_is_false in Hnwl. 
    now exists id.
  - intros id. tauto.
Qed.

(* Fairness entails that if the robots aren't gathered yet, 
 * then a robot that isn't [looping on w] will eventually be activated. *)
Lemma non_webloop_will_activate config d w :
  Stream.forever (Stream.instant similarity_da_prop) d ->
  Fair d ->
  ~gathered_at w config ->    
  invariant w config -> 
  FirstActivNLW w d config.
Proof using lt_0n.
intros Hsim Hfair HNgather Hinv.
destruct (exists_non_webloop HNgather Hinv) as [id Hnwl].
destruct Hfair as [Hlocallyfair Hfair]. specialize (Hlocallyfair id).
clear HNgather. generalize dependent config.
induction Hlocallyfair as [d Hact | d HNact Hlater IH].
+ intros config Hinv Hnwl.
  apply FirstActivNLW_Now with id ; auto.
+ intros config Hinv Hnwl.
  apply FirstActivNLW_Later, IH.
  - apply Hsim.
  - apply Hfair.
  - apply round_preserves_invariant ; [apply Hsim | apply Hinv].
  - destruct Hsim as [Hsim_hd Hsim_tl]. 
    destruct Hinv as [Hstg Hweb].
    destruct (round_simplify config Hsim_hd Hweb) as [r Hround].
    rewrite (Hround id). destruct_match_eq Hact ; 
      [foldR2 ; rewrite Hact in HNact ; discriminate |].
    cbn. destruct (config id) as [[start dest] ri].
    rewrite andb_false_iff in Hnwl |- *.
    rewrite (is_looping_ratio _ _ _ ri).
    case Hnwl as [HNloop | HNon] ; [now left |].
    case (start =?= dest) as [Hloop | HNloop] ; [right | left].
    * revert HNon. cbn in Hloop. rewrite Hloop. unfold is_on. 
      cbn -[straight_path]. now rewrite 2 straight_path_same.
    * unfold is_looping. destruct_match ; intuition.
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


(* Notice that [invariant w config] is in the assumptions : 
 * see the next theorem for the final assumptions. 
 * The proof is essentially a well-founded induction on [measure config].
 * Fairness ensures that the measure must decrease at some point,
 * which leads to a second induction on [FirstMoveNLW w d config]. *)
Lemma weber_correct_aux w config d :
  Fair d -> 
  invariant w config ->
  Stream.forever (Stream.instant similarity_da_prop) d ->
  Stream.forever (Stream.instant flex_da_prop) d ->
  WillGather (execute gatherW d config).
Proof using lt_0n delta_g0.
assert (Hdelta1 : (Rmin delta 1 > 0)%R).
{ unfold Rmin. destruct_match ; lra. }
revert d.
induction config as [config IH] using (well_founded_ind (lt_config_wf Hdelta1)).
intros d Hfair Hinv Hsim Hflex.
case (gathered_at_dec config w) as [Hgather | HNgather].
{ apply Stream.Now. exists w. now apply gathered_over. }
induction (non_webloop_will_activate Hsim Hfair HNgather Hinv) as [d config id Hact Hnwl | d config Hnwl_later IHnwl].
+ apply Stream.Later. apply IH ; auto.
  - unfold lt_config. split ; [apply measure_nonneg|].
    apply round_decreases_measure_strong with w ; auto.
    * apply Hsim.
    * apply Hflex.
    * exists id. intuition.
  - apply Hfair.  
  - apply round_preserves_invariant ; [apply Hsim | auto].
  - apply Hsim.
  - apply Hflex.
+ apply Stream.Later. 
  case (gathered_at_dec (round gatherW (Stream.hd d) config) w) as [HRgather | HRNgather].
  - apply Stream.Now. exists w. apply gathered_over ; auto.
    * apply Hsim.
    * now apply round_preserves_invariant ; [apply Hsim|].
  - apply IHnwl ; auto.
    * intros c Hc. apply IH. unfold lt_config in Hc |- *.
      split ; [apply measure_nonneg|].
      etransitivity ; [apply Hc|].
      unfold Rminus. apply Rplus_le_compat_r.
      apply round_decrease_measure with w ; auto. apply Hsim.
    * apply Hfair.
    * apply round_preserves_invariant ; [apply Hsim | auto].
    * apply Hsim. 
    * apply Hflex.
Qed.

(* This is the main theorem. *)
Theorem weber_correct config d :
  Fair d -> 
  (* Initially, no robot is moving. *)
  config_stay config -> 
  (* Initially, the configuration has a unique weber point *)
  OnlyWeber (pos_list config) (weber_calc (pos_list config)) -> 
  (* The frame changes (chosen by the demon) are similarities centered on the observing robot. *)
  Stream.forever (Stream.instant similarity_da_prop) d ->
  (* We are in a flexible setting *)
  Stream.forever (Stream.instant flex_da_prop) d ->
  (* The robots will gather on the weber point (this is not explicit in this theorem). *)
  WillGather (execute gatherW d config).
Proof using lt_0n delta_g0.
intros Hfair Hstay Hsim Hflex. 
apply weber_correct_aux with (weber_calc (pos_list config)) ; auto.
now split ; [apply config_stay_impl_config_stg|]. 
Qed.

End Gathering.