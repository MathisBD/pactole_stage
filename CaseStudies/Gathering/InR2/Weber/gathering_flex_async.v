
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* Author : Mathis Bouverot-Dupuis (June 2022).

 * This file implements an algorithm to align all robots on an arbitrary 
 * axis, in the plane (R²). The algorithm assumes there are no byzantine robots,
 * and works in a FLEXIBLE and ASYNCHRONOUS setting. 

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
(* Specific to definition and properties of the weber point. *)
Require Import Pactole.CaseStudies.Gathering.InR2.Weber.Weber_point.

(* User defined *)
Import Permutation.
Import Datatypes.


Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.


(* Change the left hand side of a setoid-equality with a convertible term. *)
Ltac change_LHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (E == RHS)
  end.

(* Change the right hand side of a setoid-equality with a convertible term. *)
Ltac change_RHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (LHS == E)
  end.

(* Simplify a goal involving calculations in R2 by expanding everything. 
 * This is rarely useful. *)
Ltac simplifyR2 :=
  unfold Rminus ; 
  repeat (try rewrite mul_distr_add ;
          try rewrite <-add_morph ;
          try rewrite mul_0 ;
          try rewrite mul_1 ; 
          try rewrite add_origin_l ; 
          try rewrite add_origin_r ; 
          try rewrite mul_opp ; 
          try rewrite minus_morph ;
          try rewrite opp_opp ; 
          try rewrite opp_origin ;
          try rewrite R2_opp_dist ; 
          try rewrite add_opp).
      

Lemma contra (P Q : Prop) : (Q -> P) -> (~P -> ~Q).
Proof. intuition. Qed.


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
Proof. intros Hin. induction l as [|y l IH] ; cbn ; auto. Qed.

Lemma byz_impl_false : B -> False.
Proof. 
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
Proof. unfold unpack_good. destruct_match ; [auto | byz_exfalso]. Qed.

Lemma unpack_good_good g : unpack_good (Good g) = g.
Proof. reflexivity. Qed.  

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


(* This is what represents a robot's state.
 * The first location is the robot's start position (where it performed its last 'compute').
 * The second location is the robot's destination (what the robogram computed).
 * The ratio indicates how far the robot has moved along the straight path
 * from start to destination. *)
(* The robogram doesn't have access to all of this information : 
 * when we create an observation, this state gets reduced to 
 * only the current position of the robot. *)
(* I would have prefered to use a path instead of a (start, destination) pair,
 * but we need an EqDec instance on [info]. *)
Definition info := ((location * location) * ratio)%type.

Local Instance info_Setoid : Setoid info := 
  prod_Setoid (prod_Setoid location_Setoid location_Setoid) ratio_Setoid.
Local Instance info_EqDec : EqDec info_Setoid := 
  prod_EqDec (prod_EqDec location_EqDec location_EqDec) ratio_EqDec.

Lemma straight_path_similarity (f : similarity location) x y r :
  straight_path (f x) (f y) r == f (straight_path x y r).
Proof.
cbn -[mul opp RealVectorSpace.add]. 
rewrite sim_add, <-RealVectorSpace.add_assoc. f_equal.
rewrite sim_mul. unfold Rminus. rewrite <-add_morph, mul_1.
rewrite (RealVectorSpace.add_comm (f 0%VS) _), <-2 RealVectorSpace.add_assoc.
rewrite add_opp, add_origin_r. 
rewrite minus_morph, <-mul_opp, <-mul_distr_add. f_equal.
rewrite sim_add, sim_opp, <-2 RealVectorSpace.add_assoc. f_equal.
change 2%R with (1 + 1)%R. rewrite <-add_morph, mul_1. 
rewrite RealVectorSpace.add_comm, 2 RealVectorSpace.add_assoc. 
rewrite <-add_origin_l. f_equal.
rewrite <-(RealVectorSpace.add_assoc (- f 0)%VS _), (RealVectorSpace.add_comm (- f 0)%VS (f 0)%VS), add_opp.
rewrite add_origin_r, RealVectorSpace.add_comm, add_opp.
reflexivity.
Qed.

Local Instance St : State info.
Print State. 
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


(* We are in a flexible and semi-synchronous setting. *)
Local Instance UpdateF : update_function location (similarity location) unit.
simple refine {| update config g _ target _ :=  
  let '(start, dest, r) := config (Good g) in 
  (straight_path start dest r, target, ratio_0)
|} ; autoclass.
Proof using .
intros c c' Hc g g' Hg _ _ _ t t' Ht _ _ _.
assert (H : c (Good g) == c' (Good g')) by now rewrite Hg, Hc.
destruct (c (Good g)) as [[start dest] r].
destruct (c' (Good g')) as [[start' dest'] r'].
destruct H as [[Hstart Hdest] Hr]. cbn -[equiv] in Hstart, Hdest, Hr.  
now rewrite Hstart, Hdest, Hr, Ht. 
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
 * so that we can use functions [colinear_dec] and [weber_calc]. *)
Definition multi_support {A} `{EqDec A} (s : multiset A) :=
  List.flat_map (fun '(x, mx) => alls x mx) (elements s).

Local Instance flat_map_compat_eq {A B} `{Setoid A} `{Setoid B} : 
  Proper ((equiv ==> PermutationA equiv) ==> eqlistA equiv ==> PermutationA equiv) (@flat_map A B).
Proof using . 
intros f f' Hff' l l' Hll'. elim Hll'.
+ cbn. now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn. now f_equiv ; auto.
Qed.

Local Instance flat_map_compat_perm {A B} `{Setoid A} `{Setoid B} : 
  Proper ((equiv ==> PermutationA equiv) ==> PermutationA equiv ==> PermutationA equiv) (@flat_map A B).
Proof using . 
intros f f' Hff' l l' Hll'. elim Hll'.
+ simpl. now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn. rewrite <-IH. f_equiv. now apply Hff'.
+ intros x y t. cbn. repeat rewrite app_assoc. f_equiv.
 - rewrite PermutationA_app_comm. f_equiv ; now apply Hff'. now apply setoid_equiv.
 - now f_equiv.
+ intros t t' t'' _ IH1 _ IH2. rewrite IH1, <-IH2. f_equiv. 
  intros x x' Hxx'. symmetry. now apply Hff'.
Qed.

Local Instance multi_support_compat {A} `{EqDec A} : Proper (equiv ==> PermutationA equiv) (@multi_support A _ _).
Proof using . 
intros s s' Hss'. unfold multi_support. f_equiv.
+ intros [x mx] [y my] Hxy. inv Hxy. simpl in H0, H1. now rewrite H0, H1.
+ now apply elements_compat.
Qed.


(* The main algorithm : just move towards the weber point
 * (in a straight line) until all robots are aligned. *)
Definition gatherW_pgm obs : location := 
  if aligned_dec (multi_support obs) 
  (* Don't move (the robot's local frame is always centered on itself, i.e. its position is at the origin). *)
  then origin 
  (* Go towards the weber point. *)
  else weber_calc (multi_support obs).

Local Instance gatherW_pgm_compat : Proper (equiv ==> equiv) gatherW_pgm.
Proof using .
intros s1 s2 Hs. unfold gatherW_pgm.
repeat destruct_match.
+ reflexivity.
+ rewrite Hs in a. now intuition.
+ rewrite Hs in n0. now intuition.
+ apply weber_unique with (multi_support s1) ; auto.
  - now apply weber_calc_correct.
  - rewrite Hs. now apply weber_calc_correct.
Qed.

Definition gatherW : robogram := {| pgm := gatherW_pgm |}.

Local Instance countA_occ_compat_setoid {A : Type} `{eq_dec : EqDec A} : 
  Proper (equiv ==> PermutationA equiv ==> equiv) (countA_occ equiv eq_dec).
Proof using . intros x x' Hx l l' Hl. now apply countA_occ_compat ; autoclass. Qed.

Lemma countA_occ_removeA_same {A : Type} `{eq_dec : EqDec A} x l :
  countA_occ equiv eq_dec x (removeA eq_dec x l) = 0.
Proof. 
induction l as [|y l IH].
+ reflexivity.
+ cbn. destruct_match.
  - now rewrite IH.
  - cbn. destruct_match ; [intuition | now rewrite IH].
Qed.    

Lemma countA_occ_removeA_other {A : Type} `{eq_dec : EqDec A} x y l :
  x =/= y -> countA_occ equiv eq_dec x (removeA eq_dec y l) = countA_occ equiv eq_dec x l.
Proof.
intros Hxy. induction l as [|z l IH].
+ reflexivity.
+ cbn. repeat destruct_match.
  - rewrite <-e in e0. symmetry in e0. intuition.
  - now rewrite IH.
  - rewrite e. cbn. rewrite IH. destruct_match ; [|intuition]. reflexivity.
  - cbn. destruct_match ; [intuition|]. now rewrite IH.
Qed.    


Lemma PermutationA_countA_occ {A : Type} `{eq_dec : EqDec A} l l' :
  PermutationA equiv l l' <-> 
  forall x, countA_occ equiv eq_dec x l == countA_occ equiv eq_dec x l'.
Proof. 
split.
+ intros Hperm x. elim Hperm.
  - now reflexivity.
  - intros x1 x2 l1 l2 Hx Hl IH. cbn. 
    repeat destruct_match ; try (now rewrite IH) ; 
      rewrite <-e, Hx in c ; unfold complement in c ; now intuition.
  - intros a b t. cbn. repeat destruct_match ; reflexivity.
  - intros l1 l2 l3 _ H1 _ H2. now rewrite H1, <-H2.
+ intros Hcount. remember (length l) as m. generalize l l' Heqm Hcount.
  pattern m. apply (well_founded_ind lt_wf). clear m l l' Heqm Hcount.
  intros m IH [|x l] l' Hm Hcount.
  -  cbn in *. destruct l' as [|y tl'] ; [now apply permA_nil|].
    specialize (Hcount y). revert Hcount ; cbn. destruct_match ; [|intuition]. discriminate.
  - rewrite (PermutationA_count_split _ eq_dec x l).
    rewrite (PermutationA_count_split _ eq_dec x l').
    rewrite app_comm_cons. f_equiv.
    * apply eqlistA_PermutationA. rewrite <-Hcount. cbn. destruct_match ; [|intuition].
      cbn. reflexivity.
    * eapply IH ; [|reflexivity|].
      ++apply (Nat.le_lt_trans _ (length l)) ; [apply Preliminary.removeA_length_le|].
        rewrite Hm. cbn. lia.
      ++intros y. case (eq_dec x y) as [Hxy|Hxy]. 
        rewrite <-Hxy. repeat rewrite countA_occ_removeA_same. reflexivity.
        repeat rewrite countA_occ_removeA_other by (symmetry ; auto).
        rewrite <-Hcount. cbn. destruct_match ; [intuition|reflexivity].
Qed.

Lemma multi_support_add {A : Type} `{EqDec A} s x k : ~ In x s -> k > 0 ->
  PermutationA equiv (multi_support (add x k s)) (alls x k ++ multi_support s).
Proof. 
intros Hin Hk. unfold multi_support. 
transitivity (flat_map (fun '(x0, mx) => alls x0 mx) ((x, k) :: elements s)).
+ f_equiv.
  - intros [a ka] [b kb] [H0 H1]. cbn in H0, H1. now rewrite H0, H1.
  - apply elements_add_out ; auto.
+ now cbn -[elements].
Qed.

Lemma multi_support_countA {A : Type} `{eq_dec : EqDec A} s x :
  countA_occ equiv eq_dec x (multi_support s) == s[x]. 
Proof.
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
Proof. 
pose (l := pos_list config). fold l.
change (obs_from_config config (config id)) with (make_multiset l).
apply PermutationA_countA_occ. intros x. rewrite multi_support_countA. now apply make_multiset_spec.
Qed. 

Corollary multi_support_map f config id : 
  Proper (equiv ==> equiv) (projT1 f) ->
  PermutationA (@equiv location _) 
    (@multi_support location _ _ (obs_from_config (map_config (lift f) config) (lift f (config id))))
    (List.map (fun x => (projT1 f) (get_location x)) (config_list config)).
Proof.  
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

(* Simplify the [round] function and express it in the global frame of reference. *)
(* All the proofs below use this simplified version. *)
Lemma round_simplify da config : similarity_da_prop da ->
  exists r : ident -> ratio,
  round gatherW da config == 
  fun id => if activate da id then
              let target := 
                if aligned_dec (pos_list config) 
                then get_location (config id) 
                else weber_calc (pos_list config) 
              in (get_location (config id), target, ratio_0)
            else inactive config id (r id).
Proof. 
intros Hsim. eexists ?[r]. intros id. unfold round. 
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
assert (Halign_loc_glob : aligned (List.map get_location (config_list config)) <-> aligned (multi_support obs)).
{ unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[config_list get_location].
  now rewrite (aligned_similarity _ (change_frame da config g)), map_map. }
destruct_match.
(* The robots are aligned. *)
+ unfold gatherW_pgm. destruct_match ; [|intuition].
  change (frame_choice_bijection (change_frame da config g ⁻¹) 0%VS) with (center (change_frame da config g)).
  rewrite Hsim. cbn -[equiv inverse straight_path lift].
  destruct (config (Good g)) as [[start dest] r].
  reflexivity.
(* The robots aren't aligned. *)
+ unfold gatherW_pgm. destruct_match ; [intuition|].
  pose (sim := change_frame da config g). foldR2. fold sim.
  assert (Hweb : weber_calc (multi_support obs) == sim (weber_calc (List.map get_location (config_list config)))).
  {
    unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[equiv config_list get_location].
    foldR2. fold sim. 
    apply weber_unique with (List.map sim (List.map get_location (config_list config))).
    - now rewrite <-aligned_similarity.
    - rewrite map_map. apply weber_calc_correct.
    - apply weber_similarity, weber_calc_correct.
  }
  rewrite Hweb. cbn -[equiv config_list straight_path].
  destruct (config (Good g)) as [[start dest] r].
  rewrite Bijection.retraction_section. reflexivity.
Qed.

(* This is the goal (for all demons and configs). *)
Definition eventually_aligned config (d : demon) (r : robogram) := 
  Stream.eventually 
    (Stream.forever (Stream.instant (fun c => aligned (List.map get_location (config_list c))))) 
    (execute r d config).

(* This is the property : all robots stay where they are. 
 * This is what should be verified in the initial configuration. *)
Definition config_stay (config : configuration) : Prop := 
  forall id, let '(start, dest, _) := config id in dest == start.

Local Instance config_stay_compat : Proper (equiv ==> iff) config_stay.
Proof. 
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
Proof. 
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
Proof.
unfold config_stay, config_stay_or_go. intros Hstay p i. specialize (Hstay i). 
destruct (config i) as [[start dest] _]. now left.
Qed.

Lemma nth_enum i m d :
  forall Him : i < m, nth i (enum m) d = exist (fun x => x < m) i Him.
Proof.
intros Him. apply eq_proj1, Nat.le_antisymm ; cbn.
+ apply lt_n_Sm_le, firstn_enum_spec. rewrite <-(firstn_skipn (S i)) at 1.
  rewrite app_nth1 ; [apply nth_In|] ; rewrite firstn_length_le ; try rewrite enum_length ; lia. 
+ apply skipn_enum_spec. rewrite <-(firstn_skipn i) at 1.
  rewrite app_nth2 ; [apply nth_In|] ; rewrite firstn_length_le by (rewrite enum_length ; lia) ; auto.
  rewrite Nat.sub_diag, skipn_length, enum_length. lia.
Qed.

Lemma nth_InA {A : Type} {eqA : relation A} i l d :
  Reflexive eqA -> 
  i < length l -> InA eqA (nth i l d) l.
Proof.
intros Hrefl Hi. induction l using rev_ind. 
+ cbn in Hi. lia.
+ rewrite app_length in Hi. cbn in Hi.
  case (lt_dec i (length l)) as [Hi_lt | Hi_ge].
  - rewrite InA_app_iff ; left. Search nth app. 
    rewrite app_nth1 by auto. now apply IHl.
  - assert (Hi_eq : i = length l) by lia.
    rewrite Hi_eq, nth_middle, InA_app_iff ; right.
    now apply InA_cons_hd.
Qed. 

(* This would have been much more pleasant to do with mathcomp's tuples. *)
Lemma config_list_InA_combine x x' c c' : 
  InA equiv (x, x') (combine (config_list c) (config_list c')) <-> 
  exists id, x == c id /\ x' == c' id.
Proof.
assert (g0 : G).
{ change G with (fin n). apply (exist _ 0). lia. }
split.
+ intros Hin. Check In_nth. Search InA nth. 
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

Lemma combine_nil_or {A B : Type} (l : list A) (l' : list B) :
  combine l l' = nil <-> (l = nil \/ l' = nil).
Proof. 
split.
+ intros Hcom. destruct l as [|x l] ; destruct l' as [|x' l'] ; intuition.
  discriminate Hcom.
+ intros [-> | ->] ; [|rewrite combine_nil] ; reflexivity.
Qed.

Lemma Forall2_Forall {A B : Type} (R : A -> B -> Prop) l l' : length l = length l' -> 
  (Forall2 R l l' <-> Forall (fun '(x, y) => R x y) (combine l l')).
Proof. 
intros Hlen. split.
+ intros Hforall2. induction Hforall2 as [|x x' l l' Hx Hl IH] ; constructor ; auto.
+ intros Hforall. remember (combine l l') as c.
  generalize dependent l'. generalize dependent l. generalize dependent c.
  induction c as [|a c IH] ; intros Hforall l l' Hlen Hcom.
  - symmetry in Hcom. rewrite combine_nil_or in Hcom. 
    destruct Hcom as [-> | ->] ; cbn in Hlen ; [symmetry in Hlen|] ; 
      apply length_0 in Hlen ; rewrite Hlen ; constructor.
  - destruct a as [y y']. 
    destruct l as [|x l] ; [discriminate|]. 
    destruct l' as [|x' l'] ; [discriminate|].
    cbn in Hcom. inv Hcom. rewrite Forall_cons_iff in Hforall. constructor ; intuition.
Qed.

Lemma combine_map {A B C : Type} l l' (f : A -> C) (f' : B -> C) : 
  combine (List.map f l) (List.map f' l') = List.map (fun '(x, x') => (f x, f' x')) (combine l l').
Proof.
generalize l'. clear l'. induction l as [| x l IH] ; intros [|x' l'] ; cbn ; try reflexivity.
f_equal. apply IH.
Qed.

Lemma colinear_exists_mul u v : 
  ~ u == 0%VS -> colinear u v -> exists t, v == (t * u)%VS. 
Proof.
intros Hu_n0 Hcol. destruct (colinear_decompose Hu_n0 Hcol) as [Hdecomp | Hdecomp].
+ exists (norm v / norm u)%R. rewrite Hdecomp at 1. unfold Rdiv, unitary.
  now rewrite mul_morph.
+ exists ((- norm v) / norm u)%R. rewrite Hdecomp at 1. unfold Rdiv, unitary.
  now rewrite mul_morph.
Qed.   



(* A robot is moving from [s] to [d]. It is thus on the half line [L] 
 * originating at [d] and passing through [s]. If we move the robot a bit closer to [d],
 * it is still on [L]. *)
Lemma half_line_progress s d (r1 r2 : ratio) :
  half_line d (straight_path s d r1 - d) (straight_path s d (add_ratio r1 r2)).
Proof. 
unfold add_ratio. case (Rle_dec R1 (r1 + r2)) as [Hle | HNle].   
+ rewrite straight_path_1. apply half_line_origin. 
+ change R1 with 1%R in HNle. cbn -[mul opp RealVectorSpace.add]. 
  assert (H : (s + r1 * (d - s) - d == (1 - r1) * (s - d))%VS).
  { 
    rewrite (RealVectorSpace.add_comm s), <-RealVectorSpace.add_assoc, RealVectorSpace.add_comm.
    unfold Rminus. rewrite <-add_morph, mul_1. f_equiv.
    rewrite minus_morph, <-mul_opp. f_equiv. 
    now rewrite opp_distr_add, opp_opp, RealVectorSpace.add_comm. 
  }
  rewrite H ; clear H.
  rewrite <-half_line_mul_dir by (generalize (ratio_bounds r2) ; lra).
  unfold half_line. exists (1 - (r1 + r2))%R. split ; [lra|].
  unfold Rminus. rewrite <-(add_morph 1%R), mul_1, RealVectorSpace.add_assoc. f_equiv.
  - now rewrite (RealVectorSpace.add_comm s), RealVectorSpace.add_assoc, add_opp, add_origin_l.
  - rewrite minus_morph, <-mul_opp. f_equiv. 
    now rewrite opp_distr_add, opp_opp, RealVectorSpace.add_comm.
Qed. 
    

(* This is the main invariant : the robots are alway headed towards a weber point. *)
Lemma invariant_stg_weber config da w : similarity_da_prop da -> 
  let invariant c := config_stay_or_go c w /\ Weber (pos_list c) w in 
  invariant config -> invariant (round gatherW da config).
Proof. 
cbn zeta. intros Hsim [Hstg Hweb]. destruct (round_simplify config Hsim) as [r Hround].
split.
+ case (aligned_dec (pos_list config)) as [Halign | HNalign] ; cbn zeta in Hround.
  (* The robots are aligned. *)  
  - rewrite Hround. intros i. destruct_match ; [now left |].
    specialize (Hstg i). cbn -[equiv]. now destruct (config i) as [[s d] _].
  (* The robots aren't aligned. *)
  - rewrite Hround. intros i. destruct_match.
    * right. apply weber_unique with (pos_list config) ; auto.
      apply weber_calc_correct.
    * specialize (Hstg i). cbn -[equiv]. now destruct (config i) as [[s d] _].   
+ revert Hweb. apply weber_half_line. 
  rewrite Forall2_Forall, Forall_forall by (now unfold pos_list ; repeat rewrite map_length, config_list_length).
  intros [x x'] Hin. apply (@In_InA _ equiv) in Hin ; autoclass. foldR2.
  unfold pos_list in Hin. rewrite combine_map, (@InA_map_iff _ _ equiv equiv) in Hin ; autoclass.
  - destruct Hin as [[y y'] [Hxy Hin]]. apply config_list_InA_combine in Hin.
    destruct Hin as [i [Hi Hi']].
    destruct Hxy as [Hx Hx'] ; cbn -[equiv get_location] in Hx, Hx'. 
    rewrite <-Hx, <-Hx', Hi, Hi'. rewrite (Hround i).
    destruct_match.
    (* Activated robots don't move. *)
    * cbn zeta. cbn -[config_list RealVectorSpace.add opp mul]. rewrite mul_0, add_origin_r. 
      destruct (config i) as [[s d] ri]. apply half_line_segment.
    (* Inactive robots move along a straight line towards w. *)
    * cbn -[straight_path mul opp RealVectorSpace.add]. 
      specialize (Hstg i). destruct (config i) as [[s d] ri].
      case Hstg as [Hstay | Hgo].
      --rewrite Hstay. cbn -[mul opp RealVectorSpace.add]. 
        rewrite add_opp, 2 mul_origin, add_origin_r. apply half_line_segment.
      --rewrite Hgo. apply half_line_progress.
  - intros [a b] [a' b'] [Ha Hb]. cbn -[equiv] in Ha, Hb. split ; cbn -[equiv get_location].
    * now rewrite Ha.
    * now rewrite Hb.
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
Proof. 
intros c c' Hc. unfold measure, measure_count, measure_dist.
assert (Rplus_compat : Proper (equiv ==> equiv ==> equiv) Rplus).
{ intros x x' Hx y y' Hy. now rewrite Hx, Hy. } 
apply Rplus_compat.
+ apply list_sum_compat, eqlistA_PermutationA. f_equiv ; [| now rewrite Hc].
  intros ? ? H. repeat destruct_match ; rewrite H, Hc in * ; intuition.
+ now rewrite Hc.
Qed.


Lemma measure_nonneg config : (0 <= measure config)%R.
Proof. 
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
Proof. 
intros Hsim Hweb. apply weber_half_line with (config_list config) ; auto.
rewrite Forall2_Forall, Forall_forall by now repeat rewrite config_list_length.
intros [x x']. rewrite config_list_In_combine.
intros [id [Hx Hx']]. destruct (round_simplify config Hsim) as [r Hround].
revert Hx'. rewrite Hround. 
repeat destruct_match ; intros Hx' ; rewrite Hx, Hx' ; try apply half_line_segment.
assert (w == weber_calc (config_list config)) as Hw.
{ apply weber_unique with (config_list config) ; auto. apply weber_calc_correct. }
cbn zeta. rewrite <-Hw. cbn -[mul opp RealVectorSpace.add dist]. unfold Datatypes.id.
pose (c := config id). fold c.
destruct_match ; unfold half_line.
+ pose (ri := r (unpack_good id)). fold ri. 
  exists (1 - ri)%R ; split.
  - generalize (ratio_bounds ri). lra.
  - simplifyR2. 
    rewrite (RealVectorSpace.add_comm (ri * w) (- (ri * c))), 3 RealVectorSpace.add_assoc.
    f_equiv ; f_equiv.
    rewrite (RealVectorSpace.add_comm c (-w)), RealVectorSpace.add_assoc.
    now simplifyR2.
+ exists 0%R ; split.
  - lra.
  - simplifyR2. rewrite (RealVectorSpace.add_comm w (-c)), RealVectorSpace.add_assoc.
    now simplifyR2.  
Qed.

(* If the robots don't end up colinear, then the point calculated by weber_calc doesn't change. *)
Corollary round_preserves_weber_calc config da :
  similarity_da_prop da -> ~aligned (config_list (round gatherW da config)) -> 
  weber_calc (config_list (round gatherW da config)) == weber_calc (config_list config). 
Proof. 
intros Hsim HNalign.
apply weber_unique with (config_list (round gatherW da config)) ; auto.
+ apply weber_calc_correct.
+ apply round_preserves_weber ; [auto | apply weber_calc_correct].
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
Proof. 
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
Proof. 
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
Proof. 
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
Proof. 
rewrite Forall_forall. intros Hgathered.
unfold aligned. rewrite ForallTriplets_forall.
intros a b c Ha Hb Hc.
apply Hgathered in Ha, Hb, Hc. rewrite Ha, Hb, Hc, add_opp.
apply colinear_origin_r.
Qed.

Lemma mul_eq0_iff (k : R) (x : R2) : (k * x == 0)%VS <-> (k == 0)%R \/ (x == 0)%VS.
Proof.
split ; intros H.
+ case (k =?= 0%R) as [Hk | Hk] ; [now left | right].
  apply mul_reg_l with k ; [intuition|].
  rewrite mul_origin. exact H.
+ destruct H as [Hk | Hx].
  - now rewrite Hk, mul_0.
  - now rewrite Hx, mul_origin.
Qed.

(* If the robots aren't aligned yet then there exists at least one robot which, 
 * if activated, will move. 
 * Any robot that isn't on the weber point will do the trick. *)
Lemma one_must_move config : ~aligned (config_list config) ->
  exists i, forall da, similarity_da_prop da -> activate da i = true ->
                       round gatherW da config i =/= config i.
Proof.
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
Proof.
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
Proof. intros e e' He c1 c1' Hc1 c2 c2' Hc2. unfold lt_config. now rewrite He, Hc1, Hc2. Qed.

(* We proove this using the well-foundedness of lt on nat. *)
Lemma lt_config_wf eps : (eps > 0)%R -> well_founded (lt_config eps).
Proof. 
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
Proof.
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

End Gathering.