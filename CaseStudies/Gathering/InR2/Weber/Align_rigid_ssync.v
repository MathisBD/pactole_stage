
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
 * and works in a RIGID and SEMI-SYNCHRONOUS setting.

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
(* Specific to rigidity *)
Require Import Pactole.Models.Rigid.
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


(* Robots don't have an state (and thus no memory) apart from their location. *)
Local Instance St : State location := OnlyLocation (fun f => True).
Local Instance RobotC : robot_choice location := {| robot_choice_Setoid := location_Setoid |}.

(* Robots view the other robots' positions up to a similarity. *)
Local Instance FrameC : frame_choice (similarity location) := FrameChoiceSimilarity.
Local Instance UpdateC : update_choice unit := NoChoice.
Local Instance InactiveC : inactive_choice unit := NoChoiceIna.

(* We are in a rigid and semi-synchronous setting. *)
Local Instance UpdateF : update_function _ _ _.
  refine {| update := fun _ _ _ target _ => target |}.
Proof using . now repeat intro. Defined. 
Local Instance InactiveF : inactive_function _.
  refine {| inactive := fun config id _ => config id |}.
Proof using . repeat intro. now subst. Defined.
Local Instance Rigid : RigidSetting.
Proof using . split. reflexivity. Qed.

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


(* The main algorithm : just move towards the weber point until all robots are aligned. *)
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

(* Simplify the [round] function and express it in the global frame of reference. *)
(* All the proofs below use this simplified version. *)
Lemma round_simplify da config : similarity_da_prop da -> 
  round gatherW da config == 
  fun id => 
    if activate da id then 
      if aligned_dec (config_list config) then config id 
      else weber_calc (config_list config)
    else config id.
Proof using . 
intros Hsim. apply no_byz_eq. intros g. unfold round. 
cbn -[inverse equiv lift location config_list origin].
destruct_match ; try reflexivity.
pose (f := existT (fun _ : location -> location => True)
  (frame_choice_bijection (change_frame da config g))
  (precondition_satisfied da config g)).
pose (f_inv := existT (fun _ : location -> location => True)
  (frame_choice_bijection (change_frame da config g) ⁻¹)
  (precondition_satisfied_inv da config g)).
change_LHS (lift f_inv (gatherW_pgm (obs_from_config 
  (map_config (lift f) config) 
  ((lift f) (config (Good g)))
))).
assert (Proper (equiv ==> equiv) (projT1 f)) as f_compat.
{ unfold f ; cbn -[equiv]. intros x y Hxy ; now rewrite Hxy. }
unfold gatherW_pgm ; destruct_match.
+ rewrite multi_support_map in a by auto.
  cbn -[equiv inverse config_list location] in *. 
  rewrite <-aligned_similarity in a. change_LHS (center (change_frame da config g)).
  rewrite Hsim ; cbn -[equiv config_list] ; unfold id.
  now destruct_match ; intuition.
+ rewrite multi_support_map in * by auto.
  cbn -[equiv inverse config_list location multi_support] in *.
  pose (sim := change_frame da config g) ; fold sim in n0 ; fold sim.
  rewrite <-aligned_similarity in n0. destruct_match ; intuition.
  apply weber_unique with (config_list config) ; auto ; [now apply weber_calc_correct|].
  apply weber_similarity with sim. cbn -[config_list]. rewrite Bijection.section_retraction.
  now apply weber_calc_correct.
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
{ intros id. rewrite round_simplify by auto. repeat destruct_match ; auto. }
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

Lemma sub_lt_sub (i j k : nat) : j < i <= k -> k - i < k - j.
Proof using lt_0n. lia. Qed.

Lemma list_in_length_n0 {A : Type} x (l : list A) : List.In x l -> length l <> 0.
Proof using . intros Hin. induction l as [|y l IH] ; cbn ; auto. Qed.

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

(* This measure strictly decreases whenever a robot moves. *)
Definition measure config := 
  let ps := config_list config in 
  n - countA_occ equiv R2_EqDec (weber_calc ps) ps.

Local Instance measure_compat : Proper (equiv ==> eq) measure.
Proof using . intros c c' Hc. unfold measure. now rewrite Hc. Qed.

(* All the magic is here : when the robots move 
 * they go towards the weber point so it is preserved. 
 * This still holds in a flexible and/or asynchronous setting.
 * The point calculated by weber_calc thus stays the same during an execution,
 * until the robots are colinear. *)
Lemma round_preserves_weber config da w :
  similarity_da_prop da -> Weber (config_list config) w -> 
    Weber (config_list (round gatherW da config)) w.
Proof using lt_0n. 
intros Hsim Hweb. apply weber_contract with (config_list config) ; auto.
unfold contract. rewrite Forall2_Forall, Forall_forall by now repeat rewrite config_list_length.
intros [x x']. rewrite config_list_In_combine.
intros [id [Hx Hx']]. revert Hx'. rewrite round_simplify by auto. 
repeat destruct_match ; intros Hx' ; rewrite Hx, Hx' ; try apply segment_end.
assert (w == weber_calc (config_list config)) as Hw.
{ apply weber_unique with (config_list config) ; auto. now apply weber_calc_correct. }
rewrite <-Hw. apply segment_start.
Qed.

(* If a robot moves, either the measure decreases or the robots become colinear. *)
Lemma round_decreases_measure config da : 
  similarity_da_prop da ->
  moving gatherW da config <> nil -> 
    aligned (config_list (round gatherW da config)) \/ 
    measure (round gatherW da config) < measure config.
Proof using lt_0n. 
intros Hsim Hmove. 
destruct (aligned_dec (config_list (round gatherW da config))) as [Rcol | RNcol] ; [now left|right].
assert (weber_calc (config_list (round gatherW da config)) == weber_calc (config_list config)) as Hweb.
{ 
  apply weber_unique with (config_list (round gatherW da config)) ; auto.
  + apply round_preserves_weber ; [auto | apply weber_calc_correct].
  + apply weber_calc_correct.  
}
unfold measure. apply sub_lt_sub. split.
+ destruct (not_nil_In Hmove) as [i Hi]. apply moving_spec in Hi.
  rewrite Hweb. apply countA_occ_lt.
  - rewrite Forall2_Forall, Forall_forall. intros [x x'] Hin.
    apply config_list_In_combine in Hin. destruct Hin as [j [-> ->]].
    rewrite round_simplify by auto. repeat destruct_match ; intuition.
    repeat rewrite config_list_length. reflexivity.
  - apply Exists_exists. exists (config i, round gatherW da config i).
    split ; [| now auto].
    apply config_list_In_combine. exists i ; intuition.
+ etransitivity ; [apply countA_occ_length_le|].
  rewrite config_list_length. cbn ; lia.
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
  exists r, forall da, similarity_da_prop da -> activate da r = true ->
                       round gatherW da config r =/= config r.
Proof using .
intros Nalign.
cut (exists r, config r =/= weber_calc (config_list config)). 
{
  intros [r Hr]. exists r. intros da Hsim Hact. rewrite round_simplify by auto.
  repeat destruct_match ; intuition.
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
Proof using .
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

(* The proof is essentially a well-founded induction on [measure config].
 * Fairness ensures that the measure must decrease at some point. *)
Theorem weber_correct (d : demon) config : 
  Fair d -> 
  Stream.forever (Stream.instant similarity_da_prop) d ->
  eventually_aligned config d gatherW.
Proof using lt_0n.
remember (measure config) as k. 
generalize dependent d. generalize dependent config.
pattern k. apply (well_founded_ind lt_wf). clear k.
intros k IHk config Hk d Hfair Hsim.
destruct (aligned_dec (config_list config)) as [align | Nalign] ;
  [now apply Stream.Now, aligned_over|].
induction (fair_first_move config Hfair Hsim Nalign) as [d config Hmove | d config Hmove FM IH_FM] ;
  destruct Hsim as [Hsim_hd Hsim_tl] ; cbn in Hsim_hd ; apply Stream.Later.
+ destruct (round_decreases_measure config Hsim_hd Hmove) as [Ralign | Rmeasure].
  - now apply Stream.Now, aligned_over.
  - eapply IHk. 
    * rewrite Hk. exact Rmeasure.  
    * reflexivity.
    * destruct Hfair as [_ Hfair_tl]. exact Hfair_tl.
    * exact Hsim_tl.
+ apply no_moving_same_config in Hmove.
  apply IH_FM ; (try rewrite Hmove) ; auto.
  destruct Hfair as [_ Hfair_tl]. exact Hfair_tl.
Qed.

End Alignment.
