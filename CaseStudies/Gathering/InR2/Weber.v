
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
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

(* User defined *)
Import Permutation.
Import Datatypes.

Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.


Section Forall3.
Variables (A B C : Type).
Implicit Types (R : A -> B -> C -> Prop).

(* Note that this definition is NOT similar to Forall2 : here x y and z can be arbitrary elements,
 * they don't have to be at the same positions in their respective lists. *)
Definition Forall3 R l1 l2 l3 : Prop :=
  Forall (fun x => Forall (fun y => Forall (fun z => R x y z) l3) l2) l1.

Local Instance Forall_PermutationA_compat_strong {T : Type} `{Setoid T} : 
  Proper ((equiv ==> iff) ==> PermutationA equiv ==> iff) (@Forall T).
Proof using . 
intros P P' HP l l' Hl. elim Hl.
+ intuition.
+ intros x x' t t' Hx Ht IH. repeat rewrite Forall_cons_iff. now f_equiv ; [apply HP|].
+ intros x y t. repeat rewrite Forall_cons_iff. repeat rewrite <-and_assoc. f_equiv.
  - rewrite and_comm. now f_equiv ; auto.
  - f_equiv. intros ? ? ->. now apply HP.
+ intros t1 t2 t3 _ IH1 _ IH2. rewrite IH1, <-IH2.
  f_equiv. intros ? ? ->. symmetry. now apply HP.
Qed.

Local Instance Forall3_PermutationA_compat  `{Setoid A} `{Setoid B} `{Setoid C} : 
  Proper ((equiv ==> equiv ==> equiv ==> iff) ==> PermutationA equiv ==> PermutationA equiv ==> PermutationA equiv ==> iff) Forall3.
Proof. 
intros R R' HR l1 l1' Hl1 l2 l2' Hl2 l3 l3' Hl3. unfold Forall3.
repeat (f_equiv ; auto ; intros ? ? ?). now apply HR.
Qed.

(*unfold Forall3. f_equiv. 
+ intros [x [y z]] [x' [y' z']] Hxyz. apply HR ; inv Hxyz ; [|inv H1 ..] ; now intuition.
+ elim Hl.
  - cbn -[equiv]. now constructor.
  - intros x x' t t' Hx Ht IH. cbn -[equiv]. now f_equiv ; auto.
  - intros x y t. cbn -[equiv]. now apply permA_swap.
  - intros t1 t2 t3 _ IH1 _ IH2. now rewrite IH1, IH2.
Qed. *)

(*Definition sumbool_impl (P P' Q Q' : Prop) (f : P -> P') (g : Q -> Q') : 
    ({P} + {Q}) -> ({P'} + {Q'}) := fun t => 
  match t with 
  | left t1 => left (f t1)
  | right t2 => right (g t2) 
  end.*)

Lemma Forall3_dec R l1 l2 l3 : 
  (forall x y z, {R x y z} + {~ R x y z}) ->
  {Forall3 R l1 l2 l3} + {~ Forall3 R l1 l2 l3}.
Proof. intros Rdec. unfold Forall3. repeat (apply Forall_dec ; intros ?). now apply Rdec. Qed.

End Forall3.

Section WeberPoint.
Implicit Types (points : list R2).

Local Existing Instances R2_VS R2_ES Forall3_PermutationA_compat.

Definition det (v1 v2 : R2) := (fst v1 * snd v2 - snd v1 * fst v2)%R.

Local Instance det_compat : Proper (equiv ==> equiv ==> equiv) det. 
Proof using . intros x x' Hxx' y y' Hyy'. unfold det. now rewrite Hxx', Hyy'. Qed. 

(* A list of points in R2 are colinear. *)
Definition colinear points := 
  Forall3 (fun x y z => det (y - x) (z - x) == 0%R) points points points.

Local Instance colinear_compat : Proper (PermutationA equiv ==> equiv) colinear.
Proof using . intros p p' Hpp'. unfold colinear. now f_equiv. Qed.

Lemma colinear_dec points : {colinear points} + {~colinear points}.
Proof. unfold colinear. apply Forall3_dec. intros x y z. now apply equiv_dec. Qed. 

(* A Weber point of a finite collection P of points 
 * is a point that minimizes the sum of the distances to elements of P *)

(* Compute the sum of the element of a list [l] *)
Fixpoint list_sum l :=
  match l with 
  | nil => 0%R 
  | hd :: tl => (hd + list_sum tl)%R 
  end.

Local Instance list_sum_compat : 
  Proper (PermutationA (@equiv R _) ==> equiv) list_sum.
Proof.
intros l l' Hll'. elim Hll'.
+ now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn -[equiv]. now rewrite Hxx', IH.
+ intros x y t. cbn -[equiv].
  repeat rewrite <-Rplus_assoc. f_equiv. now rewrite Rplus_comm.
+ intros t t' t'' _ IH1 _ IH2. now rewrite IH1, IH2.
Qed.    

Definition dist_sum points (x : R2) := 
  list_sum (List.map (dist x) points).

Local Instance dist_sum_compat : Proper (PermutationA equiv ==> equiv ==> equiv) dist_sum.
Proof using .
intros p p' Hpp' x y Hxy. unfold dist_sum. f_equiv. now rewrite Hpp', Hxy.
Qed.

(* [argmin f P] is the set of elements that minimize [f] in the set [P],
 * when sets are represented by membership predicates. *)
Definition argmin {A : Type} (f : A -> R) (P : A -> Prop) : A -> Prop := 
  fun a => P a /\ forall b, P b -> (f a <= f b)%R.
  
Local Instance argmin_compat {A : Type} : Proper (equiv ==> equiv ==> @Logic.eq A ==> equiv) argmin.
Proof using . 
intros f g Hfg P P' HPP' a a' Haa'. unfold argmin.
rewrite <-Haa'. setoid_rewrite <-HPP'. setoid_rewrite <-Hfg.
reflexivity.
Qed.

(* The trivial predicate true everywhere. *)
Definition predT {A : Type} : A -> Prop := fun _ => True.

(* The set of Weber points of a finite collection of points *)
Definition Weber points : R2 -> Prop := argmin (dist_sum points) predT.

Local Instance weber_compat : Proper (PermutationA equiv ==> equiv ==> equiv) Weber.
Proof using .
  intros p p' Hpp' x y Hxy. unfold Weber. f_equiv ; try auto. intros z. now f_equiv.
Qed.

(* We can show that a weber point can equivalently be defined as
 * an argmin on a compact set of points (instead of an argmin on the whole plane),
 * and a continuous function always has a minimum on a compact set.*)
(* RMK : this is also true if [points] is empty. *)
Lemma weber_exists points : 
  exists x, Weber points x.
Proof. Admitted.

(* If the points aren't colinear, than the weber point is unique. *)
Lemma weber_unique points : ~colinear points -> 
  forall x y, Weber points x -> Weber points y -> x == y.
Proof. Admitted.

Lemma dist_sum_similarity (f : similarity R2) points x : 
  (dist_sum (List.map f points) (f x) == f.(zoom) * dist_sum points x)%R.
Proof. 
elim points.
+ cbn. now rewrite Rmult_0_r.
+ intros p ps IH. cbn -[dist]. 
  now rewrite dist_prop, IH, Rmult_plus_distr_l.
Qed.

Lemma weber_similarity_weak points w (f : similarity R2) : 
  Weber points w -> Weber (List.map f points) (f w).
Proof.
unfold Weber, argmin. intros [_ H]. split ; try now unfold predT.
intros b _. rewrite <-(Bijection.section_retraction f b). 
remember (Bijection.retraction f b) as b'.
repeat rewrite dist_sum_similarity. apply Rmult_le_compat_l.
+ now apply Rlt_le, zoom_pos.
+ now apply H.
Qed.


(* A weber point is preserved by similarities. *)
Lemma weber_similarity points w (f : similarity R2) : 
  Weber points w <-> Weber (List.map f points) (f w).
Proof.
split.
+ now apply weber_similarity_weak.
+ intros H. apply (@weber_similarity_weak _ _ (f ⁻¹)) in H.
  revert H. rewrite map_map.
  pose (f1f := fun x => (f ⁻¹) (f x)). 
  fold f1f. change ((f ⁻¹) (f w)) with (f1f w).
  assert (forall x, f1f x == x).
  { intros x. cbn -[equiv]. now rewrite Bijection.retraction_section. }
  apply weber_compat.
  - apply eqlistA_PermutationA. rewrite <-List.map_id at 1. f_equiv.
    intros x y Hxy. now rewrite H.
  - now rewrite H.
Qed.  

(* [half_line o d] represents the set of points that are in the the half line with 
 * origin [o] and direction [d], [o] included. 
 * If d == 0 then the set of points represented is reduced to [o]. *)
Definition half_line (o d : R2) : R2 -> Prop := fun x =>
  exists t : R, (x == o + t * d)%VS.

Local Instance half_line_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) half_line.
Proof using .
intros x x' Hxx' y y' Hyy' z z' Hzz'. unfold half_line. now rewrite Hxx', Hyy', Hzz'. 
Qed.

(* If we move each point towards/away from the weber point in a straight line
 * (without crossing the weber point), the weber point is preserved. *)
Lemma weber_half_line ps ps' w : 
  Forall2 (fun x y => half_line w (w - x) y) ps ps' -> Weber ps w -> Weber ps' w.
Proof. Admitted.

(* We assume the existence of a function that calculates a weber point of a collection
 * (even when the weber point is not unique).
 * This is a very strong assumption : such a function may not exist in closed form, 
 * and the Weber point can only be approximated. *)
Axiom weber_calc : list R2 -> R2.
Axiom weber_calc_correct : forall ps, Weber ps (weber_calc ps).

End WeberPoint.


Section Gathering.
Local Existing Instances colinear_compat weber_compat.

(* The number of robots *)
Variables n : nat.


Local Instance N : Names := Robots n 0.
Local Instance NoByz : NoByzantine.
Proof using . now split. Qed.

Local Instance Loc : Location := make_Location R2.
Local Instance LocVS : RealVectorSpace location := R2_VS.
Local Instance LocES : EuclideanSpace location := R2_ES.

(* We are in a rigid formalism *)

Local Instance St : State location := OnlyLocation (fun f => True).
Local Instance RobotC : robot_choice location := {| robot_choice_Setoid := location_Setoid |}.

Local Instance FrameC : frame_choice (similarity location) := FrameChoiceSimilarity.
Local Instance UpdateC : update_choice unit := NoChoice.
Local Instance InactiveC : inactive_choice unit := NoChoiceIna.

Local Instance UpdateF : update_function _ _ _.
  refine {| update := fun _ _ _ target _ => target |}.
Proof using . now repeat intro. Defined. 
Local Instance InactiveF : inactive_function _.
  refine {| inactive := fun config id _ => config id |}.
Proof using . repeat intro. now subst. Defined.
Local Instance Rigid : RigidSetting.
Proof using . split. reflexivity. Qed.


Definition multi_support {A} `{EqDec A} (s : multiset A) :=
  List.flat_map (fun '(x, mx) => alls x mx) (elements s).

Instance flat_map_compat_eq {A B} `{Setoid A} `{Setoid B} : 
  Proper ((equiv ==> PermutationA equiv) ==> eqlistA equiv ==> PermutationA equiv) (@flat_map A B).
Proof using . 
intros f f' Hff' l l' Hll'. elim Hll'.
+ cbn. now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn. now f_equiv ; auto.
Qed.

Instance flat_map_compat_perm {A B} `{Setoid A} `{Setoid B} : 
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

Definition gatherW_pgm obs : location := 
  if colinear_dec (multi_support obs) 
  (* don't move *)
  then origin 
  (* go towards the weber point *)
  else weber_calc (multi_support obs).

Local Instance gatherW_pgm_compat : Proper (equiv ==> equiv) gatherW_pgm.
Proof using .
intros s1 s2 Hs. unfold gatherW_pgm.
repeat destruct_match.
+ reflexivity.
+ rewrite Hs in c. now intuition.
+ rewrite Hs in n0. now intuition.
+ apply weber_unique with (multi_support s1) ; auto.
  - now apply weber_calc_correct.
  - rewrite Hs. now apply weber_calc_correct.
Qed.

Definition gatherW : robogram := {| pgm := gatherW_pgm |}.

(* Simplify the [round] function and express it in the glabal frame of reference. *)
Lemma round_simplify da config : similarity_da_prop da -> 
  round gatherW da config == 
  fun id => 
    if activate da id then 
      if colinear_dec (config_list config) then config id 
      else weber_calc (config_list config)
    else config id.
Proof. Admitted.  

(* This is the goal (for all demons and configs). *)
Definition eventually_colinear config (d : demon) (r : robogram) := 
  Stream.eventually 
    (Stream.forever (Stream.instant (fun c => colinear (config_list c)))) 
    (execute r d config).


(* If the robots are colinear, they stay colinear. *)
Lemma colinear_forever da config : similarity_da_prop da ->
  colinear (config_list config) -> colinear (config_list (round gatherW da config)).
Proof. Admitted.

Lemma colinear_over config (d : similarity_demon) :
  colinear (config_list config) -> eventually_colinear config d gatherW.
Proof. Admitted.

Lemma move_to_weber config da id : 
  

Theorem weber_correct : forall config (d : similarity_demon),
  Fair d -> eventually_colinear config d gatherW.
Proof. Check Fair. Admitted.

End Gathering.