
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* This file implements an algorithm to align all robots on an arbitrary 
 * axis, in the plane (R²). The algorithm assumes there are no byzantine robots,
 * and should work in a flexible and asynchronous setting 
 * (the proof maybe hasn't got that far yet). 

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

(* User defined *)
Import Permutation.
Import Datatypes.

Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.


(* Change the left hand side of an setoid-equality with a convertible term. *)
Ltac change_LHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (E == RHS)
  end.

(* Change the right hand side of an setoid-equality with a convertible term. *)
Ltac change_RHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (LHS == E)
  end.

(* Simplify a goal involving calculations in R2 by developing everything. *)
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


Section ForallTriplets.
Variables (A B C : Type).
Implicit Types (R : A -> B -> C -> Prop).

(* The proposition R holds for every triplet in the cartesian product (l1 * l2 * l3). *)
Definition ForallTriplets R l1 l2 l3 : Prop :=
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

Local Instance ForallTriplets_PermutationA_compat  `{Setoid A} `{Setoid B} `{Setoid C} : 
  Proper ((equiv ==> equiv ==> equiv ==> iff) ==> 
    PermutationA equiv ==> PermutationA equiv ==> PermutationA equiv ==> iff) ForallTriplets.
Proof. 
intros R R' HR l1 l1' Hl1 l2 l2' Hl2 l3 l3' Hl3. unfold ForallTriplets.
repeat (f_equiv ; auto ; intros ? ? ?). now apply HR.
Qed.

(*Definition sumbool_impl (P P' Q Q' : Prop) (f : P -> P') (g : Q -> Q') : 
    ({P} + {Q}) -> ({P'} + {Q'}) := fun t => 
  match t with 
  | left t1 => left (f t1)
  | right t2 => right (g t2) 
  end.*)

(* As with Forall, ForallTriplets is decidable (provided R is decidable). *)
Lemma ForallTriplets_dec R l1 l2 l3 : 
  (forall x y z, {R x y z} + {~ R x y z}) ->
  {ForallTriplets R l1 l2 l3} + {~ ForallTriplets R l1 l2 l3}.
Proof. intros Rdec. unfold ForallTriplets. repeat (apply Forall_dec ; intros ?). now apply Rdec. Qed.

(* The equivalence between ForallTriplets and regular forall. *)
Lemma ForallTriplets_forall R l1 l2 l3 : 
  (ForallTriplets R l1 l2 l3) <-> forall x y z, List.In x l1 -> List.In y l2 -> List.In z l3 -> R x y z.
Proof. 
unfold ForallTriplets. split.
+ intros H x y z Hinx Hiny Hinz.
  rewrite Forall_forall in H. specialize (H x Hinx).
  rewrite Forall_forall in H. specialize (H y Hiny).
  rewrite Forall_forall in H. specialize (H z Hinz).
  exact H.
+ intros H. 
  rewrite Forall_forall. intros x Hinx.
  rewrite Forall_forall. intros y Hiny.
  rewrite Forall_forall. intros z Hinz.
  auto.
Qed.

End ForallTriplets.

Section WeberPoint.
Implicit Types (points : list R2).

Local Existing Instances R2_VS R2_ES ForallTriplets_PermutationA_compat.

(* This would require proving (and more importantly stating) that for a similarity [f],
 * there exists an orthogonal matrix [A] and a vector [b] such that
 * [forall x, f(x) = f.(zoom)*A*x + b]. 
 * We would need mathcomp (or some other math library) to do this. *)
Lemma colinear_similarity x y z (f : similarity R2) : 
  colinear (f y - f x) (f z - f x) <-> colinear (y - x) (z - x).
Proof. Admitted. 

(* A finite collection of points are aligned iff every triplet of points are aligned. *)
(* This definition is based on lists : we could have used multisets,
 * and the code might have been cleaner (who knows). 
 * In the current state of things, we have to convert observations from multiset to list format, 
 * which requires lots of boilerplate lemmas. *)
Definition aligned (points : list R2) := 
  ForallTriplets (fun x y z => colinear (y - x) (z - x)) points points points.

(* [aligned] doesn't depent on the order of the points. *)
Local Instance aligned_compat : Proper (PermutationA equiv ==> equiv) aligned.
Proof using . intros p p' Hpp'. unfold aligned. now f_equiv. Qed.

(* Whether a finite collection of poitns are aligned is decidable. The proof given here 
 * obviously constructs a very slow algorithm (O(n^3)), but we don't really care. *)
Lemma aligned_dec points : {aligned points} + {~aligned points}.
Proof. unfold aligned. apply ForallTriplets_dec. intros x y z. apply colinear_dec. Qed.

Lemma aligned_similarity_weak points (f : similarity R2) :
  aligned points -> aligned (List.map f points).
Proof.
unfold aligned. repeat rewrite ForallTriplets_forall. intros H x y z.
repeat rewrite in_map_iff. intros [x0 [Hfx Hpx]] [y0 [Hfy Hpy]] [z0 [Hfz Hpz]].
rewrite <-Hfx, <-Hfy, <-Hfz. rewrite colinear_similarity. now apply H.
Qed.

Lemma aligned_similarity points (f : similarity R2) :
  aligned points <-> aligned (List.map f points).
Proof.
split ; try apply aligned_similarity_weak.
intros H. apply aligned_similarity_weak with (List.map f points) (inverse f) in H. revert H.
apply aligned_compat, eqlistA_PermutationA. rewrite <-List.map_id at 1. rewrite map_map. f_equiv.
intros x y Hxy. cbn -[equiv]. now rewrite Bijection.retraction_section.
Qed.

(* A Weber point of a finite collection P of points 
 * is a point that minimizes the sum of the distances to elements of P.
 * In general, there is no unique weber point for a collection.
 * However it is unique if the points in P are not colinear. *)

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

Lemma list_sum_le l l' : Forall2 Rle l l' -> (list_sum l <= list_sum l')%R.
Proof. 
intros HF. induction HF as [| x x' l l' Hx Hl IH] ; try now auto.
cbn -[equiv]. now apply Rplus_le_compat.
Qed.

Lemma list_sum_le_eps l l' eps : Forall2 Rle l l' -> 
  List.Exists (fun '(x, x') => (x <= x' + eps)%R) (combine l l') -> 
  (list_sum l <= list_sum l' + eps)%R.
Proof. 
intros HF HE. induction HF as [| x x' l l' Hx Hl IH].
+ exfalso. rewrite Exists_exists in HE. destruct HE as [x [Hin_nil _]]. now apply in_nil in Hin_nil.
+ cbn -[equiv] in *. rewrite Exists_cons in HE. 
  destruct HE as [Hx_eps | HE].
  - apply list_sum_le in Hl. lra.
  - apply IH in HE. lra.
Qed.

(* This is the function that a weber point minimizes. *)
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

(* [Weber] doesn't depend on the order of the points. *)
Local Instance weber_compat : Proper (PermutationA equiv ==> equiv ==> equiv) Weber.
Proof using .
  intros p p' Hpp' x y Hxy. unfold Weber. f_equiv ; try auto. intros z. now f_equiv.
Qed.

(* We can show that a weber point can equivalently be defined as
 * an argmin on a compact set of points (instead of an argmin on the whole plane),
 * and a continuous function always has a minimum on a compact set. *)
(* RMK : this is also true if [points] is empty. *)
Lemma weber_exists points : 
  exists x, Weber points x.
Proof. Admitted.

(* If the points aren't colinear, than the weber point is unique. *)
Lemma weber_unique points x y : 
  ~aligned points -> Weber points x -> Weber points y -> x == y.
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


(* A weber point is preserved by similarities. 
 * This is important because it means that all robots will calculate the same correct weber point, 
 * even though they view the configuration up to a change of frame (i.e. a similarity). *)
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
  exists t : R, (0 <= t)%R /\ (x == o + t * d)%VS.

Local Instance half_line_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) half_line.
Proof using .
intros x x' Hxx' y y' Hyy' z z' Hzz'. unfold half_line. now rewrite Hxx', Hyy', Hzz'. 
Qed.

(* If we move each point towards/away from the weber point in a straight line
 * (without crossing the weber point), the weber point is preserved. 
 * We can even move robots onto the weber point, it will still be preserved. *)
Lemma weber_half_line ps ps' w : 
  Forall2 (fun x y => half_line w (x - w) y) ps ps' -> Weber ps w -> Weber ps' w.
Proof. Admitted.

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

End WeberPoint.


Section Gathering.
Local Existing Instances aligned_compat weber_compat weber_calc_compat dist_sum_compat.

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
Ltac changeR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change R2_VS with LocVS in *;
  change R2_ES with LocES in *.


(* Robots don't have an state (and thus no memory) apart from their location. *)
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
Lemma multi_support_config config id : 
  PermutationA equiv 
    (multi_support (obs_from_config config (config id))) 
    (config_list config).
Proof.
cbv -[multi_support config_list equiv make_multiset List.map]. rewrite List.map_id.
apply PermutationA_countA_occ. intros x. rewrite multi_support_countA. now apply make_multiset_spec.
Qed. 

Corollary multi_support_map f config id : 
  Proper (equiv ==> equiv) (projT1 f) ->
  PermutationA equiv 
    (multi_support (obs_from_config (map_config (lift f) config) (lift f (config id))))
    (List.map (projT1 f) (config_list config)).
Proof.  
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
  changeR2. lra.
- assert (Hzoom := Similarity.zoom_pos (change_frame da config1 g ⁻¹)).
  eapply Rmult_le_reg_l; eauto; []. simpl.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l; trivial; [].
  changeR2. generalize (Similarity.zoom_pos (change_frame da config1 g)). lra.
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
Proof. 
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
  pose (sim := change_frame da config g). changeR2. fold sim.
  assert (Hweb : weber_calc (multi_support obs) == sim (weber_calc (config_list config))).
  {
    unfold obs. rewrite multi_support_map by auto. unfold f. cbn -[equiv config_list].
    changeR2. fold sim. 
    apply weber_unique with (List.map sim (config_list config)).
    - now rewrite <-aligned_similarity.
    - apply weber_calc_correct.
    - apply weber_similarity, weber_calc_correct.
  }
  change location_Setoid with state_Setoid. apply update_compat ; auto.
  - intros r. cbn -[equiv]. rewrite Bijection.retraction_section. reflexivity.
  - intros r. rewrite Hweb. 
    pose (w := weber_calc (config_list config)). fold w. 
    pose (c := config (Good g)). fold c.
    cbn -[equiv w c opp RealVectorSpace.add mul inverse].
    rewrite sim_mul.  
    assert (Hcenter : (sim ⁻¹) 0%VS == c).
    { changeR2. change_LHS (center sim). apply Hsim. }
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
Proof. 
intros Hsim Halign. assert (round gatherW da config == config) as H.
{ intros id. destruct (round_simplify config Hsim) as [r Hround].
  rewrite Hround. repeat destruct_match ; auto. }
now rewrite H.
Qed.

Lemma aligned_over config (d : demon) :
  Stream.forever (Stream.instant similarity_da_prop) d ->
  aligned (config_list config) -> eventually_aligned config d gatherW.
Proof.
Admitted.



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

(* This would have been much more pleasant to do with mathcomp's tuples. *)
Lemma config_list_In_combine x x' c c' : 
  List.In (x, x') (combine (config_list c) (config_list c')) <-> 
  exists id, x == c id /\ x' == c' id.
Proof.
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

Lemma measure_noneg config : (0 <= measure config)%R.
Proof. Admitted.

Lemma half_line_origin o d : half_line o d o.
Proof. 
unfold half_line. exists 0%R. split ; [apply Rle_refl|].
rewrite mul_0, add_origin_r. reflexivity.
Qed.

Lemma half_line_segment x y : half_line x (y - x) y.
Proof.
unfold half_line. exists 1%R. split ; [apply Rle_0_1|].
rewrite mul_1, RealVectorSpace.add_comm, <-add_assoc.
assert (H := add_opp x). rewrite RealVectorSpace.add_comm in H. rewrite H.
rewrite add_origin_r. reflexivity.
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


Lemma combine_map {A B C : Type} l l' (f : A -> C) (f' : B -> C) : 
  combine (List.map f l) (List.map f' l') = List.map (fun '(x, x') => (f x, f' x')) (combine l l').
Proof.
generalize l'. clear l'. induction l as [| x l IH] ; intros [|x' l'] ; cbn ; try reflexivity.
f_equal. apply IH.
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
      pose (w := weber_calc (config_list config)). changeR2. fold w. 
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
        apply Rplus_le_compat ; try lra. Search Ropp Rmult. 
        rewrite <-Ropp_mult_distr_l. now apply Ropp_le_contravar.
      --exfalso. apply HNreached. rewrite Hround. destruct_match ; [|intuition].
        cbn -[config_list dist mul opp RealVectorSpace.add].
        rewrite Rmult_1_l, good_unpack_good ; unfold id ; fold x ; fold ri ; changeR2 ; fold w.
        destruct_match ; intuition. 
        rewrite mul_1, (RealVectorSpace.add_comm w), RealVectorSpace.add_assoc. 
        now simplifyR2.
    * exfalso. apply Hi. rewrite Hround. destruct_match ; intuition.
Qed.

(* This is the well founded relation we will perform induction on. *)
Definition lt_config eps c c' := 
  (0 <= measure c <= measure c' - eps)%R. 

Lemma lt_config_compat : Proper (equiv ==> equiv ==> equiv ==> iff) lt_config.
Proof. Admitted.

Lemma lt_config_wf eps : (eps > 0)%R -> well_founded (lt_config eps).
Proof. Admitted.


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
changeR2. change location_Setoid with state_Setoid in *. rewrite config_list_InA in Hin.
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

(* The proof is essentially a well-founded induction on [measure config].
 * Fairness ensures that the measure must decrease at some point. *)
Theorem weber_correct (d : demon) config : 
  Fair d -> Stream.forever (Stream.instant similarity_da_prop) d ->
  eventually_aligned config d gatherW.
Proof.
remember (measure config) as k. 
generalize dependent d. generalize dependent config.
pattern k. apply (well_founded_ind lt_wf). clear k.
intros k IHk config Hk d Hfair Hsim.
destruct (aligned_dec (config_list config)) as [align | Nalign] ;
  [now apply aligned_over|].
induction (fair_first_move config Hfair Hsim Nalign) as [d config Hmove | d config Hmove FM IH_FM] ;
  destruct Hsim as [Hsim_hd Hsim_tl] ; cbn in Hsim_hd ; apply Stream.Later.
+ destruct (round_decreases_measure config Hsim_hd Hmove) as [Ralign | Rmeasure].
  - now apply aligned_over.
  - eapply IHk. 
    * rewrite Hk. exact Rmeasure.  
    * reflexivity.
    * destruct Hfair as [_ Hfair_tl]. exact Hfair_tl.
    * exact Hsim_tl.
+ apply no_moving_same_config in Hmove.
  apply IH_FM ; (try rewrite Hmove) ; auto.
  destruct Hfair as [_ Hfair_tl]. exact Hfair_tl.
Qed.

End Gathering.