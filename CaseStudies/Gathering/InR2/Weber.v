
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

Print ForallPairs.

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

(* The determinant of two vectors in R². 
 * We use this to define what it means for two vectors to be parallel. *)
(*Definition det (x y : R2) := (fst x * snd y - snd x * fst y)%R.*)

(*Local Instance det_compat : Proper (equiv ==> equiv ==> equiv) det. 
Proof using . intros x x' Hxx' y y' Hyy'. unfold det. now rewrite Hxx', Hyy'. Qed. *)

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
Local Existing Instances aligned_compat weber_compat weber_calc_compat.

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
Ltac changeR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change R2_VS with LocVS in *;
  change R2_ES with LocES in *.


(* Robots don't have an state (and thus no memory) apart from their location. *)
Local Instance St : State location := OnlyLocation (fun f => True).
Local Instance RobotC : robot_choice location := {| robot_choice_Setoid := location_Setoid |}.

(* Robots view the other robots' positions up to a similarity. *)
Local Instance FrameC : frame_choice (similarity location) := FrameChoiceSimilarity.
Local Instance UpdateC : update_choice unit := NoChoice.
Local Instance InactiveC : inactive_choice unit := NoChoiceIna.

(* We are in a rigid and semi-synchronous setting (for now). *)
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
  - now apply weber_calc_correct.
  - rewrite Hs. now apply weber_calc_correct.
Qed.

Definition gatherW : robogram := {| pgm := gatherW_pgm |}.

Lemma eq_dec_refl {A B : Type} `(eq_dec : EqDec A) (x : A) (u v : B) : 
  (if eq_dec x x then u else v) = u.
Proof. destruct_match ; [reflexivity | unfold complement in c ; intuition]. Qed.

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
  - rewrite e. cbn. now rewrite (eq_dec_refl eq_dec), IH.
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
    specialize (Hcount y). revert Hcount ; cbn. rewrite (eq_dec_refl eq_dec). discriminate.
  - rewrite (PermutationA_count_split _ eq_dec x l).
    rewrite (PermutationA_count_split _ eq_dec x l').
    rewrite app_comm_cons. f_equiv.
    * apply eqlistA_PermutationA. rewrite <-Hcount. cbn. rewrite (eq_dec_refl eq_dec).
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

(* Simplify the [round] function and express it in the global frame of reference. *)
(* All the proofs below use this simplified version. *)
Lemma round_simplify da config : similarity_da_prop da -> 
  round gatherW da config == 
  fun id => 
    if activate da id then 
      if aligned_dec (config_list config) then config id 
      else weber_calc (config_list config)
    else config id.
Proof. 
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
  apply weber_unique with (config_list config) ; [now auto| |now apply weber_calc_correct].
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
Proof. 
intros Hsim Halign. assert (round gatherW da config == config) as H.
{ intros id. rewrite round_simplify by auto. repeat destruct_match ; auto. }
now rewrite H.
Qed.

Lemma aligned_over config (d : demon) :
  Stream.forever (Stream.instant similarity_da_prop) d ->
  aligned (config_list config) -> eventually_aligned config d gatherW.
Proof.
Admitted.


Lemma sub_lt_sub (i j k : nat) : j < i <= k -> k - i < k - j.
Proof. lia. Qed.

Lemma countA_occ_le w ps ps' :
  Forall2 (fun x x' => x' == x \/ x' == w) ps ps' -> 
    countA_occ equiv R2_EqDec w ps <= countA_occ equiv R2_EqDec w ps'.
Proof. 
intros HF. induction HF as [| x x' l l' Hxx' Hll' IH] ; [auto|].
cbn -[equiv]. repeat destruct_match ; intuition.
rewrite H, e in c. intuition.
Qed.

Lemma countA_occ_lt w ps ps' : 
  Forall2 (fun x x' => x' == x \/ x' == w) ps ps' -> 
  List.Exists (fun '(x, x') => x' =/= x) (combine ps ps') ->
    countA_occ equiv R2_EqDec w ps < countA_occ equiv R2_EqDec w ps'.
Proof.
intros HF HE. induction HF as [| x x' l l' Hxx' Hll' IH].
+ rewrite Exists_exists in HE. destruct HE as [x [In_nil _]]. now apply in_nil in In_nil.
+ cbn -[complement equiv] in HE. rewrite Exists_cons in HE.
  destruct HE as [Dxx' | HE].
  - destruct Hxx' as [Exx' | Ex'w] ; intuition.
    rewrite Ex'w in Dxx' |- *. cbn -[equiv].
    repeat destruct_match ; intuition. apply le_lt_n_Sm. now apply countA_occ_le.
  - destruct Hxx' as [Exx' | Ex'w] ; cbn -[equiv] ; repeat destruct_match ; intuition.
    rewrite Exx', e in c. intuition.
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

Lemma list_in_length_n0 {A : Type} x (l : list A) : List.In x l -> length l <> 0.
Proof. intros Hin. induction l as [|y l IH] ; cbn ; auto. Qed.

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


(* This measure strictly decreases whenever a robot moves. *)
Definition measure config := 
  let ps := config_list config in 
  n - countA_occ equiv R2_EqDec (weber_calc ps) ps.

Local Instance measure_compat : Proper (equiv ==> eq) measure.
Proof. intros c c' Hc. unfold measure. now rewrite Hc. Qed.

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
 * This still holds in a flexible and/or asynchronous setting.
 * The point calculated by weber_calc thus stays the same during an execution,
 * until the robots are colinear. *)
Lemma round_preserves_weber config da w :
  similarity_da_prop da -> Weber (config_list config) w -> 
    Weber (config_list (round gatherW da config)) w.
Proof. 
intros Hsim Hweb. apply weber_half_line with (config_list config) ; auto.
rewrite Forall2_Forall, Forall_forall by now repeat rewrite config_list_length.
intros [x x']. rewrite config_list_In_combine.
intros [id [Hx Hx']]. revert Hx'. rewrite round_simplify by auto. 
repeat destruct_match ; intros Hx' ; rewrite Hx, Hx' ; try apply half_line_segment.
assert (w == weber_calc (config_list config)) as Hw.
{ apply weber_unique with (config_list config) ; auto. apply weber_calc_correct. }
rewrite Hw. apply half_line_origin.
Qed.

(* If a robot moves, either the measure decreases or the robots become colinear. *)
Lemma round_decreases_measure config da : 
  similarity_da_prop da ->
  moving gatherW da config <> nil -> 
    aligned (config_list (round gatherW da config)) \/ 
    measure (round gatherW da config) < measure config.
Proof. 
intros Hsim Hmove. 
destruct (aligned_dec (config_list (round gatherW da config))) as [Rcol | RNcol] ; [now left|right].
assert (weber_calc (config_list (round gatherW da config)) == weber_calc (config_list config)) as Hweb.
{ 
  apply weber_unique with (config_list (round gatherW da config)) ; auto.
  + apply weber_calc_correct.
  + apply round_preserves_weber ; [auto | apply weber_calc_correct].  
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
Proof. 
rewrite Forall_forall. intros Hgathered.
unfold aligned. rewrite ForallTriplets_forall.
intros a b c Ha Hb Hc.
apply Hgathered in Ha, Hb, Hc. rewrite Ha, Hb, Hc, add_opp.
apply colinear_origin_r.
Qed.

Lemma contra (P Q : Prop) : (Q -> P) -> (~P -> ~Q).
Proof. intuition. Qed.

(* If the robots aren't aligned yet then there exists at least one robot which, 
 * if activated, will move. 
 * Any robot that isn't on the weber point will do the trick. *)
Lemma one_must_move config : ~aligned (config_list config) ->
  exists r, forall da, similarity_da_prop da -> activate da r = true ->
                       round gatherW da config r =/= config r.
Proof.
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