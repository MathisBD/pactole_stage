
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* Author : Mathis Bouverot-Dupuis (June 2022).

 * This file gives the definition and some properties of the Weber point
 * in the real plane (R²). The weber point (also called geometric median) 
 * of a finite collection of points is unique if the points are not aligned,
 * and has the property that moving any point towards the weber point 
 * in a straight line doesn't change the weber point. *) 
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
Require Import SetoidDec.

(* Helping typeclass resolution avoid infinite loops. *)
Typeclasses eauto := (bfs).

Require Import Pactole.Spaces.R2.
Require Import Pactole.Util.SetoidDefs.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Spaces.Similarity.
Require Import Pactole.CaseStudies.Gathering.InR2.Weber.Utils.

Set Implicit Arguments.

Close Scope R_scope.
Close Scope VectorSpace_scope.


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
Global Instance aligned_compat : Proper (PermutationA equiv ==> equiv) aligned.
Proof using . intros p p' Hpp'. unfold aligned. now f_equiv. Qed.

Lemma aligned_tail p0 ps : aligned (p0 :: ps) -> aligned ps. 
Proof. 
unfold aligned. rewrite 2 ForallTriplets_forall. intros H x y z Hinx Hiny Hinz.
apply H ; now right. 
Qed.

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

Lemma aligned_spec p0 ps : 
  aligned (p0 :: ps) <-> exists v, forall p, InA equiv p ps -> exists t, (p == p0 + t * v)%VS.
Proof. 
split.
+ case (list_all_eq_or_perm p0 ps) as [Hall_eq | [p1 [ps' [Hperm Hp1p0]]]].
  - intros _. exists 0%VS. intros p Hin. apply Hall_eq in Hin. rewrite Hin. 
    exists 0%R. rewrite mul_0, add_origin_r. reflexivity.
  - unfold aligned. rewrite ForallTriplets_forall.
    setoid_rewrite <-InA_Leibniz. change (@eq R2) with (@equiv R2 _).
    setoid_rewrite Hperm. intros H. 
    exists (p1 - p0)%VS. intros p Hin.
    specialize (H p0 p1 p). feed_n 3 H ; 
      [now left | now right ; left | now right ; apply Hin |].
    apply colinear_exists_mul in H.
    * destruct H as [t H]. exists t. now rewrite <-H, add_sub.
    * now rewrite R2sub_origin.
+ intros [v H]. unfold aligned. rewrite ForallTriplets_forall.
  setoid_rewrite <-InA_Leibniz. change (@eq R2) with (@equiv R2 _).
  intros x y z Hinx Hiny Hinz. 
  assert (H' : forall p, InA equiv p (p0 :: ps) -> exists t, p == (p0 + t * v)%VS).
  {
    intros p Hin. rewrite InA_cons in Hin. case Hin as [Hin1 | Hin2].
    - exists 0%R. now rewrite Hin1, mul_0, add_origin_r.
    - now apply H.  
  }
  apply H' in Hinx, Hiny, Hinz. 
  destruct Hinx as [tx Hx].
  destruct Hiny as [ty Hy].
  destruct Hinz as [tz Hz].
  rewrite Hx, Hy, Hz. 
  rewrite (RealVectorSpace.add_comm _ (ty * v)), (RealVectorSpace.add_comm _ (tz * v)).
  rewrite <-2 RealVectorSpace.add_assoc, opp_distr_add.
  rewrite (RealVectorSpace.add_assoc p0), add_opp, add_origin_l.
  rewrite <-minus_morph, 2 add_morph.
  apply colinear_mul_compat_l, colinear_mul_compat_r.
  reflexivity.
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

Lemma list_sum_ge_0 l : 
  Forall (Rle 0%R) l -> (0 <= list_sum l)%R. 
Proof.
intros H. transitivity (list_sum (alls 0%R (length l))).
+ apply Req_le_sym. induction l as [|x l IH] ; auto.
  cbn. rewrite IH ; try lra. rewrite Forall_cons_iff in H. apply H.
+ apply list_sum_le. induction l as [|x l IH] ; cbn ; auto.
  rewrite Forall_cons_iff in H. apply Forall2_cons ; intuition.
Qed. 
(* This is the function that a weber point minimizes. *)
Definition dist_sum points (x : R2) := 
  list_sum (List.map (dist x) points).

Local Instance dist_sum_compat : Proper (PermutationA equiv ==> equiv ==> equiv) dist_sum.
Proof using .
intros p p' Hpp' x y Hxy. unfold dist_sum. f_equiv. now rewrite Hpp', Hxy.
Qed.

Lemma dist_sum_nonneg points x : (0 <= dist_sum points x)%R.
Proof.
apply list_sum_ge_0. rewrite Forall_forall. intros d Hin. rewrite in_map_iff in Hin.
destruct Hin as [y [Hd Hin]]. rewrite <-Hd. apply dist_nonneg.
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
Global Instance weber_compat : Proper (PermutationA equiv ==> equiv ==> equiv) Weber.
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

Lemma half_line_origin o d : half_line o d o.
Proof. 
unfold half_line. exists 0%R. split ; [apply Rle_refl|].
rewrite mul_0, add_origin_r. reflexivity.
Qed.

Lemma half_line_segment x y : half_line x (y - x) y.
Proof.
unfold half_line. exists 1%R. split ; [apply Rle_0_1|].
now rewrite mul_1, add_sub.
Qed.

Lemma half_line_mul_dir o d x t : 
  (0 < t)%R -> (half_line o d x <-> half_line o (t * d)%VS x).
Proof. 
intros Ht. split ; intros [s [Hs Hx]] ; unfold half_line.
+ exists (s / t)%R. split. 
  - unfold Rdiv. now apply Rle_mult_inv_pos.
  - rewrite Hx. f_equiv. rewrite mul_morph. f_equiv. unfold Rdiv.  
    rewrite Rmult_assoc, Rinv_l ; lra.
+ exists (s * t)%R. split.
  - nra.
  - rewrite Hx. f_equiv. now rewrite mul_morph.
Qed.

(* If we move each point towards/away from the weber point in a straight line
 * (without crossing the weber point), the weber point is preserved. 
 * We can even move points onto the weber point, it will still be preserved. *)
Lemma weber_half_line ps ps' w : 
  Forall2 (fun x y => half_line w (x - w) y) ps ps' -> Weber ps w -> Weber ps' w.
Proof. Admitted.

(* A weber point of aligned points is on the same line. *)
Lemma weber_aligned ps w : aligned ps -> Weber ps w -> aligned (w :: ps).
Proof. Admitted.

End WeberPoint.
