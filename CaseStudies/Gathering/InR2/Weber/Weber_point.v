
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
Require Import Pactole.Util.Ratio.
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
  Proper (PermutationA equiv ==> equiv) list_sum.
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

Lemma list_sum_map_opp {A : Type} (f : A -> R) l : 
  (-(list_sum (map f l)) == list_sum (map (fun x => -(f x)) l))%R.
Proof. Admitted.

Lemma list_sum_map_add {A : Type} (f1 f2 : A -> R) l1 l2 : 
  length l1 = length l2 -> 
  (list_sum (map f1 l1) + list_sum (map f2 l2) == 
    list_sum (map (fun '(x1, x2) => f1 x1 + f2 x2) (combine l1 l2)))%R.
Proof. Admitted.

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
Definition argmin {A : Type} (f : A -> R) : A -> Prop := 
  fun a => forall b, (f a <= f b)%R.
  
Local Instance argmin_compat {A : Type} : Proper (equiv ==> @eq A ==> iff) argmin.
Proof using . 
intros f g Hfg a a' Haa'. unfold argmin.
rewrite <-Haa'. setoid_rewrite <-Hfg.
reflexivity.
Qed.

(* The set of Weber points of a finite collection of points *)
Definition Weber points : R2 -> Prop := argmin (dist_sum points).

(* [Weber] doesn't depend on the order of the points. *)
Global Instance weber_compat : Proper (PermutationA equiv ==> equiv ==> iff) Weber.
Proof using .
  intros p p' Hpp' x y Hxy. unfold Weber. f_equiv ; try auto. intros z. now f_equiv.
Qed.

(* [OnlyWeber ps w] means that [w] is the unique weber point of [ps]. *)
Definition OnlyWeber ps w : Prop := Weber ps w /\ (forall x, Weber ps x -> x == w).

Global Instance only_weber_compat : Proper (PermutationA equiv ==> equiv ==> iff) OnlyWeber.
Proof. intros ? ? H1 ? ? H2. unfold OnlyWeber. setoid_rewrite H1. setoid_rewrite H2. reflexivity. Qed.

(* We can show that a weber point can equivalently be defined as
 * an argmin on a compact set of points (instead of an argmin on the whole plane),
 * and a continuous function always has a minimum on a compact set. *)
(* RMK : this is also true if [points] is empty. *)
Lemma weber_exists points : 
  exists x, Weber points x.
Proof. Admitted.

(* If the points aren't colinear, than the weber point is unique. *)
Lemma weber_unique points w : 
  ~aligned points -> Weber points w -> OnlyWeber points w.
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
unfold Weber, argmin. intros H b. 
rewrite <-(Bijection.section_retraction f b). 
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

(* A weber point of aligned points is on the same line. *)
Lemma weber_aligned ps w : aligned ps -> Weber ps w -> aligned (w :: ps).
Proof. Admitted.

(* [segment a b] represents the set of points that are in the segment 
 * [a, b], endpoints included. *)
Definition segment (a b : R2) : R2 -> Prop := fun x =>
  exists t : R, (0 <= t <= 1)%R /\ (x == t * a + (1 - t) * b)%VS.

Local Instance segment_compat : Proper (equiv ==> equiv ==> equiv ==> iff) segment.
Proof using .
intros ? ? H1 ? ? H2 ? ? H3. unfold segment. now rewrite H1, H2, H3. 
Qed.

Lemma segment_sym a b x : segment a b x <-> segment b a x.
Proof.
revert a b x. 
cut (forall a b x, segment a b x -> segment b a x).
{ intros H. split ; apply H. }
intros a b x.
unfold segment. intros [t [Ht Hx]].
exists (1 - t)%R. split ; [lra|].
assert (H : ((1 - (1 - t)) == t)%R).
{ unfold Rminus. now rewrite Ropp_plus_distr, Ropp_involutive, <-Rplus_assoc, Rplus_opp_r, Rplus_0_l. } 
rewrite H, RealVectorSpace.add_comm. exact Hx.
Qed. 

Lemma segment_start a b : segment a b a.
Proof. 
unfold segment. exists 1%R. split ; [lra|]. 
now rewrite mul_1, Rminus_eq_0, mul_0, add_origin_r.
Qed.

Lemma segment_end a b : segment a b b.
Proof. 
unfold segment. exists 0%R. split ; [lra|]. 
now rewrite mul_0, Rminus_0_r, mul_1, add_origin_l.
Qed.

Lemma segment_straight_path a b (r : ratio) : segment a b (straight_path a b r).
Proof.
rewrite segment_sym. unfold segment. exists r. split.
+ apply ratio_bounds.
+ cbn -[equiv RealVectorSpace.add mul opp].
  rewrite mul_distr_add, 2 (RealVectorSpace.add_comm (r * b)), RealVectorSpace.add_assoc.
  f_equiv. unfold Rminus. rewrite <-add_morph, mul_1. f_equiv.
  now rewrite minus_morph, mul_opp.
Qed.

(* [contract ps ps' x] means that [ps'] is obtained from [ps] by moving
 * each point towards [x].*)
Definition contract ps ps' x : Prop := 
  Forall2 (fun p p' => segment x p p') ps ps'.

Lemma segment_dist_weak x a b : 
  segment a b x -> dist a b = (dist a x + dist x b)%R.
Proof. 
unfold segment. intros [t [Ht Hx]].
assert (H1t : (0 <= 1 - t <= 1)%R). { lra. }
pose (rt := exist (fun t => 0 <= t <= 1)%R t Ht).
pose (r1t := exist (fun t => 0 <= t <= 1)%R (1 - t)%R H1t).
assert (Hx1 : x == straight_path a b r1t).
{ 
cbn -[equiv mul RealVectorSpace.add opp]. unfold Rminus. 
rewrite <-add_morph, mul_1, RealVectorSpace.add_assoc, add_sub.
rewrite minus_morph, mul_distr_add, opp_distr_add, mul_opp, opp_opp.
rewrite RealVectorSpace.add_assoc, RealVectorSpace.add_comm, Hx.
f_equiv. unfold Rminus. rewrite <-add_morph, mul_1, minus_morph. reflexivity.
}
assert (Hx2 : x == straight_path b a rt).
{
cbn -[equiv mul RealVectorSpace.add opp]. rewrite Hx. 
unfold Rminus. rewrite <-add_morph, mul_distr_add, mul_1, minus_morph, mul_opp.
rewrite 2 RealVectorSpace.add_assoc. f_equiv. rewrite RealVectorSpace.add_comm.
reflexivity.
}
rewrite Hx1 at 1. rewrite straight_path_dist_start.
rewrite (dist_sym _ x), Hx2, straight_path_dist_start.
cbn -[dist]. rewrite (dist_sym a b). lra.
Qed.

Lemma segment_dist_sum a b x :
  segment a b x <-> dist a b = (dist a x + dist x b)%R.
Proof.
split ; [apply segment_dist_weak|]. 
case (a =?= b) as [Eab | NEab].
+ rewrite Eab, dist_same. rewrite dist_sym. intros Hdist. 
  assert (H : dist x b = 0%R). { lra. }
  rewrite dist_defined in H. rewrite H. apply segment_start.
+ intros Hdist. destruct (triang_ineq_eq _ _ _ Hdist) as [Hcol _].
  apply colinear_exists_mul in Hcol. destruct Hcol as [t Hxa].
  2: intros H ; apply NEab ; rewrite R2sub_origin in H ; now symmetry.
  assert (Ht : (Rabs t + Rabs (t - 1) == 1)%R).
  {
    assert (Hxb : (x - b)%VS == ((t - 1) * (b - a))%VS).
    { unfold Rminus. rewrite <-add_morph, minus_morph, mul_1, <-Hxa.
      rewrite <-RealVectorSpace.add_assoc. f_equiv. 
      now rewrite opp_distr_add, add_sub. }
    rewrite (dist_sym x a), (dist_sym b a) in Hdist. repeat rewrite norm_dist in Hdist.
    rewrite Hxa, Hxb in Hdist. repeat rewrite norm_mul in Hdist.
    rewrite <-Rmult_plus_distr_r in Hdist.
    rewrite <-(Rmult_1_l (norm (b - a)%VS)) in Hdist at 1. Search Rmult "reg".
    apply Rmult_eq_reg_r in Hdist ; [now symmetry|].
    rewrite norm_defined. intros H. apply NEab. rewrite R2sub_origin in H. now symmetry.
  }
  rewrite segment_sym. exists t. split.
  - case (Rle_dec 0%R t) as [Rle_0t | NRle_0t] ; case (Rle_dec t 1%R) as [Rle_t1 | NRle_t1] ; [lra | exfalso ..]. 
    * rewrite Rabs_pos_eq in Ht by auto. rewrite Rabs_pos_eq in Ht by lra.
      assert (Ht1 : t == 1%R). { cbn in Ht |- *. lra. }
      intuition.
    * rewrite Rabs_left1 in Ht by lra. rewrite Rabs_left1 in Ht by lra.
      assert (Ht0 : t == 0%R). { cbn in Ht |- *. lra. }
      intuition.
    * rewrite Rabs_left1 in Ht by lra. rewrite Rabs_pos_eq in Ht by lra. lra.
  - unfold Rminus. rewrite <-add_morph, mul_1, minus_morph, <-mul_opp.
    rewrite (RealVectorSpace.add_comm a), RealVectorSpace.add_assoc, <-mul_distr_add.
    rewrite <-Hxa, <-RealVectorSpace.add_assoc, (RealVectorSpace.add_comm _ a), add_opp, add_origin_r.
    reflexivity.
Qed.

Lemma segment_argmin x a b : segment x a b <-> argmin (fun y => (dist y b - dist y a)%R) x.
Proof.
split.
+ intros Hsegment y. rewrite segment_dist_sum in Hsegment. rewrite Hsegment.
  unfold Rminus at 1. rewrite Ropp_plus_distr, <-Rplus_assoc, Rplus_opp_r, Rplus_0_l.
  cut (dist y a <= dist y b + dist b a)%R. { lra. }
  apply RealMetricSpace.triang_ineq.
+ unfold argmin. intros Hdist. rewrite segment_dist_sum.
  apply Rle_antisym ; [apply RealMetricSpace.triang_ineq |]. 
  specialize (Hdist b). rewrite dist_same, Rminus_0_l in Hdist.
  lra.
Qed.

Lemma Rminus_eq0_iff x y : (x - y)%R = 0%R <-> x = y. 
Proof. lra. Qed.

Lemma Rle_minus_sim r1 r2 : (r1 <= r2)%R -> (0 <= r2 - r1)%R.
Proof. lra. Qed.

Lemma argmin_sum2 {A : Type} (f g : A -> R) x0 x :
  argmin f x0 -> argmin g x0 -> 
  (argmin (fun x => (f x + g x)%R)x <-> argmin f x /\ argmin g x).
Proof. 
intros Hf0 Hg0. split ; unfold argmin in *.
+ intros Hfg.
  cut (f x = f x0 /\ g x = g x0). { intros [-> ->]. intuition. }
  rewrite <-(Rminus_eq0_iff (f x)), <-(Rminus_eq0_iff (g x)).
  apply Rplus_eq_R0.
  - apply Rle_minus_sim, Hf0.
  - apply Rle_minus_sim, Hg0.
  - cut ((f x + g x)%R = (f x0 + g x0)%R). { lra. }
    apply Rle_antisym ; [apply Hfg|].
    apply Rplus_le_compat ; auto.    
+ intros [Hf Hg] y. apply Rplus_le_compat.
  - apply Hf.
  - apply Hg.
Qed. 

Lemma argmin_sum {A : Type} (F : list (A -> R)) x0 x :
  (Forall (fun f => argmin f x0) F) -> 
  (argmin (fun x => list_sum (map (fun f => f x) F)%R)x <-> Forall (fun f => argmin f x) F).
Proof. 
intros HF0. revert x. induction F as [|f F IH] ; intros x. 
+ cbn. split ; intros _ ; [constructor|].
  unfold argmin. reflexivity.
+ rewrite Forall_cons_iff in HF0 |- *. destruct HF0 as [Hf0 HF0]. 
  specialize (IH HF0). cbn. rewrite <-IH. apply argmin_sum2 with x0 ; auto.
  rewrite IH. exact HF0.
Qed.


Lemma dist_sum_diff_eq ps ps' x : 
  length ps' = length ps -> 
  (dist_sum ps' x - dist_sum ps x)%R == list_sum (map 
    (fun '(p', p) => (dist x p' - dist x p)%R) 
    (combine ps' ps)).
Proof.
intros Hlen. unfold Rminus, dist_sum. 
rewrite list_sum_map_opp, list_sum_map_add by now symmetry.
reflexivity.
Qed. 

Lemma contract_argmin_weak ps ps' x : 
  contract ps ps' x -> argmin (fun y => (dist_sum ps' y - dist_sum ps y)%R) x.
Proof.
intros Hcontract y. rewrite 2 dist_sum_diff_eq.
2, 3: now symmetry ; eapply Forall2_length, Hcontract.
apply list_sum_le. rewrite Forall2_Forall, combine_map, Forall_map, Forall_forall by now rewrite 2 map_length.
intros [a b] Hin. rewrite in_combine_id in Hin. destruct Hin as [<- Hin].
destruct a as [p' p]. apply segment_argmin. assert (H := Hcontract). 
revert H. unfold contract. rewrite Forall2_Forall, Forall_forall by eapply Forall2_length, Hcontract.
intros H. specialize (H (p, p')). apply H. now rewrite in_combine_sym. 
Qed.

(* This is quite an amusing property. *)
Lemma contract_argmin ps ps' x0 x : 
  contract ps ps' x0 ->  
  (contract ps ps' x <-> argmin (fun y => (dist_sum ps' y - dist_sum ps y)%R) x).
Proof. 
intros Hcontract0. split. 
+ apply contract_argmin_weak.
+ Check argmin_sum. (* use the -> direction of argmin_sum. *)

Admitted.


(* See the thesis of Zohir Bouzid, lemma 3.1.5. *)
Lemma weber_contract_strong ps ps' w0 : 
  contract ps ps' w0 -> Weber ps w0 ->
  (forall w, Weber ps' w <-> (Weber ps w /\ contract ps ps' w)).
Proof. 
intros Hcontract0 Hweb0 w. rewrite contract_argmin in * ; eauto. unfold Weber in *.
rewrite <-(argmin_sum2 _ Hweb0 Hcontract0). f_equiv. 
intros x. rewrite Rplus_minus. reflexivity.
Qed.

(* We can even move points onto the weber point, it will still be preserved. *)
Corollary weber_contract ps ps' w : 
  contract ps ps' w -> Weber ps w -> Weber ps' w.
Proof. 
intros Hcontract Hweb. rewrite (weber_contract_strong Hcontract Hweb). intuition.
Qed.

(* See the thesis of Zohir Bouzid, corollary 3.1.1. *)
Corollary weber_contract_unique ps ps' w : 
  contract ps ps' w -> OnlyWeber ps w -> OnlyWeber ps' w. 
Proof.
intros Hcontract [Hweb HwebU]. split.
+ rewrite (weber_contract_strong Hcontract Hweb). intuition.
+ intros w' Hweb'. apply HwebU. 
  rewrite (weber_contract_strong Hcontract Hweb) in Hweb'.
  intuition.
Qed.

End WeberPoint.
