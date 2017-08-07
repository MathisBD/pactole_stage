(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                           
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence         
                                                                          *)
(**************************************************************************)


Require Import Rbase R_sqrt Rbasic_fun.
Require Import Psatz.
Require Import RelationPairs.
Require Import SetoidPermutation.
Require Import Omega.
Import List Permutation SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Spaces.RealMetricSpace.
Set Implicit Arguments.
Open Scope R_scope.


(** Some results about [R]. *)
Lemma sqrt_subadditive : forall x y, 0 <= x -> 0 <= y -> sqrt (x + y) <= sqrt x + sqrt y.
Proof.
intros x y Hx Hy. apply R_sqr.Rsqr_incr_0.
- repeat rewrite Rsqr_sqrt, ?R_sqr.Rsqr_plus; try lra.
  assert (0 <= 2 * sqrt x * sqrt y).
  { repeat apply Rmult_le_pos; try lra; now apply sqrt_positivity. }
  lra.
- apply sqrt_positivity. lra.
- apply Rplus_le_le_0_compat; now apply sqrt_positivity.
Qed.

Lemma pos_Rsqr_eq : forall x y, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof. intros. setoid_rewrite <- sqrt_Rsqr; trivial. now f_equal. Qed.

Lemma pos_Rsqr_le : forall x y, 0 <= x -> 0 <= y -> (x² <= y² <-> x <= y).
Proof. intros. split; intro; try now apply R_sqr.Rsqr_incr_0 + apply R_sqr.Rsqr_incr_1. Qed.

Lemma pos_Rsqr_lt : forall x y, 0 <= x -> 0 <= y -> (x² < y² <-> x < y).
Proof. intros. split; intro; try now apply R_sqr.Rsqr_incrst_0 + apply R_sqr.Rsqr_incrst_1. Qed.


(** **  R² as a vector space over R  **)

Definition R2 := (R * R)%type.
Instance R2_Setoid : Setoid R2 := {| equiv := @Logic.eq R2 |}.
Instance R2_EqDec : @EqDec R2 _.
Proof.
intros x y.
destruct (Rdec (fst x) (fst y)).
+ destruct (Rdec (snd x) (snd y)).
  - left. abstract (destruct x, y; cbn in *; subst; reflexivity).
  - right. abstract (destruct x, y; injection; auto).
+ right. abstract (destruct x, y; injection; auto).
Defined.

Ltac solve_R := repeat intros [? ?] || intro; compute; f_equal; ring.

Instance R2_RMS : RealMetricSpace R2 := {|
  origin := (0, 0);
  unit := (1, 0);
  dist := fun x y => sqrt ((fst x - fst y)² + (snd x - snd y)²);
  add := fun x y => let '(x1, x2) := x in let '(y1, y2) := y in (x1 + y1, x2 + y2)%R;
  mul := fun k x => let '(x1, x2) := x in (k * x1, k * x2)%R;
  opp := fun x => let '(x1, x2) := x in (-x1, -x2)%R |}.
Proof.
all:try solve_R.
* intros x y. cbn. split; intro Heq.
  + apply sqrt_eq_0 in Heq.
    - apply Rplus_eq_R0 in Heq; try apply Rle_0_sqr; [].
      destruct Heq as [Hx Hy].
      apply Rsqr_0_uniq, Rminus_diag_uniq in Hx.
      apply Rsqr_0_uniq, Rminus_diag_uniq in Hy.
      destruct x, y; simpl in *; subst; reflexivity.
    - replace 0%R with (0 + 0)%R by ring. apply Rplus_le_compat; apply Rle_0_sqr.
  + subst. do 2 rewrite (Rminus_diag_eq _ _ (reflexivity _)). rewrite Rsqr_0, Rplus_0_l. apply sqrt_0.
(* Version for squared distance 
* intros x y. cbn. split; intro Heq.
  + apply Rplus_eq_R0 in Heq; try apply Rle_0_sqr; [].
    destruct Heq as [Heq1 Heq2].
    apply Rsqr_0_uniq, Rminus_diag_uniq in Heq1.
    apply Rsqr_0_uniq, Rminus_diag_uniq in Heq2.
    destruct x, y; simpl in *; subst; reflexivity.
  + subst. do 2 rewrite (Rminus_diag_eq _ _ (reflexivity _)). now rewrite Rsqr_0, Rplus_0_l. *)
* intros. unfold dist. now setoid_rewrite R_sqr.Rsqr_neg_minus at 1 2.
* intros [? ?] [? ?] [? ?]. simpl. apply (Rgeom.triangle r r0 r3 r4 r1 r2).
* compute. injection. auto using R1_neq_R0.
Defined.

Delimit Scope R2_scope with R2.
Bind Scope R2_scope with R2.
Notation "u + v" := (add u v) : R2_scope.
Notation "k * u" := (mul k u) : R2_scope.
Notation "- u" := (opp u) : R2_scope.
Notation "u - v" := (add u (opp v)) : R2_scope.

Corollary square_dist_equiv : forall pt1 pt2 k, 0 <= k ->
  (dist pt1 pt2 = k <-> (dist pt1 pt2)² = k²).
Proof.
intros pt1 pt2 k Hk. split; intro Heq.
+ now rewrite Heq.
+ cbn in *. rewrite Rsqr_sqrt in Heq.
  - rewrite Heq. now rewrite sqrt_Rsqr.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma square_dist_simpl : forall pt1 pt2, (dist pt1 pt2)² = (fst pt1 - fst pt2)² + (snd pt1 - snd pt2)².
Proof.
intros pt1 pt2. cbn. rewrite Rsqr_sqrt; trivial.
replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma R2_dist_defined_2 : forall pt, dist pt pt = 0.
Proof.
  intros pt.
  rewrite dist_defined.
  reflexivity.
Qed.
Hint Resolve R2_dist_defined_2.

Lemma R2opp_dist : forall u v : R2, (dist (- u) (- v) = dist u v)%R2.
Proof.
intros [? ?] [? ?]. cbn. f_equal. cbn.
replace (- r - -r1) with (- (r - r1)) by ring.
replace (- r0 - - r2) with (- (r0 - r2)) by ring.
now do 2 rewrite <- R_sqr.Rsqr_neg.
Qed.

Lemma R2add_dist : forall w u v, (dist (u + w) (v + w) = dist u v)%R2.
Proof.
intros [? ?] [? ?] [? ?]. cbn. f_equal. cbn.
replace (r1 + r - (r3 + r)) with (r1 - r3) by ring.
replace (r2 + r0 - (r4 + r0)) with (r2 - r4) by ring.
reflexivity.
Qed.

Lemma R2mul_dist : forall k u v, dist (k * u)%R2 (k * v)%R2 = Rabs k * dist u v.
Proof.
intros k [? ?] [? ?]. cbn.
apply pos_Rsqr_eq.
- apply sqrt_pos.
- apply Rmult_le_pos; apply Rabs_pos || apply sqrt_pos.
- rewrite Rsqr_sqrt.
  + rewrite R_sqr.Rsqr_mult. rewrite Rsqr_sqrt.
    * repeat rewrite ?R_sqr.Rsqr_mult, ?R_sqr.Rsqr_plus, ?R_sqr.Rsqr_minus, <- ?R_sqr.Rsqr_abs. unfold Rsqr. lra.
    * replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
  + replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma R2dist_subadditive : forall u u' v v', dist (u + v)%R2 (u' + v')%R2 <= dist u u' + dist v v'.
Proof.
intros. etransitivity. apply (triang_ineq _ (u' + v)%R2).
rewrite R2add_dist. setoid_rewrite add_comm. rewrite R2add_dist. reflexivity.
Qed.

Lemma R2dist_ref_0 : forall u v, dist u v = dist (u - v)%R2 origin.
Proof. intros u v. now rewrite <- (R2add_dist (-v)), add_opp. Qed.

Lemma R2sub_origin : forall u v, (u - v)%R2 == origin <-> u == v.
Proof.
intros u v. split; intro Heq.
- now rewrite <- dist_defined, <- (R2add_dist (- v)), add_opp, dist_defined.
- now rewrite Heq, add_opp.
Qed.

(** **  Simplification tactics  **)

Transparent origin dist.
(*
Ltac unfoldR2 := unfold origin, equiv_dec, equiv, dist; cbn.

Tactic Notation "unfoldR2" "in" ident(H) :=
  unfold origin, R2def.origin, equiv_dec, equiv, R2def.eq, dist, R2def.dist in H.
*)
(** Small decision tactics for vectors simplifying v = v and v <> v. *)
Ltac R2dec := repeat
  match goal with
    | |- context[@equiv_dec _ _ R2_EqDec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (@equiv_dec _ _ R2_EqDec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ?x <> ?x |- _ => elim H; reflexivity
    | H : ?x =/= ?x |- _ => elim H; reflexivity
    | Heq : ?x == ?y, Hneq : ~?y == ?x |- _ => symmetry in Heq; contradiction
    | Heq : ?x == ?y, Hneq : ~?x == ?y |- _ => contradiction
    | Heq : ?x == ?y |- context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
        destruct (x =?= y); try contradiction; []
    | Heq : ?x =/= ?y |- context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
        destruct (x =?= y); try contradiction; []
    | Heq : ?y == ?x |- context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
        symmetry in Heq; destruct (x =?= y); try contradiction; []
    | Heq : ?y =/= ?x |- context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
        let HH := fresh in destruct (x =?= y) as [HH | ?]; try symmetry in HH; try contradiction; []
  end.

Ltac R2dec_full :=
  match goal with
    | |- context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (equiv_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac R2dec_full_in H :=
  match type of H with
    | context[@equiv_dec _ _ R2_EqDec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (equiv_dec x y) as [Heq | Hneq]
    | _ => fail
  end.
Tactic Notation "R2dec_full" "in" ident(H) := R2dec_full_in H.

Ltac normalize_R2dist pt1 pt2 pt3 :=
  repeat rewrite ?Rdec_bool_false_iff, ?Rdec_bool_true_iff in *;
  repeat match goal with
    | H : context[dist pt2 pt1] |- _ => rewrite (dist_sym pt1 pt2) in H
    | H : context[dist pt3 pt1] |- _ => rewrite (dist_sym pt1 pt3) in H
    | H : context[dist pt3 pt2] |- _ => rewrite (dist_sym pt2 pt3) in H
    | |- context[dist pt2 pt1] => rewrite (dist_sym pt1 pt2)
    | |- context[dist pt3 pt1] => rewrite (dist_sym pt1 pt3)
    | |- context[dist pt3 pt2] => rewrite (dist_sym pt2 pt3)
    | H : ~( _ <= _) |- _ => apply Rnot_le_lt in H
  end.

Ltac null x :=
  let Hnull := fresh "Hnull" in
  destruct (equiv_dec x origin) as [Hnull | Hnull]; [rewrite Hnull in * | change (~x == origin) in Hnull].


Definition R2dec_bool (x y : R2) := if equiv_dec x y then true else false.

Lemma R2dec_bool_true_iff (x y : R2) : R2dec_bool x y = true <-> x == y.
Proof. unfold R2dec_bool. destruct (equiv_dec x y); split; discriminate || auto. Qed.

Lemma R2dec_bool_false_iff (x y : R2) : R2dec_bool x y = false <-> x =/= y.
Proof.
unfold R2dec_bool.
destruct (equiv_dec x y); split; discriminate || auto.
intros abs. rewrite e in abs. now elim abs.
Qed.


(** **  Poor man's formalization of euclidean spaces  **)

(* FIXME: we should instead have a proper formalisation of euclidean spaces! *)
Definition product (u v : R2) := fst u * fst v + snd u * snd v.
Definition R2norm u := sqrt (product u u).
Definition orthogonal (u : R2) : R2 := /(R2norm u) * (snd u, - fst u).
Definition unitary u := (/(R2norm u) * u)%R2.
Definition perpendicular u v := product u v = 0.
Definition colinear (u v : R2) := perpendicular u (orthogonal v).


(* Compatibilities *)
Instance product_compat : Proper (equiv ==> equiv ==> eq) product.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

Instance R2norm_compat : Proper (equiv ==> eq) R2norm.
Proof. intros u v Heq. now rewrite Heq. Qed.

Instance orthogonal_compat : Proper (equiv ==> equiv) orthogonal.
Proof. intros u v Heq. now rewrite Heq. Qed.

(* could be strengthen with [colinear] (up to sign) *)
Instance unitary_compat : Proper (equiv ==> equiv) unitary.
Proof. intros u v Heq. unfold unitary. now rewrite Heq. Qed.

Instance perpendicular_compat : Proper (equiv ==> equiv ==> iff) perpendicular.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

Instance colinear_compat : Proper (equiv ==> equiv ==> iff) colinear.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

(** *** Results about [product]  **)

Lemma product_origin_l : forall u, product origin u = 0.
Proof. intros [x y]. unfold product; simpl. field. Qed.

Lemma product_origin_r : forall u, product u origin = 0.
Proof. intros [x y]. unfold product; simpl. field. Qed.

Lemma product_comm : forall u v, product u v = product v u.
Proof. intros [x1 y1] [x2 y2]. unfold product. field. Qed.

Lemma product_opp_l : forall u v, product (- u) v = - product u v.
Proof. intros [x1 y1] [x2 y2]. unfold product; simpl. field. Qed.

Lemma product_opp_r : forall u v, product u (- v) = - product u v.
Proof. intros [x1 y1] [x2 y2]. unfold product; simpl. field. Qed.

Lemma product_opp : forall u v, product (- u) (- v) = product u v.
Proof. intros [x1 y1] [x2 y2]. unfold product; simpl. field. Qed.

Lemma product_mul_l : forall k u v, product (k * u) v = k * product u v.
Proof. intros k [x1 y1] [x2 y2]. unfold product; simpl. field. Qed.

Lemma product_mul_r : forall k u v, product u (k * v) = k * product u v.
Proof. intros k [x1 y1] [x2 y2]. unfold product; simpl. field. Qed.

Lemma product_add_l : forall w u v, product (u + w) v = product u v + product w v.
Proof. intros [] [] [] *. unfold product. simpl. field. Qed.

Lemma product_add_r : forall w u v, product u (v + w) = product u v + product u w.
Proof. intros [] [] [] *. unfold product. simpl. field. Qed.

Lemma product_self_pos : forall u, 0 <= product u u.
Proof.
intros [x y]. unfold product; simpl. replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

(** ***  Results about [R2norm]  **)

Lemma R2norm_dist : forall u v, dist u v = R2norm (u - v)%R2.
Proof. intros [x1 y1] [x2 y2]. cbn. unfold R2norm. reflexivity. Qed.

Lemma R2norm_0 : forall u, R2norm u = 0 <-> u == origin.
Proof.
intros [x y]. unfold R2norm. simpl. split; intro Heq.
+ apply sqrt_eq_0 in Heq.
  - apply Rplus_eq_R0 in Heq; try apply Rle_0_sqr; []. simpl in *.
    destruct Heq as [Heqx Heqy]. apply Rsqr_0_uniq in Heqx. apply Rsqr_0_uniq in Heqy. now subst.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
+ unfold product. inversion Heq. simpl. ring_simplify (0 * 0 + 0 * 0). apply sqrt_0.
Qed.

Lemma R2norm_pos : forall u, 0 <= R2norm u.
Proof. intro. unfold R2norm. apply sqrt_pos. Qed.

Lemma R2norm_add : forall u v, (R2norm (u + v))² = (R2norm u)² + 2 * product u v + (R2norm v)².
Proof.
intros u v. unfold R2norm.
repeat rewrite Rsqr_sqrt; try apply product_self_pos; [].
rewrite product_add_l, product_add_r, product_add_r. rewrite (product_comm v u). ring.
Qed.

Lemma R2norm_sub : forall u v, (R2norm (u - v))² = (R2norm u)² - 2 * product u v + (R2norm v)².
Proof.
intros u v. unfold R2norm.
repeat rewrite Rsqr_sqrt; try apply product_self_pos; [].
rewrite product_add_l, product_add_r, product_add_r.
repeat rewrite product_opp_l, product_opp_r. rewrite (product_comm v u). ring.
Qed.

Lemma R2norm_mul : forall k u, R2norm (k * u) = Rabs k * R2norm u.
Proof.
intros k u. unfold R2norm. rewrite product_mul_l, product_mul_r, <- Rmult_assoc.
change (k * k) with k². rewrite sqrt_mult.
- now rewrite sqrt_Rsqr_abs.
- apply Rle_0_sqr.
- apply product_self_pos.
Qed.

Lemma R2norm_opp : forall u, R2norm (- u) = R2norm u.
Proof.
intro u. replace (- u)%R2 with ((-1) * u)%R2.
- rewrite R2norm_mul. rewrite Rabs_Ropp, Rabs_R1. ring.
- now rewrite minus_morph, mul_1.
Qed.

Lemma square_R2norm_equiv : forall u k, 0 <= k -> (R2norm u = k <-> (R2norm u)² = k²).
Proof. intros u k Hk. split; intro Heq; try congruence; []. apply pos_Rsqr_eq; trivial. apply R2norm_pos. Qed.

Corollary squared_R2norm : forall u v, R2norm u = R2norm v <-> (R2norm u)² = (R2norm v)².
Proof. intros u v. apply square_R2norm_equiv. apply R2norm_pos. Qed.

Lemma squared_R2norm_product : forall u, (R2norm u)² = product u u.
Proof. intro. unfold R2norm. rewrite Rsqr_sqrt; trivial. apply product_self_pos. Qed.

Lemma R2norm_origin : R2norm origin = 0.
Proof. rewrite square_R2norm_equiv, squared_R2norm_product; try reflexivity; []. compute. field. Qed.

(** ***  Results about [orthogonal]  **)

Lemma orthogonal_perpendicular : forall u, perpendicular u (orthogonal u).
Proof.
intro u. destruct (equiv_dec u origin) as [Hnull | Hnull].
- unfold perpendicular. now rewrite Hnull, product_origin_l.
- destruct u as [x y]. unfold perpendicular, orthogonal, product. simpl. field. now rewrite R2norm_0.
Qed.

Lemma orthogonal_origin : orthogonal origin == origin.
Proof. unfold orthogonal. simpl. now rewrite Ropp_0, Rmult_0_r. Qed.

Lemma orthogonal_origin_iff : forall u, orthogonal u == origin <-> u == origin.
Proof.
intro u. null u.
+ split; now auto using orthogonal_origin.
+ split; intro Heq.
  - destruct u as [x y]. unfold orthogonal in Heq.
    rewrite <- R2norm_0 in Hnull. injection Heq; intros Heqx Heqy.
    apply Rinv_neq_0_compat in Hnull. apply Rmult_integral in Heqx. apply Rmult_integral in Heqy.
    destruct Heqx, Heqy; try contradiction; []. cbn. f_equal; lra.
  - rewrite Heq. apply orthogonal_origin.
Qed.

Lemma R2norm_orthogonal : forall u, ~u == origin -> R2norm (orthogonal u) = 1.
Proof.
intros u Hnull. rewrite <- R2norm_0 in Hnull. unfold orthogonal. rewrite R2norm_mul. rewrite Rabs_pos_eq.
- unfold R2norm in *. destruct u. unfold product in *. simpl in *.
  replace (r0 * r0 + - r * - r) with (r * r + r0 * r0) by ring. now apply Rinv_l.
- apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply R2norm_pos.
Qed.

Lemma orthogonal_opp : forall u, orthogonal (- u)%R2 == (- orthogonal u)%R2.
Proof.
intro u. null u.
- now rewrite opp_origin, orthogonal_origin, opp_origin.
- destruct u as [? ?]. unfold orthogonal. rewrite R2norm_opp. cbn. hnf. now f_equal; field; rewrite R2norm_0.
Qed.

(* False in general because k may change the direction (but not the orientation) of u *)
Lemma orthogonal_mul : forall k u, 0 < k -> orthogonal (k * u) == orthogonal u.
Proof.
intros k u Hk. null u.
- now rewrite mul_origin, orthogonal_origin.
- rewrite <- R2norm_0 in Hnull. unfold orthogonal.
  rewrite R2norm_mul, Rabs_pos_eq; try (now apply Rlt_le); [].
  destruct u. simpl. hnf. f_equal; field; split; auto with real.
Qed.

(** ***  Results about [unitary]  **)

Lemma R2norm_unitary : forall u, ~equiv u origin -> R2norm (unitary u) = 1.
Proof.
intros u Hnull.
assert (R2norm u <> 0). { now rewrite R2norm_0. }
unfold unitary. rewrite R2norm_mul, Rabs_pos_eq.
- now apply Rinv_l.
- apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply R2norm_pos.
Qed.

Lemma unitary_origin : unitary origin == origin.
Proof. unfold unitary. apply mul_origin. Qed.

Lemma unitary_is_origin : forall u, equiv (unitary u) origin <-> equiv u origin.
Proof.
intro u. split; intro Heq.
- null u; try reflexivity; [].
  apply R2norm_unitary in Hnull. rewrite Heq, R2norm_origin in Hnull.
  exfalso. now apply R1_neq_R0.
- now rewrite Heq, unitary_origin.
Qed.

Lemma unitary_opp : forall u, unitary (-u)%R2 == (-unitary u)%R2.
Proof. intro u. unfold unitary. now rewrite R2norm_opp, mul_opp. Qed.

Lemma unitary_mul : forall k u, 0 < k -> unitary (k * u) == unitary u.
Proof.
intros k u Hk.
null u.
- now rewrite mul_origin.
- unfold unitary. rewrite R2norm_mul. rewrite Rabs_pos_eq; try lra; [].
  rewrite mul_morph. replace (/ (k * R2norm u) * k) with (/R2norm u); try reflexivity; [].
  field. rewrite R2norm_0. split; auto with real.
Qed.

Lemma unitary_id : forall u, u == ((R2norm u) * unitary u)%R2.
Proof.
intro u. unfold unitary. rewrite mul_morph.
destruct (equiv_dec u origin) as [Hnull | Hnull].
- rewrite Hnull. now rewrite mul_origin.
- rewrite Rinv_r, mul_1; try easy; []. now rewrite R2norm_0.
Qed.

Lemma unitary_idempotent : forall u, unitary (unitary u) == unitary u.
Proof.
intro u. destruct (equiv_dec u origin) as [Hnull | Hnull].
- rewrite Hnull. now rewrite unitary_origin at 1.
- unfold unitary at 1. rewrite R2norm_unitary; trivial; []. replace (/1) with 1 by field. apply mul_1.
Qed.

Lemma unitary_product : forall u v, product u v = R2norm u * R2norm v * product (unitary u) (unitary v).
Proof. intros. setoid_rewrite unitary_id at 1 2. rewrite product_mul_l, product_mul_r. field. Qed.

Lemma unitary_orthogonal : forall u, unitary (orthogonal u) == orthogonal u.
Proof.
intro u. destruct (equiv_dec u origin) as [Hnull | Hnull].
- rewrite Hnull. rewrite orthogonal_origin. apply unitary_origin.
- unfold unitary. rewrite R2norm_orthogonal; trivial; []. replace (/1) with 1 by field. now rewrite mul_1.
Qed.

Lemma orthogonal_unitary : forall u, orthogonal (unitary u) == orthogonal u.
Proof.
intro u. null u.
- now rewrite unitary_origin.
- unfold orthogonal. rewrite R2norm_unitary; trivial; []. unfold unitary. simpl.
  rewrite <- R2norm_0 in Hnull. now destruct u; f_equal; simpl; field.
Qed.

(** ***  Results about [perpendicular]  **)

Lemma perpendicular_sym : forall u v, perpendicular u v <-> perpendicular v u.
Proof. intros. unfold perpendicular. now rewrite product_comm. Qed.

Lemma perpendicular_origin_l : forall u, perpendicular origin u.
Proof. intros [? ?]; compute. field. Qed.

Lemma perpendicular_origin_r : forall u, perpendicular u origin.
Proof. intros [? ?]; compute. field. Qed.

Lemma perpendicular_opp_compat_l : forall u v, perpendicular (- u) v <-> perpendicular u v.
Proof.
intros u v. unfold perpendicular. split; intro Hperp.
- rewrite <- mul_1, mul_opp, <- minus_morph, product_mul_l in Hperp. lra.
- rewrite <- mul_1, mul_opp, <- minus_morph, product_mul_l, Hperp. field.
Qed.

Lemma perpendicular_opp_compat_r : forall u v, perpendicular u (- v) <-> perpendicular u v.
Proof.
intros u v. unfold perpendicular. split; intro Hperp.
- setoid_rewrite <- mul_1 in Hperp at 2. rewrite mul_opp, <- minus_morph, product_mul_r in Hperp. lra.
- setoid_rewrite <- mul_1 at 2. rewrite mul_opp, <- minus_morph, product_mul_r, Hperp. field.
Qed.

Lemma perpendicular_mul_compat_l : forall k u v, perpendicular u v -> perpendicular (k * u) v.
Proof. intros k u v Hperp. unfold perpendicular. rewrite product_mul_l, Hperp. field. Qed.

Lemma perpendicular_mul_compat_r : forall k u v, perpendicular u v -> perpendicular u (k * v).
Proof. intros k u v Hperp. unfold perpendicular. rewrite product_mul_r, Hperp. field. Qed.

Lemma perpendicular_mul_compat_l_iff : forall k u v, k <> 0 -> (perpendicular (k * u) v <-> perpendicular u v).
Proof.
intros k u v Hk. split; intro Hperp.
- rewrite <- mul_1. rewrite <- (Rinv_l k); trivial; []. rewrite <- mul_morph.
  now apply perpendicular_mul_compat_l.
- now apply perpendicular_mul_compat_l.
Qed.

Lemma perpendicular_mul_compat_r_iff : forall k u v, k <> 0 -> (perpendicular u (k * v) <-> perpendicular u v).
Proof.
intros k u v Hk. split; intro Hperp.
- rewrite <- (mul_1 v). rewrite <- (Rinv_l k); trivial; []. rewrite <- mul_morph.
  now apply perpendicular_mul_compat_r.
- now apply perpendicular_mul_compat_r.
Qed.

Lemma perpendicular_orthogonal_compat : forall u v,
  perpendicular (orthogonal u) (orthogonal v) <-> perpendicular u v.
Proof.
intros u v. split; intro Hperp.
+ null u; [| null v].
  - apply perpendicular_origin_l.
  - apply perpendicular_origin_r.
  - destruct u, v. unfold perpendicular, orthogonal, product in *. simpl in Hperp |- *.
    replace (/ R2norm (r, r0) * r0 * (/ R2norm (r1, r2) * r2) + / R2norm (r, r0) * - r * (/ R2norm (r1, r2) * - r1))
      with (/ R2norm (r, r0) * (/ R2norm (r1, r2) * (r * r1 + r0 * r2))) in Hperp by ring.
    rewrite <- R2norm_0 in Hnull, Hnull0.
    apply Rinv_neq_0_compat in Hnull. apply Rinv_neq_0_compat in Hnull0.
    apply Rmult_eq_reg_l with (/ R2norm (r1, r2)); trivial.
    apply Rmult_eq_reg_l with (/ R2norm (r, r0)); trivial.
    rewrite Hperp. lra.
+ destruct u, v. unfold perpendicular, orthogonal, product in *. simpl in *.
  replace (/ R2norm (r, r0) * r0 * (/ R2norm (r1, r2) * r2) + / R2norm (r, r0) * - r * (/ R2norm (r1, r2) * - r1))
    with (/ R2norm (r, r0) * (/ R2norm (r1, r2) * (r * r1 + r0 * r2))) by ring. rewrite Hperp. ring.
Qed.

Lemma perpendicular_unitary_compat_l : forall u v, perpendicular (unitary u) v <-> perpendicular u v.
Proof.
intros u v. null u.
+ now rewrite unitary_origin.
+ unfold perpendicular, unitary. rewrite product_mul_l.
  rewrite <- R2norm_0 in Hnull. apply Rinv_neq_0_compat in Hnull.
  split; intro Hperp.
  - apply Rmult_integral in Hperp. destruct Hperp; lra.
  - rewrite Hperp. lra.
Qed.

Lemma perpendicular_unitary_compat_r : forall u v, perpendicular u (unitary v) <-> perpendicular u v.
Proof.
intros u v. null v.
+ now rewrite unitary_origin.
+ unfold perpendicular, unitary. rewrite product_mul_r.
  rewrite <- R2norm_0 in Hnull. apply Rinv_neq_0_compat in Hnull.
  split; intro Hperp.
  - apply Rmult_integral in Hperp. destruct Hperp; lra.
  - rewrite Hperp. lra.
Qed.

Lemma unitary_orthogonal_perpendicular : forall u, perpendicular (unitary u) (orthogonal u).
Proof. intro. rewrite perpendicular_unitary_compat_l. apply orthogonal_perpendicular. Qed.

Lemma perpendicular_orthogonal_shift : forall u v,
  perpendicular (orthogonal u) v <-> perpendicular u (orthogonal v).
Proof.
intros u v. null u; [| null v].
+ rewrite orthogonal_origin. split; intros _; apply perpendicular_origin_l.
+ rewrite orthogonal_origin. split; intros _; apply perpendicular_origin_r.
+ unfold perpendicular, orthogonal, product. cbn.
  replace (/ R2norm u * snd u * fst v + / R2norm u * - fst u * snd v)
    with (- / R2norm u * (fst u * snd v - snd u * fst v)) by ring.
  replace (fst u * (/ R2norm v * snd v) + snd u * (/ R2norm v * - fst v))
    with (/ R2norm v * ((fst u * snd v) - snd u * fst v)) by ring.
  rewrite <- R2norm_0 in Hnull, Hnull0. apply Rinv_neq_0_compat in Hnull. apply Rinv_neq_0_compat in Hnull0.
  split; intro Heq;
  assert (Heq0 : fst u * snd v - snd u * fst v = 0) by (eapply Rmult_eq_reg_l; try rewrite Heq; lra);
  rewrite Heq0; lra.
Qed.

Lemma perpendicular_twice_colinear : forall u v w, ~equiv v origin ->
  perpendicular u v -> perpendicular v w -> colinear u w.
Proof.
intros u v w Hv Huv Hvw.
null u; [| null w].
+ apply perpendicular_origin_l.
+ unfold colinear. rewrite orthogonal_origin. apply perpendicular_origin_r.
+ unfold colinear, perpendicular, orthogonal, product in *. simpl.
  replace (fst u * (/ R2norm w * snd w) + snd u * (/ R2norm w * - fst w))
    with (/ R2norm w * (fst u * snd w + snd u * - fst w)) by ring.
  erewrite <- Rmult_0_r. apply Rmult_eq_compat_l.
  destruct (Req_dec (fst u) 0) as [Heq_u | Heq_u].
  - assert (snd u <> 0). { intro Heq. apply Hnull. destruct u. simpl in *. now subst. }
    rewrite Heq_u in *. ring_simplify in Huv. ring_simplify.
    assert (Heq_v : snd v = 0). { apply Rmult_integral in Huv. now destruct Huv. }
    assert (Heq_v' : fst v <> 0). { intro Heq. apply Hv. destruct v. simpl in *. now subst. }
    rewrite Heq_v in *. ring_simplify in Hvw.
    erewrite <- Rmult_0_r. apply Rmult_eq_compat_l.
    apply Rmult_integral in Hvw. now destruct Hvw.
  - apply (f_equal (Rmult (fst u))) in Hvw. rewrite Rmult_plus_distr_l, <- Rmult_assoc in Hvw.
    assert (Huv' : fst u * fst v = - snd u * snd v) by lra.
    rewrite Huv' in Hvw.
    assert (snd v <> 0).
    { intro Heq. apply Hv. destruct v as [x y]. simpl in *. subst. cut (x = 0); try (now intro; subst); [].
      ring_simplify in Huv'. apply Rmult_integral in Huv'. lra. }
    apply Rmult_eq_reg_l with (snd v); trivial. lra.
Qed.

Lemma perpendicular_dec : forall u v, {perpendicular u v} + {~perpendicular u v}.
Proof. intros u v. unfold perpendicular. apply Rdec. Defined.

(** ***  Results about [colinear]  **)

Lemma colinear_dec : forall u v, {colinear u v} + {~colinear u v}.
Proof. intros u v. unfold colinear. apply perpendicular_dec. Defined.

Instance colinear_Reflexive : Reflexive colinear.
Proof. intro. apply orthogonal_perpendicular. Qed.

Instance colinear_Symmetric : Symmetric colinear.
Proof. intros u v H. unfold colinear. now rewrite perpendicular_sym, perpendicular_orthogonal_shift. Qed.

Lemma colinear_trans : forall u v w, ~equiv v origin -> colinear u v -> colinear v w -> colinear u w.
Proof.
intros u v w Hv Huv Hvw. apply perpendicular_twice_colinear with (orthogonal v).
- now rewrite orthogonal_origin_iff.
- assumption.
- now rewrite perpendicular_orthogonal_shift.
Qed.

Lemma colinear_sym : forall u v, colinear u v <-> colinear v u.
Proof. intros. split; intros; now symmetry. Qed.

Lemma colinear_origin_l : forall u, colinear origin u.
Proof. intro u. unfold colinear. apply perpendicular_origin_l. Qed.

Lemma colinear_origin_r : forall u, colinear u origin.
Proof. intro u. unfold colinear. rewrite orthogonal_origin. apply perpendicular_origin_r. Qed.

Lemma colinear_opp_compat_l : forall u v, colinear (- u) v <-> colinear u v.
Proof. intros. unfold colinear. apply perpendicular_opp_compat_l. Qed.

Lemma colinear_orthogonal_shift : forall u v, colinear u (orthogonal v) <-> colinear (orthogonal u) v.
Proof. intros. unfold colinear. now rewrite perpendicular_orthogonal_shift. Qed.

Lemma colinear_opp_compat_r : forall u v, colinear u (- v) <-> colinear u v.
Proof.
intros. unfold colinear.
now rewrite <- perpendicular_orthogonal_shift, perpendicular_opp_compat_r, perpendicular_orthogonal_shift.
Qed.

Lemma colinear_mul_compat_l : forall k u v, colinear u v -> colinear (k * u) v.
Proof. intros. unfold colinear. now apply perpendicular_mul_compat_l. Qed.

Lemma colinear_mul_compat_r : forall k u v, colinear u v -> colinear u (k * v).
Proof.
intros. unfold colinear.
rewrite <- perpendicular_orthogonal_shift. apply perpendicular_mul_compat_r.
now rewrite perpendicular_orthogonal_shift.
Qed.

Lemma colinear_mul_compat_l_iff : forall k u v, k <> 0 -> (colinear (k * u) v <-> colinear u v).
Proof. intros. unfold colinear. now apply perpendicular_mul_compat_l_iff. Qed.

Lemma colinear_mul_compat_r_iff : forall k u v, k <> 0 -> (colinear u (k * v) <-> colinear u v).
Proof.
intros. unfold colinear.
now rewrite <- perpendicular_orthogonal_shift, perpendicular_mul_compat_r_iff, perpendicular_orthogonal_shift.
Qed.

Lemma colinear_orthogonal_compat : forall u v, colinear (orthogonal u) (orthogonal v) <-> colinear u v.
Proof. intros. unfold colinear. now rewrite perpendicular_orthogonal_compat. Qed.

Lemma colinear_add : forall u v, colinear u (u + v) <-> colinear u v.
Proof.
intros u v. unfold colinear at 1. rewrite <- perpendicular_orthogonal_shift.
unfold perpendicular. rewrite product_add_r. rewrite product_comm, orthogonal_perpendicular.
rewrite Rplus_0_l. rewrite product_comm. rewrite colinear_sym. reflexivity.
Qed.

(** Important theorems *)
Theorem Pythagoras : forall u v, perpendicular u v <-> (R2norm (u + v)%R2)² = (R2norm u)² + (R2norm v)².
Proof.
intros u v. split; intro Hperp.
- unfold R2norm.
  repeat rewrite Rsqr_sqrt; try apply product_self_pos; [].
  rewrite product_add_l, product_add_r, product_add_r.
  rewrite (product_comm v u), Hperp. ring.
- rewrite squared_R2norm_product in Hperp at 1.
  rewrite product_add_l, product_add_r, product_add_r in Hperp.
  setoid_rewrite product_comm in Hperp at 3.
  do 2 rewrite <- squared_R2norm_product in Hperp.
  unfold perpendicular. lra.
Qed.

(* Beurk! *)
Theorem decompose_on : forall u, ~equiv u origin -> forall v,
  (v = product v (unitary u) * unitary u + product v (orthogonal u) * orthogonal u)%R2.
Proof.
intros [x1 y1] Hnull [x2 y2]. unfold unitary, orthogonal, R2norm, product. simpl. f_equal.
+ ring_simplify. rewrite <- R2norm_0 in Hnull. unfold R2norm, product in Hnull. simpl in Hnull.
  replace (Rpow_def.pow (/ sqrt (x1 * x1 + y1 * y1)) 2) with (/ sqrt (x1 * x1 + y1 * y1))²
    by now unfold Rsqr; field.
  replace (Rpow_def.pow x1 2) with x1² by (unfold Rsqr; ring).
  replace (Rpow_def.pow y1 2) with y1² by (unfold Rsqr; ring).
  replace (x2 * (/ sqrt (x1 * x1 + y1 * y1))² * x1² + x2 * (/ sqrt (x1 * x1 + y1 * y1))² * y1²)
    with (x2 * (/ sqrt (x1 * x1 + y1 * y1))² * (x1² + y1²)) by ring.
  rewrite R_sqr.Rsqr_inv; trivial; [].
  rewrite Rsqr_sqrt.
  - unfold Rsqr. field. intro Habs. apply Hnull. rewrite Habs. apply sqrt_0.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
+ ring_simplify. rewrite <- R2norm_0 in Hnull. unfold R2norm, product in Hnull. simpl in Hnull.
  replace (Rpow_def.pow (/ sqrt (x1 * x1 + y1 * y1)) 2) with (/ sqrt (x1 * x1 + y1 * y1))²
    by now unfold Rsqr; field.
  replace (Rpow_def.pow x1 2) with x1² by (unfold Rsqr; ring).
  replace (Rpow_def.pow y1 2) with y1² by (unfold Rsqr; ring).
  replace (x2 * (/ sqrt (x1 * x1 + y1 * y1))² * x1² + x2 * (/ sqrt (x1 * x1 + y1 * y1))² * y1²)
    with (x2 * (/ sqrt (x1 * x1 + y1 * y1))² * (x1² + y1²)) by ring.
  rewrite R_sqr.Rsqr_inv; trivial; [].
  rewrite Rsqr_sqrt.
  - unfold Rsqr. field. intro Habs. apply Hnull. rewrite Habs. apply sqrt_0.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Corollary colinear_decompose : forall u, ~equiv u origin -> forall v,
  colinear u v -> equiv v (R2norm v * unitary u)%R2 \/ equiv v (- R2norm v * unitary u)%R2.
Proof.
intros u Hnull v Huv. rewrite (decompose_on Hnull v).
symmetry in Huv. rewrite Huv. rewrite mul_0, add_origin.
rewrite R2norm_mul. rewrite R2norm_unitary, Rmult_1_r; trivial.
destruct (Rle_dec 0 (product v (unitary u))) as [Hle | Hle].
- left. f_equal. now rewrite Rabs_pos_eq.
- right. f_equal. now rewrite Rabs_left, Ropp_involutive; auto with real.
Qed.

Lemma perpendicular_colinear_compat : forall u u' v v', ~equiv u origin -> ~equiv v origin ->
  colinear u u' -> colinear v v' -> perpendicular u v -> perpendicular u' v'.
Proof.
intros u u' v v' Hu Hv Hcol_u Hcol_v Hperp.
apply colinear_decompose in Hcol_u; trivial; [].
apply colinear_decompose in Hcol_v; trivial; [].
rewrite <- perpendicular_unitary_compat_l, <- perpendicular_unitary_compat_r in Hperp.
destruct Hcol_u as [Hcol_u | Hcol_u], Hcol_v as [Hcol_v | Hcol_v];
rewrite Hcol_u, Hcol_v; apply perpendicular_mul_compat_l, perpendicular_mul_compat_r; assumption.
Qed.

Lemma colinear_product_spec : forall u v, Rabs (product u v) = (R2norm u) * (R2norm v) <-> colinear u v.
Proof.
intros u v. split; intro Huv.
* apply (f_equal Rsqr) in Huv. rewrite <- R_sqr.Rsqr_abs in Huv.
  rewrite R_sqr.Rsqr_mult in Huv. do 2 rewrite squared_R2norm_product in Huv.
  null v; try apply colinear_origin_r; [].
  unfold colinear, orthogonal, perpendicular. rewrite product_mul_r. apply Rmult_eq_0_compat_l.
  unfold product in *. rewrite R_sqr.Rsqr_plus in Huv. do 2 rewrite R_sqr.Rsqr_mult in Huv.
  unfold Rsqr in Huv. simpl. ring_simplify. apply Rsqr_0_uniq.
  rewrite R_sqr.Rsqr_minus. unfold Rsqr. lra.
* null u.
  + rewrite product_origin_l. rewrite Rabs_R0, R2norm_origin. ring.
  + apply (colinear_decompose Hnull) in Huv.
    setoid_rewrite unitary_id at 1. rewrite product_mul_l.
    destruct Huv as [Huv | Huv]; rewrite Huv at 1.
    - rewrite product_mul_r. rewrite <- squared_R2norm_product, R2norm_unitary; trivial.
      rewrite R_sqr.Rsqr_1, Rmult_1_r. apply Rabs_pos_eq.
      replace 0 with (0 * 0) by ring. apply Rmult_le_compat; reflexivity || apply R2norm_pos.
    - rewrite product_mul_r. rewrite <- squared_R2norm_product, R2norm_unitary; trivial.
      rewrite R_sqr.Rsqr_1, Rmult_1_r.
      replace (R2norm u * - R2norm v) with (- (R2norm u * R2norm v)) by ring. rewrite Rabs_Ropp.
      apply Rabs_pos_eq.
      replace 0 with (0 * 0) by ring. apply Rmult_le_compat; reflexivity || apply R2norm_pos.
Qed.

Theorem triang_ineq_eq : forall u v w,
  dist u w = dist u v + dist v w -> colinear (w - u) (v - u) /\ colinear (w - u) (w - v).
Proof.
intros u v w Heq. null (w - u)%R2.
* split; apply colinear_origin_l.
* rewrite dist_sym, R2norm_dist in Heq.
  assert (Huw : (w - u =(w - v) + (v - u))%R2).
  { rewrite add_assoc. f_equal. rewrite <- add_assoc. setoid_rewrite add_comm at 2.
    rewrite add_opp. now rewrite add_origin. }
  rewrite Huw in Heq. apply (f_equal Rsqr) in Heq. rewrite squared_R2norm_product in Heq.
  rewrite product_add_l in Heq. setoid_rewrite product_add_r in Heq.
  do 2 rewrite <- squared_R2norm_product, <- R2norm_dist in Heq.
  rewrite R_sqr.Rsqr_plus in Heq. rewrite product_comm in Heq. setoid_rewrite dist_sym at 1 2 in Heq.
  assert (Heq' : product (v - u) (w - v) = dist u v * dist v w) by lra.
  apply (f_equal Rabs) in Heq'. setoid_rewrite Rabs_pos_eq at 2 in Heq'.
  + setoid_rewrite dist_sym in Heq'. setoid_rewrite R2norm_dist in Heq'.
    rewrite colinear_product_spec in Heq'.
    split.
    - rewrite Huw. rewrite add_comm. rewrite colinear_sym. now rewrite colinear_add.
    - rewrite Huw. rewrite colinear_sym. now rewrite colinear_add.
  + replace 0 with (0 * 0) by ring. apply Rmult_le_compat; reflexivity || apply dist_pos.
Qed.

Theorem triang_ineq_eq3 : forall t u v w,
  dist t w = dist t u + dist u v + dist v w -> colinear (u - t) (v - t) /\ colinear (w - t) (u - t).
Proof.
intros t u v w Heq. null (u - t)%R2; [| null (v - t)%R2].
+ split; apply colinear_origin_l || apply colinear_origin_r.
+ split; try apply colinear_origin_r.
  rewrite R2sub_origin in Hnull0. rewrite <- Hnull0 in *.
  elim Hnull.
  rewrite R2sub_origin, <- dist_defined. apply Rmult_eq_reg_l with 2; try lra; [].
  ring_simplify. apply Rplus_eq_reg_r with (dist v w).
  rewrite Rplus_0_l. rewrite Heq at 2. setoid_rewrite dist_sym at 3. ring.
+ assert (Heq' : dist t v = dist t u + dist u v).
  { apply antisymmetry.
    - apply triang_ineq.
    - apply Rplus_le_reg_r with (dist v w). rewrite <- Heq. apply triang_ineq. }
  assert (Hcol := triang_ineq_eq _ _ _ Heq'). split; try (now symmetry); [].
  rewrite <- Heq' in Heq. apply triang_ineq_eq in Heq.
  destruct Heq. destruct Hcol. now apply colinear_trans with (v - t)%R2.
Qed.

(* A very ugly proof! *)
Lemma segment_bisector_spec : forall pt1 pt2 pt, ~equiv pt1 pt2 ->
  dist pt1 pt = dist pt pt2 <-> exists k, equiv pt (middle pt1 pt2 + k * orthogonal (pt2 - pt1))%R2.
Proof.
intros pt1 pt2 pt Hnull. split; intro Hpt.
+ pose (ptx := (pt - pt1)%R2).
  exists (product ptx (orthogonal (pt2 - pt1))).
  assert (Hneq : ~(pt2 - pt1)%R2 == origin).
  { intro Habs. apply Hnull. destruct pt1, pt2; simpl in *. injection Habs; intros; hnf; f_equal; lra. }
  rewrite add_comm. rewrite <- dist_defined. rewrite <- (R2add_dist (- pt1)). fold ptx.
  rewrite <- add_assoc. replace (middle pt1 pt2 - pt1)%R2 with (1/2 * (pt2 - pt1))%R2
    by (destruct pt1, pt2; simpl; f_equal; field). pose (u := (pt2 - pt1)%R2). fold u in Hneq |- *.
  rewrite (decompose_on Hneq ptx) at 1.
  rewrite R2norm_dist. unfold R2norm. rewrite <- sqrt_0. f_equal.
  repeat rewrite ?product_add_l, ?product_add_r, ?product_opp_l, ?product_opp_r, ?product_mul_l, ?product_mul_r.
  ring_simplify.
  rewrite (unitary_id u) at 6 8. rewrite ?product_mul_l, ?product_mul_r.
  assert (Heq : product (unitary u) (unitary u) = 1).
  { rewrite <- R_sqr.Rsqr_1. rewrite <- (R2norm_unitary Hneq). unfold R2norm.
    rewrite Rsqr_sqrt; trivial. apply product_self_pos. }
  rewrite Heq. clear Heq. repeat rewrite Rmult_1_r.
  assert (Heq : product u u = (R2norm u)²).
  { unfold R2norm. rewrite Rsqr_sqrt; trivial. apply product_self_pos. }
    rewrite Heq. clear Heq.
  (* Let us now use the assumption about pt. *)
  setoid_rewrite <- (R2add_dist (- pt1)) at 2 in Hpt. rewrite dist_sym in Hpt.
  do 2 rewrite R2norm_dist in Hpt. fold u ptx in Hpt.
  assert (Hsquare : (R2norm ptx)² = (R2norm (ptx - u))²) by now rewrite Hpt.
  rewrite R2norm_sub in Hsquare. rewrite <- R2norm_0 in Hneq.
  assert (Heq : R2norm u = 2 * product ptx (unitary u)).
  { unfold unitary. rewrite product_mul_r. apply Rmult_eq_reg_l with (R2norm u); trivial; [].
    change (R2norm u * R2norm u) with (R2norm u)². field_simplify; trivial; []. lra. }
  rewrite Heq. unfold Rsqr. field.
+ destruct Hpt as [k Hpt]. rewrite Hpt. unfold middle. do 2 rewrite R2norm_dist.
  rewrite opp_distr_add. rewrite <- (add_comm (-pt2))%R2. repeat rewrite add_assoc.
  replace (pt1 - (1 / 2 * (pt1 + pt2)))%R2 with (- (/2 * (pt2 - pt1)))%R2
    by (destruct pt1, pt2; simpl; f_equal; field).
  replace (- pt2 + 1 / 2 * (pt1 + pt2))%R2 with (- (/2 * (pt2 - pt1)))%R2
    by (destruct pt1, pt2; simpl; f_equal; field).
  assert (Hperp : perpendicular (- (/2 * (pt2 - pt1)))%R2 (k * orthogonal (pt2 - pt1))%R2)
    by apply perpendicular_opp_compat_l, perpendicular_mul_compat_l,
             perpendicular_mul_compat_r, orthogonal_perpendicular.
  rewrite squared_R2norm. rewrite Pythagoras in Hperp. rewrite Hperp.
  setoid_rewrite <- R2norm_opp at 3. rewrite <- Pythagoras.
  apply perpendicular_opp_compat_l, perpendicular_opp_compat_r,
        perpendicular_mul_compat_l, perpendicular_mul_compat_r, orthogonal_perpendicular.
Qed.

(** ** Segments **)

Lemma Rplus_reg_r : forall r1 r2 r3, r1 = r3 + - r2 -> r1 + r2 = r3.
Proof.
  intros. subst. rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r. reflexivity.
Qed.

Lemma Rplus_reg_l : forall r1 r2 r3, r2 = r3 + -r1 -> r1 + r2 = r3.
Proof.
  intros. subst. rewrite Rplus_comm, Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r. reflexivity.
Qed.

Lemma Rplus_opp_r_rwrt : forall r1 r2,  r1 + - r2 = 0 -> r1 = r2.
Proof.
intros. apply Rplus_opp_r_uniq in H. apply Ropp_eq_compat in H.
repeat rewrite Ropp_involutive in H. subst. reflexivity.
Qed.

Lemma Rmult_inv_reg_r : forall r1 r2 r3, r2 <> 0 -> r1 = r3 * r2 -> r1 * / r2 = r3.
Proof. intros. subst. now apply Rinv_r_simpl_l. Qed.

Lemma R2plus_opp_assoc_comm : forall u1 u2 u3, (u1 + u2 + - u3 = u1 + - u3 + u2)%R2.
Proof. intros. now rewrite <- add_assoc, (add_comm u2), add_assoc. Qed.

Lemma R2_opp_dist : forall u v, (- (u + v) = -u + -v)%R2.
Proof. intros [? ?] [? ?]. compute. f_equal; ring. Qed.

Lemma orthogonal_projection_aux :
  forall ptA ptB ptS, ~ptA == ptB ->
                      exists kH, perpendicular (ptB - ptA) (ptA - ptS + kH * (ptB - ptA))%R2.
Proof.
  intros A B S Hineq.
  destruct A as (xA, yA).
  destruct B as (xB, yB).
  destruct S as (xS, yS).
  unfold perpendicular, product.
  simpl.
  set (xAB := xB + - xA).
  set (yAB := yB + - yA).
  set (xSA := xA + - xS).
  set (ySA := yA + - yS).

  exists ( - (xAB * xSA + yAB * ySA) * / (xAB * xAB + yAB * yAB) ).

  rewrite Rmult_plus_distr_l.
  rewrite Rplus_assoc.
  apply Rplus_reg_l.
  rewrite Rplus_0_l.
  rewrite Rplus_comm.
  rewrite Rmult_plus_distr_l.
  rewrite Rplus_assoc.
  apply Rplus_reg_l.
  rewrite Rplus_comm.

  rewrite Rmult_comm with (r2 := xAB).
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite Rplus_comm.
  rewrite Rmult_comm with (r2 := yAB).
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_plus_distr_r.

  apply Rmult_inv_reg_r.

  + intro Hsqr_sum.
    destruct (Rplus_sqr_eq_0 _ _ Hsqr_sum) as (Hx, Hy).
    apply Hineq.
    simpl.
    rewrite (Rplus_opp_r_rwrt Hx).
    rewrite (Rplus_opp_r_rwrt Hy).
    reflexivity.

  + ring.

Qed.

Lemma orthogonal_projection :
  forall ptA ptB ptS, ~ptA == ptB ->
  exists kH, perpendicular (ptB - ptA) (ptA + kH * (ptB - ptA) - ptS)%R2.
Proof.
intros A B S Hineq.
destruct (orthogonal_projection_aux S Hineq) as (k, Hp).
exists k.
now rewrite R2plus_opp_assoc_comm.
Qed.

Lemma squared_R2norm_le : forall u v, (R2norm u)² <= (R2norm v)² <-> R2norm u <= R2norm v.
Proof. intros. apply pos_Rsqr_le; auto using R2norm_pos. Qed.

Definition on_segment (ptA ptB pt : R2) :=
  exists k, (pt - ptA)%R2 = (k * (ptB - ptA))%R2 /\ (0 <= k <= 1)%R.

Lemma inner_segment : forall ptA ptB ptS ptK,
  ~ ptA == ptB ->
  on_segment ptA ptB ptK ->
  dist ptS ptK <= dist ptS ptA \/ dist ptS ptK <= dist ptS ptB.
Proof.
intros A B S K Hneq Hseg.
destruct Hseg as (k, (Hcolinear, Hinside)).
destruct (orthogonal_projection S Hneq) as (kh, Hp).
set (H := (A + kh * (B - A))%R2).

assert (HperpA: perpendicular (A - H) (H - S)).
{ unfold H.
  replace (A - (A + kh * (B - A)))%R2 with (- kh * (B - A))%R2.
  auto using perpendicular_mul_compat_l.
  destruct A, B; compute; f_equal; ring. }
assert (HperpB: perpendicular (B - H) (H - S)).
{ unfold H.
  replace (B - (A + kh * (B - A)))%R2 with ((1 + - kh) * (B - A))%R2.
  auto using perpendicular_mul_compat_l.
  destruct A, B; compute; f_equal; ring. }
assert (HperpK: perpendicular (K - H) (H - S)).
{ replace ((K - H)%R2) with (((K - A) + (A - H))%R2).
  rewrite Hcolinear.
  unfold H.
  replace (A - (A + kh * (B - A)))%R2 with (-kh * (B - A))%R2.
  rewrite add_morph.
  auto using perpendicular_mul_compat_l.
  destruct A, B; compute; f_equal; ring.
  destruct K, A, H; compute; f_equal; ring. }
clear Hp.

assert (Kdef: K = (A + k * (B - A))%R2).
{ rewrite <- Hcolinear. destruct K, A; compute; f_equal; ring. }
clear Hcolinear.

destruct (Rlt_le_dec k kh) as [Hlt | Hle].
+ left.
  rewrite dist_sym, R2norm_dist, dist_sym, R2norm_dist.
  apply squared_R2norm_le.
  replace (K - S)%R2 with ((K - H) + (H - S))%R2.
  apply Pythagoras in HperpK. rewrite HperpK.
  replace (A - S)%R2 with ((A - H) + (H - S))%R2.
  apply Pythagoras in HperpA. rewrite HperpA.
  apply Rplus_le_compat_r.
  rewrite Kdef.
  unfold H.
  replace (A + k * (B - A) - (A + kh * (B - A)))%R2 with ((k - kh) * (B - A))%R2.
  replace (A - (A + kh * (B - A)))%R2 with (-kh * (B - A))%R2.

  apply squared_R2norm_le.
  repeat rewrite R2norm_mul.
  apply Rmult_le_compat_r.
  apply R2norm_pos.
  rewrite Rabs_Ropp, Rabs_minus_sym.
  repeat rewrite Rabs_pos_eq.
  apply Rplus_le_reg_pos_r with (r2 := k). tauto.
  right. ring.
  left. apply Rle_lt_trans with (r2 := k). tauto.
  assumption.
  left. apply Rlt_Rminus. assumption.

  destruct A, B; compute; f_equal; ring.
  destruct A, B; compute; f_equal; ring.
  destruct A, H, S; compute; f_equal; ring.
  destruct K, H, S; compute; f_equal; ring.

+ right.
  rewrite dist_sym, R2norm_dist, dist_sym, R2norm_dist.
  apply squared_R2norm_le.
  replace (K - S)%R2 with ((K - H) + (H - S))%R2.
  apply Pythagoras in HperpK. rewrite HperpK.
  replace (B - S)%R2 with ((B - H) + (H - S))%R2.
  apply Pythagoras in HperpB. rewrite HperpB.
  apply Rplus_le_compat_r.
  rewrite Kdef.
  unfold H.
  replace (A + k * (B - A) - (A + kh * (B - A)))%R2 with ((k - kh) * (B - A))%R2.
  replace (B - (A + kh * (B - A)))%R2 with ((1 - kh) * (B - A))%R2.

  apply squared_R2norm_le.
  repeat rewrite R2norm_mul.
  apply Rmult_le_compat_r.
  apply R2norm_pos.
  repeat rewrite Rabs_pos_eq.
  apply Rplus_le_compat_r. tauto.
  apply Rge_le.
  apply Rge_minus.
  apply Rle_ge.
  apply Rle_trans with (r2 := k). assumption. tauto.
  apply Rge_le.
  apply Rge_minus.
  apply Rle_ge.
  assumption.

  destruct A, B; compute; f_equal; ring.
  destruct A, B; compute; f_equal; ring.
  destruct B, H, S; compute; f_equal; ring.
  destruct K, H, S; compute; f_equal; ring.
Qed.

Lemma R2div_reg_l : forall k u v, k <> 0 -> (k * u = v)%R2 -> (u = /k * v)%R2.
Proof. intros k u v Hneqz Heq. subst. now rewrite mul_morph, Rinv_l, mul_1. Qed.

Lemma R2plus_compat_eq_r :
  forall u v w, (u = v)%R2 -> (u + w = v + w)%R2.
Proof. intros. subst. reflexivity. Qed.

Lemma distance_after_move
      (C P Q : R2) (kp kq dm : R)
      (HneqPC : ~ P == C) (HneqQC: ~ Q == C) (*(HneqPQ: ~R2.eq P Q)*)
      (HdistPC : dist P C <= dm) (*(HdistQC: dist Q C <= dm)*) (HdistPQ : dist P Q <= dm)
      (Hkp: 0 < kp) (Hkpkq : kp <= kq) (Hkq : kq <= 1) :
  dist (P + kp * (C - P))%R2 (Q + kq * (C - Q))%R2 <= (1 - kp) * dm.
Proof.
destruct (Req_dec kq 1).
+ subst kq.
  rewrite mul_1.
  assert (Heq : (Q + (C - Q) = C)%R2).
  { rewrite add_comm, <- add_assoc, (add_comm _ Q), add_opp.
    change eq with equiv. apply add_origin.
  }
  rewrite Heq, R2norm_dist.
  assert (Heq' : (P + kp * (C - P) - C = (- 1 + kp) * (C - P))%R2).
  { rewrite <- add_morph, minus_morph, mul_1, opp_distr_add, opp_opp.
    symmetry. now rewrite <- add_assoc, add_comm. }
  rewrite Heq', R2norm_mul, <- Rabs_Ropp.
  apply Rmult_le_compat.
  - apply Rabs_pos.
  - apply R2norm_pos.
  - right.
    rewrite Rabs_pos_eq.
    ring.
    rewrite Ropp_plus_distr, Ropp_involutive.
    apply Rplus_le_reg_r with (r := kp).
    now rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
  - now rewrite <- R2norm_dist, dist_sym.
+ destruct Hkq as [Hkq | Hkq]; [| exfalso; now apply H].
  clear H.

  set (KP := (P + kp * (C - P))%R2).
  set (KQ := (Q + kq * (C - Q))%R2).
  set (KQ' := (Q + kp * (C - Q))%R2).
  assert (Hpos: 0 < 1 - kp).
  { apply Rgt_lt.
    apply Rgt_minus.
    apply Rlt_gt.
    apply Rle_lt_trans with (r2 := kq); assumption.
  }
  assert (Hpoz: 0 <= 1 - kp).
  { left. assumption. }

  assert (Thales: dist KP KQ' <= (1 - kp) * dm).
  { rewrite R2norm_dist.
    unfold KP, KQ'.
    replace (P + kp * (C - P) - (Q + kp * (C - Q)))%R2 with ((1 - kp) * (P - Q))%R2.
    { rewrite R2norm_mul.
      rewrite (Rabs_pos_eq _ Hpoz).
      rewrite (Rmult_le_compat_l (1 - kp) (R2norm (P - Q)) dm Hpoz).
      right. reflexivity.
      rewrite <- R2norm_dist.
      assumption.
    }
    destruct P, Q, C; compute; f_equal; ring.
  }

  assert (Hseg: on_segment KQ' C KQ).
  { unfold on_segment.
    exists (/(1 - kp) * (kq - kp)).
    split.
    + rewrite <- mul_morph.
      apply R2div_reg_l.
      { apply Rgt_not_eq.
        apply Rlt_gt.
        assumption. }    
      unfold KQ, KQ'.
      destruct C, Q; compute; f_equal; ring.
    + split.
      - apply Rmult_le_reg_l with (r := 1 - kp).
        { assumption. }
        rewrite Rmult_0_r.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r.
        * rewrite Rmult_1_l. apply Rge_le. apply Rge_minus. apply Rle_ge.
          assumption.
        * apply Rgt_not_eq. apply Rlt_gt. assumption.
      - apply Rmult_le_reg_l with (r := 1 - kp).
        { assumption. }
        rewrite Rmult_1_r.
        rewrite <- Rmult_assoc.
        rewrite Rinv_r.
        * rewrite Rmult_1_l.
          apply Rplus_le_reg_l with (r := kp).
          repeat rewrite Rplus_minus.
          left. assumption.
        * apply Rgt_not_eq. apply Rlt_gt. assumption.
  }

  assert (HneqKQ'C: ~ KQ' == C).
  { unfold KQ'.
    intro Heq.
    apply R2plus_compat_eq_r with (w := (-Q)%R2) in Heq.
    replace (Q + kp * (C - Q) - Q)%R2 with (kp * (C - Q))%R2 in Heq;
      [ | destruct Q, C; compute; f_equal; ring].
    rewrite <- (mul_1 (C - Q)%R2) in Heq at 2.
    change eq with equiv in Heq.
    apply mul_reg_r in Heq.
    - subst.
      compute in Hpos. rewrite Rplus_opp_r in Hpos. apply (Rlt_irrefl _ Hpos).
    - intro Horigin.
      apply R2plus_compat_eq_r with (w := Q%R2) in Horigin.
      rewrite <- add_assoc in Horigin.
      rewrite add_comm with (u := (-Q)%R2) in Horigin.
      rewrite add_opp in Horigin.
      rewrite add_origin in Horigin.
      rewrite add_comm in Horigin.
      rewrite add_origin in Horigin.
      subst.
      now apply HneqQC. }

  destruct (inner_segment KP HneqKQ'C Hseg).
  - apply Rle_trans with (r2 := dist KP KQ'); assumption.
  - apply Rle_trans with (r2 := dist KP C); [ assumption | ].
    unfold KP. rewrite R2norm_dist.
    replace (P + kp * (C - P) - C)%R2 with ((1 - kp) * (P - C))%R2.
    rewrite R2norm_mul.
    rewrite Rabs_pos_eq.
    apply Rmult_le_compat_l.
    left; assumption.
    rewrite <- R2norm_dist.
    assumption.
    left; assumption.
    destruct P, C; compute; f_equal; ring.
Qed.

Lemma R2norm_ineq : forall u v, R2norm (u + v) <= R2norm u + R2norm v.
Proof.
intros u v.
replace (R2norm (u+v)) with (R2norm (u - -v)%R2).
replace (R2norm u) with (R2norm (u - origin)).
replace (R2norm v) with (R2norm (origin - - v)%R2).
- repeat rewrite <- R2norm_dist. apply triang_ineq.
- now rewrite add_comm, add_origin, opp_opp.
- now rewrite opp_origin, add_origin.
- now rewrite opp_opp.
Qed.

Lemma fold_add_ac : forall E a b, fold_left add E (a + b)%R2 = ((fold_left add E a) + b)%R2.
Proof.
induction E as [| x E].
+ reflexivity.
+ intros a b.
  cbn [fold_left].
  rewrite <- add_assoc, add_comm with (u := b), add_assoc.
  apply IHE.
Qed.

Lemma fold_add_permutation : forall l1 l2 a,
  PermutationA equiv l1 l2 ->
  fold_left add l1 a = fold_left add l2 a.
Proof.
intros l1 l2 a Hpermut. revert a.
induction Hpermut; intro a.
+ now simpl.
+ simpl. rewrite H. apply IHHpermut.
+ cbn [fold_left]. now rewrite <- add_assoc, (add_comm y x), add_assoc.
+ now rewrite IHHpermut1.
Qed.

(** Barycenter of a list of locations *)

Definition barycenter (E: list R2) : R2 :=
  /(INR (List.length E)) * (List.fold_left add E origin).

Definition sqr_dist_sum_aux (init: R) (pt: R2) (E: list R2) : R :=
  List.fold_left (fun acc pt' => acc + (dist pt pt')²) E init.

Definition sqr_dist_sum := sqr_dist_sum_aux 0.

Axiom Barycenter_n_spec :
  forall (E: list R2) (B: R2),
    barycenter E = B -> 
    forall p,
      sqr_dist_sum B E <= sqr_dist_sum p E.

Definition is_barycenter_n (E: list R2) (B: R2) : Prop :=
  forall p, sqr_dist_sum B E <= sqr_dist_sum p E.

Axiom barycenter_n_spec : forall (E: list R2),
    is_barycenter_n E (barycenter E).
Axiom barycenter_n_unique: forall E a b,
    is_barycenter_n E a -> is_barycenter_n E b -> a == b.


Instance barycenter_compat : Proper (PermutationA equiv ==> equiv) barycenter.
Proof.
intros l1 l2 Hpermut. unfold barycenter.
assert (Hl: List.length l1 = List.length l2) by apply (PermutationA_length Hpermut).
rewrite Hl; clear Hl. f_equiv. now apply fold_add_permutation.
Qed.


Lemma sqr_dist_sum_aux_compat : Proper (Logic.eq ==> equiv ==> PermutationA equiv ==> Logic.eq) sqr_dist_sum_aux.
Proof.
intros i1 i2 Heqi pt1 pt2 Heqpt E1 E2 Hpermut.
unfold sqr_dist_sum_aux.
revert i1 i2 Heqi.
induction Hpermut; intros i1 i2 Heqi.
+ now simpl.
+ pattern x₁; rewrite H.
  simpl. apply IHHpermut.
  now rewrite Heqpt, Heqi.
+ simpl. f_equiv.
  - now rewrite Heqpt.
  - rewrite Heqi, Heqpt.
    ring.
+ rewrite Heqpt in *.
  rewrite (IHHpermut1 i1 i2 Heqi).
  now rewrite (IHHpermut2 i2 i2).
Qed.

Lemma sqr_dist_sum_compat : Proper (equiv ==> PermutationA equiv ==> Logic.eq) sqr_dist_sum.
Proof. now apply sqr_dist_sum_aux_compat. Qed.

Lemma barycenter_dist_decrease_aux : forall E dm,
    E <> nil ->
    (forall p1 p2, In p1 E -> In p2 E -> dist p1 p2 <= dm) ->
    forall p, (forall q, In q E -> dist p q <= dm) ->
              dist p (barycenter E) <= dm.
Proof.
intros E dm Hnotempty Hdm p Hp.
assert (Hlength_pos: 0 < INR (List.length E)).
{ apply lt_0_INR. destruct E; try (now elim Hnotempty); []. simpl. omega. }
rewrite R2norm_dist. subst. unfold barycenter.
replace p%R2 with (- / INR (length E) * (- INR (length E) * p))%R2
  by (rewrite mul_morph, Ropp_inv_permute, <- Rinv_l_sym, mul_1; lra || reflexivity).
rewrite <- minus_morph, <- mul_distr_add, R2norm_mul, Rabs_Ropp, Rabs_right;
try (now apply Rle_ge, Rlt_le, Rinv_0_lt_compat); [].
apply Rmult_le_reg_l with (r := INR (length E)); trivial; [].
rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l; try lra; [].
induction E as [| a [| b E]].
+ now elim Hnotempty.
+ specialize (Hp a ltac:(now left)). cbn -[mul add].
  replace ((-1 * p) + ((0, 0) + a))%R2 with (a - p)%R2 by (destruct a, p; simpl; f_equal; ring).
  now rewrite Rmult_1_l, <- R2norm_dist, dist_sym.
+ clear Hlength_pos Hnotempty.
  set (F := b :: E). fold F in IHE, Hdm, Hp.
  set (lF := length F). fold lF in IHE.
  replace (length (a :: F)) with (1 + lF)%nat; [ | simpl; reflexivity ].
  rewrite add_comm, S_INR, Ropp_plus_distr, <- add_morph, Rmult_plus_distr_r, Rmult_1_l.
  cbn [fold_left].
  rewrite fold_add_ac, <- add_assoc, (add_comm a), <- add_assoc, add_assoc.
  replace (-1 * p + a)%R2 with (a - p)%R2 by (destruct a, p; simpl; f_equal; ring).
  rewrite R2norm_ineq.
  apply Rplus_le_compat.
  - rewrite add_comm. apply IHE; intuition; unfold lF, F; try discriminate; [].
    cbn [length]. rewrite S_INR.
    apply Rplus_le_lt_0_compat; apply pos_INR || apply Rlt_0_1.
  - rewrite <- R2norm_dist, dist_sym. apply Hp. now left.
Qed.

Lemma barycenter_dist_decrease : forall E dm,
    E <> nil ->
    (forall p1 p2, In p1 E -> In p2 E -> dist p1 p2 <= dm) ->
    forall p, In p E -> dist p (barycenter E) <= dm.
Proof.
intros E dm Hnotempty Hdm p Hp.
apply (barycenter_dist_decrease_aux Hnotempty Hdm).
intros q Hq. now apply Hdm.
Qed.

(** **  Triangles  **)

Inductive triangle_type :=
  | Equilateral
  | Isosceles (vertex : R2)
  | Scalene.

Function classify_triangle (pt1 pt2 pt3 : R2) : triangle_type :=
  if Rdec_bool (dist pt1 pt2) (dist pt2 pt3)
  then if Rdec_bool (dist pt1 pt3) (dist pt2 pt3)
       then Equilateral
       else Isosceles pt2
  else if Rdec_bool (dist pt1 pt3) (dist pt2 pt3) then Isosceles pt3
  else if Rdec_bool (dist pt1 pt2) (dist pt1 pt3) then Isosceles pt1
  else Scalene.

Function opposite_of_max_side (pt1 pt2 pt3 : R2) :=
  let len12 := dist pt1 pt2 in
  let len23 := dist pt2 pt3 in
  let len13 := dist pt1 pt3 in
  if Rle_bool len12 len23
  then if Rle_bool len23 len13 then pt2 else pt1
  else if Rle_bool len12 len13 then pt2 else pt3.

Lemma classify_triangle_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    classify_triangle pt1 pt2 pt3 =  classify_triangle pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' Hperm.
  rewrite <- PermutationA_Leibniz, (PermutationA_3 _) in Hperm.
  decompose [or and] Hperm; clear Hperm; subst;
  match goal with
  | |- ?x = ?x => reflexivity
  | |- classify_triangle ?a ?b ?c = classify_triangle ?a' ?b' ?c'
    =>
    functional induction (classify_triangle a b c); auto;
    functional induction (classify_triangle a' b' c'); auto
  end;
  normalize_R2dist pt1' pt2' pt3'; exfalso; try contradiction;
  match goal with
    | H1:?A <> ?B, H2: ?B = ?A |- _ => symmetry in H2; contradiction
    | H1:?A <> ?B, H2: ?A = ?C , H3: ?C = ?B  |- _ =>
        assert (A = B) by (transitivity C; auto); contradiction
    | H1:?A <> ?B, H2: ?A = ?C , H3: ?B = ?C  |- _ =>
        assert (A = B) by (transitivity C; auto); contradiction || (symmetry; contradiction)
    | H1:?A <> ?B, H2: ?C = ?A , H3: ?C = ?B  |- _ =>
        assert (A = B) by (transitivity C; auto); contradiction || (symmetry; contradiction)
    | H1:?A <> ?B, H2: ?C = ?A , H3: ?B = ?C  |- _ =>
        assert (A = B) by (transitivity C; auto); contradiction || (symmetry; contradiction)
    end.
Qed.

Lemma opposite_of_max_side_compat : forall pt1 pt2 pt3 pt1' pt2' pt3',
    classify_triangle pt1 pt2 pt3 = Scalene ->
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    opposite_of_max_side pt1 pt2 pt3 = opposite_of_max_side pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' scalene Hperm.
  generalize (classify_triangle_compat Hperm).
  intro scalene'.
  rewrite scalene in scalene'. symmetry in scalene'.
  functional inversion scalene.
  functional inversion scalene'.
  clear scalene' scalene.
  normalize_R2dist pt1 pt2 pt3.
  normalize_R2dist pt1' pt2' pt3'.
  rewrite <- PermutationA_Leibniz, (PermutationA_3 _) in Hperm.
  decompose [or and] Hperm; clear Hperm; subst; reflexivity ||
  match goal with
  | |- ?x = ?x => reflexivity
  | |- opposite_of_max_side ?a ?b ?c = opposite_of_max_side ?a' ?b' ?c'
    =>
    functional induction (opposite_of_max_side a b c);auto;
    functional induction (opposite_of_max_side a' b' c');auto
  end;
  repeat rewrite ?Rle_bool_true_iff, ?Rle_bool_false_iff in *
  ; repeat progress normalize_R2dist pt1' pt2' pt3' ;try contradiction;
  repeat match goal with
         | H1: ?A < ?A |- _ => elim (Rlt_irrefl _ h_ltxx)
         | H1: ?A < ?B, H2: ?B < ?A |- _ =>
           assert (h_ltxx:A<A) by (eapply Rlt_trans;eauto);elim (Rlt_irrefl _ h_ltxx)
         | H1: ?A < ?B, H2: ?B < ?C, H3: ?C < ?A |- _ =>
           assert (h_ltxx:A<C) by (eapply Rlt_trans;eauto);
           assert (h_ltxx':A<A) by (eapply Rlt_trans;eauto);elim (Rlt_irrefl _ h_ltxx')
         | H1:?A <> ?B, H2: ?A <= ?B |- _ => assert (A<B) by (apply Rle_neq_lt;auto);clear H2
         | H1:?A <> ?B, H2: ?B <= ?A |- _ => assert (B<A) by (apply Rle_neq_lt;auto;apply not_eq_sym;auto);clear H2
         end.
Qed.

Lemma classify_triangle_Equilateral_spec : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Equilateral
  <-> dist pt1 pt2 = dist pt2 pt3 /\ dist pt1 pt3 = dist pt2 pt3.
Proof.
intros pt1 pt2 pt3. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *; split; intro; intuition discriminate.
Qed.

Lemma classify_triangle_Isosceles_spec : forall pt1 pt2 pt3 pt,
  classify_triangle pt1 pt2 pt3 = Isosceles pt
  <-> (pt = pt1 /\ dist pt1 pt2 = dist pt1 pt3 /\ dist pt1 pt2 <> dist pt2 pt3)
   \/ (pt = pt2 /\ dist pt2 pt1 = dist pt2 pt3 /\ dist pt2 pt1 <> dist pt1 pt3)
   \/ (pt = pt3 /\ dist pt3 pt1 = dist pt3 pt2 /\ dist pt3 pt1 <> dist pt1 pt2).
Proof.
intros pt1 pt2 pt3 pt. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *;
repeat lazymatch goal with
  | H : context[dist pt2 pt1] |- _ => rewrite (dist_sym pt1 pt2) in H
  | H : context[dist pt3 pt1] |- _ => rewrite (dist_sym pt1 pt3) in H
  | H : context[dist pt3 pt2] |- _ => rewrite (dist_sym pt2 pt3) in H
  | |- context[dist pt2 pt1] => rewrite (dist_sym pt1 pt2)
  | |- context[dist pt3 pt1] => rewrite (dist_sym pt1 pt3)
  | |- context[dist pt3 pt2] => rewrite (dist_sym pt2 pt3)
  | H : context[dist ?x ?y = _] |- context[dist ?x ?y] => setoid_rewrite H; clear H
end;
split; intro H; discriminate || (progress decompose [or and] H; clear H) || (injection H; intro);
subst; trivial; try contradiction.
+ right; left. subst. repeat split. intro Heq. rewrite Heq in *. intuition.
+ do 2 right. subst. repeat split; trivial. intro Heq. rewrite Heq in *. intuition.
+ repeat match goal with
    | H : dist _ _ = _ |- _ => rewrite H in *; clear H
    | H : ?x <> ?x |- _ => now elim H
  end.
+ left. now repeat split.
Qed.

Lemma classify_triangle_Scalene_spec : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Scalene
  <-> dist pt1 pt2 <> dist pt2 pt3
   /\ dist pt1 pt2 <> dist pt1 pt3
   /\ dist pt1 pt3 <> dist pt2 pt3.
Proof.
intros pt1 pt2 pt3. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *; split; intro; intuition discriminate.
Qed.

Lemma isoscele_vertex_is_vertex: forall ptx pty ptz vertex,
  classify_triangle ptx pty ptz = Isosceles vertex -> 
  InA equiv vertex (ptx :: pty :: ptz :: nil).
Proof.
intros ptx pty ptz vertex H.
functional induction (classify_triangle ptx pty ptz);
try discriminate; inversion H; now repeat constructor.
Qed.

Lemma scalene_vertex_is_vertex: forall ptx pty ptz,
  classify_triangle ptx pty ptz = Scalene ->
  InA equiv (opposite_of_max_side ptx pty ptz) (ptx :: pty :: ptz :: nil).
Proof.
intros ptx pty ptz H.
functional induction (opposite_of_max_side ptx pty ptz);
repeat (left + right); reflexivity.
Qed.

(** **  Barycenter and middle  **)

(* Barycenter is the center of SEC for an equilateral triangle *)

Definition barycenter_3_pts (pt1 pt2 pt3:R2) := mul (Rinv 3) (add pt1 (add pt2 pt3)).

Lemma barycenter_3_pts_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    barycenter_3_pts pt1 pt2 pt3 =  barycenter_3_pts pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' Hperm.
  rewrite <- PermutationA_Leibniz, (PermutationA_3 _) in Hperm.
  decompose [or and] Hperm; clear Hperm; subst;
  reflexivity || unfold barycenter_3_pts; f_equal;
  destruct pt1', pt2', pt3'; cbn; f_equal; ring.
Qed.

Axiom Barycenter_spec: forall pt1 pt2 pt3 B: R2,
    barycenter_3_pts pt1 pt2 pt3 = B -> 
    forall p,
      (dist B pt1)² + (dist B pt2)² + (dist B pt3)²
      <= (dist p pt1)² + (dist p pt2)² + (dist p pt3)².

(* False if we are not in an euclidian space!
   Take for instance the coarse distance d(x,y) = 1 <-> x <> y, and pt1, pt2 pt3 different.
   Then any one of them is a barycenter. *)
Axiom Barycenter_spec_unicity: forall pt1 pt2 pt3 B: R2,
    barycenter_3_pts pt1 pt2 pt3 = B <-> 
    forall p, p <> B ->
              (dist B pt1)² + (dist B pt2)² + (dist B pt3)²
              < (dist p pt1)² + (dist p pt2)² + (dist p pt3)².

Definition is_middle pt1 pt2 B := forall p,
  (dist B pt1)² + (dist B pt2)² <= (dist p pt1)² + (dist p pt2)².
Definition is_barycenter_3_pts pt1 pt2 pt3 B := forall p,
  (dist B pt1)² + (dist B pt2)² + (dist B pt3)² <= (dist p pt1)² + (dist p pt2)² + (dist p pt3)².

(* TODO? *)
Axiom bary3_spec: forall pt1 pt2 pt3,
  is_barycenter_3_pts pt1 pt2 pt3 (barycenter_3_pts pt1 pt2 pt3).
Axiom bary3_unique: forall x y z a b,
    is_barycenter_3_pts x y z a -> is_barycenter_3_pts x y z b -> equiv a b.


Lemma R2dist_middle : forall pt1 pt2,
  dist pt1 (middle pt1 pt2) = /2 * dist pt1 pt2.
Proof.
intros pt1 pt2.
replace pt1 with (/2 * pt1 + /2 * pt1)%R2 at 1.
+ unfold middle. rewrite mul_distr_add. setoid_rewrite add_comm.
  replace (1/2) with (/2) by field. rewrite R2add_dist.
  rewrite R2mul_dist. rewrite Rabs_pos_eq; lra.
+ rewrite add_morph. replace (/ 2 + / 2) with 1 by field. now rewrite mul_1.
Qed.

Lemma middle_comm : forall ptx pty,
    equiv (middle ptx pty) (middle pty ptx).
Proof.
  intros ptx pty.
  unfold middle.
  rewrite add_comm.
  reflexivity.
Qed.

Lemma middle_shift : forall ptx pty, (middle ptx pty - ptx)%R2 == (pty - middle ptx pty)%R2.
Proof. unfold middle. destruct ptx, pty; simpl; hnf; f_equal; field. Qed.

Lemma middle_eq : forall ptx pty,
    equiv (middle ptx pty) ptx <-> equiv ptx pty.
Proof.
  cbn. intros [? ?] [? ?].
  split; intro h.
  - inversion h; clear h; f_equal; lra.
  - inversion_clear h.
    cbv.
    f_equal; lra.
Qed.

Lemma middle_diff: forall ptx pty,
  ptx <> pty -> ~InA equiv (middle ptx pty) (ptx :: pty :: nil).
Proof.
intros ptx pty Hdiff Hin.
inversion_clear Hin; subst.
* rewrite middle_eq in H. contradiction.
* inversion_clear H.
  - rewrite middle_comm, middle_eq in H0.
    symmetry in H0. contradiction.
  - inversion H0.
Qed.

Lemma middle_spec : forall pt1 pt2, is_middle pt1 pt2 (middle pt1 pt2).
Proof.
intros pt1 pt2 pt.
setoid_rewrite dist_sym. rewrite R2dist_middle, middle_comm, R2dist_middle, dist_sym.
rewrite R_sqr.Rsqr_mult. unfold Rsqr at 1 3. field_simplify.
transitivity ((dist pt1 pt + dist pt2 pt)² / 2).
+ replace (2 * (dist pt2 pt1)² / 4) with ((dist pt2 pt1)² / 2) by field.
  cut ((dist pt2 pt1)² <= (dist pt1 pt + dist pt2 pt)²); try lra; [].
  rewrite pos_Rsqr_le.
  - rewrite (dist_sym pt pt1), Rplus_comm. apply triang_ineq.
  - apply dist_pos.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply dist_pos.
+ assert (Hle : 0 <= (dist pt1 pt - dist pt2 pt)²) by apply Rle_0_sqr.
  rewrite R_sqr.Rsqr_minus in Hle. rewrite R_sqr.Rsqr_plus. lra.
Qed.

(* This is true because we use the euclidean distance. *)
Lemma middle_is_R2middle : forall pt1 pt2 pt, is_middle pt1 pt2 pt -> equiv pt (middle pt1 pt2).
Proof.
intros pt1 pt2 pt Hpt. specialize (Hpt (middle pt1 pt2)).
(* First, we simplify out middle pt1 pt2. *)
assert (Hmid : (dist (middle pt1 pt2) pt1)² + (dist (middle pt1 pt2) pt2)² = (dist pt1 pt2)² / 2).
{ setoid_rewrite dist_sym. rewrite R2dist_middle, middle_comm, R2dist_middle.
  rewrite (dist_sym pt1 pt2). rewrite R_sqr.Rsqr_mult. unfold Rsqr. field. }
rewrite Hmid in Hpt.
(* Then, we prove that pt is at the same distance of pt1 and pt2. *)
assert (Hle : (dist pt1 pt2)² <= (dist pt1 pt + dist pt pt2)²).
{ rewrite pos_Rsqr_le.
  - apply triang_ineq.
  - apply dist_pos.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply dist_pos. }
assert (Hpt' : 2 * (dist pt pt1)² + 2 * (dist pt pt2)² <= (dist pt1 pt2)²) by lra.
clear Hpt. rename Hpt' into Hpt.
rewrite R_sqr.Rsqr_plus in Hle.
assert (Heq0 : (dist pt1 pt - dist pt pt2)² = 0).
{ apply antisymmetry.
  - rewrite R_sqr.Rsqr_minus. apply Rle_minus. rewrite dist_sym in Hpt. lra.
  - apply Rle_0_sqr. }
apply Rsqr_0_uniq in Heq0. apply Rminus_diag_uniq in Heq0.
(* That distance is half the distance between pt1 and pt2. *)
assert (Hhalf : dist pt1 pt = dist pt1 pt2 / 2).
{ apply antisymmetry.
  + rewrite <- pos_Rsqr_le.
    - rewrite <- Heq0 in *. rewrite (dist_sym pt1 pt) in Hpt. ring_simplify in Hpt.
      unfold Rdiv. rewrite R_sqr.Rsqr_mult. unfold Rsqr in *. lra.
    - apply dist_pos.
    - assert (Rpos := dist_pos pt1 pt2). lra.
  + assert (Hgoal := triang_ineq pt1 pt pt2). lra. }
(* now, we rule out the dummy case pt1 = pt2. *)
destruct (equiv_dec pt1 pt2) as [Heq12 | Heq12].
+ rewrite Heq12, R2_dist_defined_2 in Hhalf.
  replace (0/2) with 0 in Hhalf by field. rewrite dist_defined in Hhalf.
  rewrite <- Hhalf, Heq12. unfold middle. destruct pt2; simpl; hnf; f_equal; field.
+ (* Finally, we use the specification of segment bisector and prove that k is 0. *)
  rewrite segment_bisector_spec in Heq0; trivial; [].
  destruct Heq0 as [k Heq]. rewrite Heq.
  cut (k = 0); try (now intro; subst; rewrite mul_0, add_origin); [].
  rewrite dist_sym, R2norm_dist, Heq in Hhalf. apply (f_equal Rsqr) in Hhalf. revert Hhalf.
  replace (middle pt1 pt2 + k * orthogonal (pt2 - pt1) - pt1)%R2
    with (1 / 2 * (pt2 - pt1) + k * orthogonal (pt2 - pt1))%R2.
  - rewrite R2norm_add. repeat rewrite ?R2norm_mul, ?R_sqr.Rsqr_mult, <- ?R_sqr.Rsqr_abs.
    rewrite product_mul_l, product_mul_r. rewrite orthogonal_perpendicular.
    assert (~pt2 - pt1 == origin)%R2.
    { rewrite <- dist_defined. rewrite <- (R2add_dist pt1).
      setoid_rewrite add_comm at 3. rewrite add_origin.
      rewrite <- add_assoc. setoid_rewrite add_comm at 2. rewrite add_opp, add_origin.
      rewrite dist_sym. rewrite dist_defined. auto. }
    rewrite R2norm_orthogonal; trivial; [].
    rewrite R_sqr.Rsqr_1, Rmult_1_r. repeat rewrite Rmult_0_r. rewrite Rplus_0_r.
    rewrite dist_sym, R2norm_dist. setoid_rewrite R_sqr.Rsqr_div; try lra.
    unfold Rsqr. intro. assert (Hk : k*k = 0) by lra.
    now apply Rsqr_0_uniq.
  - unfold middle. destruct pt1, pt2; simpl. f_equal; field;
    rewrite R2norm_0; cbn; intros [= ? ?]; apply Heq12; hnf; f_equal; lra.
Qed.

Corollary is_middle_uniq : forall pt1 pt2 mid1 mid2,
  is_middle pt1 pt2 mid1 -> is_middle pt1 pt2 mid2 -> mid1 = mid2.
Proof. intros ? ? ? ? H1 H2. apply middle_is_R2middle in H1. apply middle_is_R2middle in H2. congruence. Qed.

Lemma colinear_middle : forall pt1 pt2, colinear (pt2 - pt1) (pt2 - middle pt1 pt2).
Proof.
intros pt1 pt2.
destruct (equiv_dec pt1 pt2) as [Heq | Hneq].
+ rewrite Heq, add_opp. apply colinear_origin_l.
+ assert (Hmid : ~(pt2 - middle pt1 pt2)%R2 == origin).
  { intro Habs. apply Hneq. unfold middle. destruct pt1, pt2; compute in *.
    injection Habs. intros. f_equal; lra. }
  unfold colinear, orthogonal, perpendicular, middle, product.
  destruct pt1 as [x1 y1], pt2 as [x2 y2]. cbn. field.
  now rewrite R2norm_0.
Qed.

Lemma middle_barycenter_3_neq: forall pt1 pt2 ptopp,
    classify_triangle pt1 pt2 ptopp = Equilateral ->
    middle pt1 pt2 = barycenter_3_pts pt1 pt2 ptopp ->
    pt1 = pt2.
Proof.
intros pt1 pt2 ptopp Htriangle h_middle_eq_bary.
unfold barycenter_3_pts,middle in h_middle_eq_bary;
  functional inversion Htriangle; rewrite -> ?Rdec_bool_true_iff in *;
  (* I prefer hdist1 hdist2 later :) *)
  repeat progress match goal with
                  | HH: dist ?p ?p' = dist ?p'' ?p''' |- _ =>
                    let hdist := fresh "hdist" in
                    assert (hdist:Rsqr (dist p p') = Rsqr (dist p'' p'''))
                    ; [ setoid_rewrite HH; try reflexivity;clear HH | clear HH ]
                  end.
rename hdist into hdist2, hdist0 into hdist1.
destruct pt1 as [xA yA], pt2 as [xB yB], ptopp as [xC yC]; cbn in *.
setoid_rewrite Rsqr_sqrt in hdist2; try now (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
setoid_rewrite Rsqr_sqrt in hdist1; try now (apply Rplus_le_le_0_compat; apply Rle_0_sqr).
inversion h_middle_eq_bary as [[heqx heqy]].
assert (hand:xA=xB /\ yA = yB).
{ clear -hdist1 hdist2 heqx heqy.
  assert (heqxC:(xC = / 2 * (xA + xB))%R) by lra.
  assert (heqyC:(yC = / 2 * (yA + yB))%R) by lra.
  rewrite heqxC,heqyC in hdist1.
  unfold Rsqr in *.
  apply Rminus_diag_eq in hdist1.
  revert hdist1.
  clear.
  match goal with |- ?v = _ -> _ => replace v with (3/4*((xA-xB)*(xA-xB) + (yA-yB)*(yA-yB)))%R by field end.
  intros h.
  apply (Rmult_eq_compat_l (4/3)%R) in h.
  rewrite <- Rmult_assoc in h.
  replace (4 / 3)%R with (/ (3 / 4))%R in h.
  + rewrite <- Rinv_l_sym in h.
    - rewrite Rmult_1_l, Rmult_0_r in h.
      apply Rplus_sqr_eq_0 in h.
      inversion h.
      intuition.
    - lra.
  + lra. }
destruct hand. now subst.
Qed.

(** Some results about equilateral triangles. *)
Section Equilateral_results.
  Variables pt1 pt2 pt3 : R2.
  Hypothesis Htriangle : classify_triangle pt1 pt2 pt3 = Equilateral.
  
  (* The base of the altitude of an equilateral triangle is the middle of the opposite side. *)
  Lemma equilateral_altitude_base : perpendicular (pt3 - pt2) (pt1 - middle pt2 pt3).
  Proof.
  null (pt3 - pt2)%R2.
  + apply perpendicular_origin_l.
  + assert (Heq := decompose_on Hnull (pt1 - middle pt2 pt3)).
  Admitted.
  
  (* The altitude of an equilateral triangle of side length a is (sqrt 2 / 3) * a. *)
  Lemma equilateral_altitude : dist pt1 (middle pt2 pt3) = sqrt 3 / 2 * dist pt1 pt2.
  Proof.
  assert (Hbase := equilateral_altitude_base).
  rewrite classify_triangle_Equilateral_spec in Htriangle. destruct Htriangle as [Heq12 Heq13]. clear Htriangle.
  null (pt3 - pt2)%R2; [| null (pt1 - middle pt2 pt3)%R2].
  + rewrite R2sub_origin in Hnull.
    assert (Heq : pt1 == pt2 /\ pt2 == pt3).
    { rewrite Hnull in *. clear Hnull. rewrite R2_dist_defined_2, dist_defined in Heq12. now split. }
    destruct Heq as [Heq ?]. rewrite Heq. rewrite R2_dist_defined_2. ring_simplify.
    rewrite dist_defined. symmetry. now rewrite middle_eq.
  + exfalso. apply Hnull. rewrite R2sub_origin in *. rewrite <- dist_defined, dist_sym.
    rewrite Hnull0 in *. rewrite dist_sym in Heq12. rewrite R2dist_middle in Heq12. lra.
  + apply (perpendicular_colinear_compat Hnull Hnull0 (colinear_middle pt2 pt3) (reflexivity _))%R2 in Hbase.
    rewrite <- perpendicular_opp_compat_l in Hbase.
    rewrite Pythagoras in Hbase.
    replace (- (pt3 - middle pt2 pt3) + (pt1 - middle pt2 pt3))%R2 with (pt1 - pt3)%R2 in Hbase
      by (unfold middle; destruct pt1, pt2, pt3; simpl; f_equal; lra).
    repeat rewrite ?R2norm_opp, <- R2norm_dist in Hbase.
    rewrite square_dist_equiv.
    - assert (Heq : (dist pt1 (middle pt2 pt3))² = (dist pt1 pt3)² - (dist pt3 (middle pt2 pt3))²) by lra.
      rewrite Heq.
      rewrite middle_comm, R2dist_middle. rewrite (dist_sym pt2). rewrite Heq12, Heq13.
      unfold Rdiv. do 3 rewrite R_sqr.Rsqr_mult. rewrite Rsqr_sqrt; try lra.
      replace (/2)² with (/4) by (unfold Rsqr; lra). lra.
    - assert (Hpos := sqrt_pos 3). apply Rmult_le_pos; apply dist_pos || lra.
  Qed.
  
  (* The radius of the circumscribed circle to an equilateral triangle of side length a is (sqrt 3 / 3) * a. *)
  Lemma equilateral_barycenter_dist : dist (barycenter_3_pts pt1 pt2 pt3) pt1 = sqrt 3 / 3 * dist pt1 pt2.
  Proof.
  unfold barycenter_3_pts. rewrite R2norm_dist.
  replace ((/ 3 * (pt1 + (pt2 + pt3)) - pt1))%R2 with (2 / 3 * (middle pt2 pt3 - pt1))%R2
    by (unfold middle; destruct pt1, pt2, pt3; simpl; f_equal; lra).
  rewrite R2norm_mul, <- R2norm_dist, dist_sym.
  rewrite equilateral_altitude. rewrite Rabs_pos_eq; lra.
  Qed.
End Equilateral_results.

Lemma same_dist_vertex_notin_sub_circle: forall ptx pty c,
  dist pty c = dist ptx c ->
  (dist (middle c ptx) pty <= dist c (middle c ptx))%R ->
  pty == ptx.
Proof.
intros ptx pty c h_dist_iso hdist.
destruct (Rtotal_order (dist (middle c ptx) pty) (dist c (middle c ptx))) as [Hlt | [Heq | Hlt]].
- assert (Heq : ((dist c ptx) = 2 * dist c (middle c ptx))%R).
  { rewrite R2dist_middle.
    lra. }
  assert (h_ineq:=triang_ineq pty (middle c ptx) c).
  setoid_rewrite dist_sym in h_ineq at 2 3.
  rewrite h_dist_iso in h_ineq.
  rewrite dist_sym in h_ineq at 1.
  rewrite Heq in h_ineq.
  exfalso.
  lra.
- pose (m := middle c ptx). fold m in Heq.
  assert (Htriang_eq : (dist c pty = dist c m + dist m pty)%R).
  { rewrite Heq. ring_simplify. unfold m. rewrite R2dist_middle.
    rewrite dist_sym, h_dist_iso, dist_sym. field. }
  apply triang_ineq_eq in Htriang_eq. destruct Htriang_eq as [Hcol1 Hcol2].
  assert (Hmiddle : colinear (m - c) (ptx - c)).
  { symmetry. unfold m. rewrite middle_shift. apply colinear_middle. }
  (* Let us eliminate the cases where m = c and pty = c. *)
  null (m - c)%R2.
  { unfold m in Hnull. rewrite R2sub_origin in Hnull. rewrite middle_eq in Hnull.
    rewrite <- dist_defined. rewrite Hnull in h_dist_iso. rewrite h_dist_iso. apply R2_dist_defined_2. }
  null (pty - c)%R2.
  { rewrite R2sub_origin in Hnull0. rewrite <- dist_defined.
    rewrite Hnull0 in *. rewrite dist_sym, <- h_dist_iso. apply R2_dist_defined_2. }
  assert (Hcol3 := colinear_trans Hnull Hcol1 Hmiddle).
  symmetry in Hcol3. setoid_rewrite dist_sym in h_dist_iso.
  assert (Hcol4 := colinear_trans Hnull0 Hcol3 Hcol2).
  destruct (equiv_dec ptx c) as [Hxc | Hxc].
  + rewrite Hxc in *. rewrite <- dist_defined. rewrite dist_sym, h_dist_iso. apply R2_dist_defined_2.
  + apply colinear_decompose in Hcol4; try (now rewrite R2sub_origin); [].
    rewrite dist_sym in Heq. rewrite <- R2norm_dist, Heq in Hcol4.
    unfold m in Hcol4. rewrite R2dist_middle in Hcol4. rewrite minus_morph in Hcol4.
    rewrite dist_sym, R2norm_dist, <- mul_morph, <- unitary_id in Hcol4. fold m in Hcol4.
    destruct Hcol4 as [Hcol4 | Hcol4].
    * assert (Hpty : pty == (m + /2 * (ptx - c))%R2 ).
      { apply add_reg_r with (- m)%R2. rewrite Hcol4. setoid_rewrite add_comm at 3.
        now rewrite <- add_assoc, add_opp, add_origin. }
      rewrite Hpty. unfold m, middle. destruct ptx, c; simpl; hnf; f_equal; field.
    * assert (Hpty : pty == (m - /2 * (ptx - c))%R2).
      { apply add_reg_r with (- m)%R2. rewrite Hcol4. setoid_rewrite add_comm at 3.
        now rewrite <- add_assoc, add_opp, add_origin. }
      assert (Hyc : pty == c).
      { rewrite Hpty. unfold m, middle. destruct ptx, c; simpl; hnf; f_equal; field. }
      rewrite Hyc, <- dist_defined, <- h_dist_iso, Hyc. apply R2_dist_defined_2.
- exfalso; lra.
Qed.

Lemma isosceles_vertex_notin_sub_circle: forall ptx pty c,
  classify_triangle ptx pty c = Isosceles c ->
  (dist (middle c ptx) pty <= dist c (middle c ptx))%R ->
  pty == ptx.
Proof.
intros ptx pty c Hhiso hdist.
assert (h_dist_iso:dist pty c = dist ptx c).
{ apply classify_triangle_Isosceles_spec in Hhiso.
  decompose [or and] Hhiso.
  + subst.
    rewrite <- H.
    apply dist_sym.
  + subst.
    rewrite <- H0.
    apply dist_sym.
  + setoid_rewrite dist_sym.
    symmetry.
    assumption. }
assert (h:=Rtotal_order (dist (middle c ptx) pty) (dist c (middle c ptx))).
destruct h as [Hlt | [Heq | Hlt]].
- assert (Heq : ((dist c ptx) = 2 * dist c (middle c ptx))%R).
  { rewrite R2dist_middle.
    lra. }
  assert (h_ineq:=triang_ineq pty (middle c ptx) c).
  setoid_rewrite dist_sym in h_ineq at 2 3.
  rewrite h_dist_iso in h_ineq.
  rewrite dist_sym in h_ineq at 1.
  rewrite Heq in h_ineq.
  exfalso.
  lra.
- pose (m := middle c ptx). fold m in Heq.
  assert (Htriang_eq : (dist c pty = dist c m + dist m pty)%R).
  { rewrite Heq. ring_simplify. unfold m. rewrite R2dist_middle.
    rewrite dist_sym, h_dist_iso, dist_sym. field. }
  apply triang_ineq_eq in Htriang_eq. destruct Htriang_eq as [Hcol1 Hcol2].
  assert (Hmiddle : colinear (m - c) (ptx - c)).
  { symmetry. unfold m. rewrite middle_shift. apply colinear_middle. }
  (* Let us eliminate the cases where m = c and pty = c. *)
  null (m - c)%R2.
  { unfold m in Hnull. rewrite R2sub_origin in Hnull. rewrite middle_eq in Hnull.
    rewrite <- dist_defined. rewrite Hnull in h_dist_iso. rewrite h_dist_iso. apply R2_dist_defined_2. }
  null (pty - c)%R2.
  { rewrite R2sub_origin in Hnull0. rewrite <- dist_defined.
    rewrite Hnull0 in *. rewrite dist_sym, <- h_dist_iso. apply R2_dist_defined_2. }
  assert (Hcol3 := colinear_trans Hnull Hcol1 Hmiddle).
  symmetry in Hcol3. setoid_rewrite dist_sym in h_dist_iso.
  assert (Hcol4 := colinear_trans Hnull0 Hcol3 Hcol2).
  destruct (equiv_dec ptx c) as [Hxc | Hxc].
  + rewrite Hxc in *. rewrite <- dist_defined. rewrite dist_sym, h_dist_iso. apply R2_dist_defined_2.
  + apply colinear_decompose in Hcol4; try (now rewrite R2sub_origin); [].
    rewrite dist_sym in Heq. rewrite <- R2norm_dist, Heq in Hcol4.
    unfold m in Hcol4. rewrite R2dist_middle in Hcol4. rewrite minus_morph in Hcol4.
    rewrite dist_sym, R2norm_dist, <- mul_morph, <- unitary_id in Hcol4. fold m in Hcol4.
    destruct Hcol4 as [Hcol4 | Hcol4].
    * assert (Hpty : pty == (m + /2 * (ptx - c))%R2).
      { apply add_reg_r with (- m)%R2. rewrite Hcol4. setoid_rewrite add_comm at 3.
        now rewrite <- add_assoc, add_opp, add_origin. }
      rewrite Hpty. unfold m, middle. destruct ptx, c; simpl; hnf; f_equal; field.
    * assert (Hpty : pty == (m - /2 * (ptx - c))%R2).
      { apply add_reg_r with (- m)%R2. rewrite Hcol4. setoid_rewrite add_comm at 3.
        now rewrite <- add_assoc, add_opp, add_origin. }
      assert (Hyc : pty == c).
      { rewrite Hpty. unfold m, middle. destruct ptx, c; simpl; hnf; f_equal; field. }
      rewrite Hyc, <- dist_defined, <- h_dist_iso, Hyc. apply R2_dist_defined_2.
- exfalso; lra.
Qed.

(** **  Circles and SEC  *)

(** ***  General results about circles  **)

Record circle := {
  center : R2;
  radius : R}.

Definition enclosing_circle (c : circle) l := forall x, In x l -> dist x (center c) <= (radius c).
Definition on_circle (c : circle) x := Rdec_bool (dist x (center c)) (radius c).

Instance enclosing_circle_compat : forall c, Proper (@Permutation _ ==> iff) (enclosing_circle c).
Proof.
repeat intro. unfold enclosing_circle.
do 2 rewrite <- Forall_forall. apply Forall_Permutation_compat; trivial.
intros ? ? ?. now subst.
Qed.

Instance on_circle_compat : Proper (eq ==> equiv ==> eq) on_circle.
Proof. repeat intro. cbn in *. now subst. Qed.

Lemma on_circle_true_iff : forall c pt, on_circle c pt = true <-> dist pt (center c) = radius c.
Proof. intros c pt. unfold on_circle. now rewrite Rdec_bool_true_iff. Qed.

(* If the radius of circle is not zero then the center is not part of it. *)
Lemma center_not_on_circle : forall c,
    on_circle c (center c) = false <-> radius c <> 0%R.
Proof.
intro.
split; [intros hrad | intro honcirc]; unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
- rewrite Rdec_bool_false_iff in *. auto.
- apply Rdec_bool_false_iff. auto.
Qed.

Lemma center_on_circle : forall c,
  on_circle c (center c) = true <-> radius c = 0%R.
Proof.
intro.
split;[ intros hrad | intro honcirc];unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
- rewrite Rdec_bool_true_iff in *. auto.
- apply Rdec_bool_true_iff. auto.
Qed.

(* Given a circle of center [c] and a point pt outside this circle, 
   any point pt' inside the disk is closer to any point on [c pt] than to [pt]. *)
Lemma disk_dist : forall circ pt, radius circ < dist pt (center circ) ->
  forall pt' k, 0 < k < dist pt (center circ) - radius circ -> dist pt' (center circ) <= radius circ ->
  dist pt' (pt + k * unitary (center circ - pt))%R2 < dist pt' pt.
Proof.
intros circ pt Hpt pt' k Hk Hpt'.
assert (Hle := dist_pos  pt' (center circ)).
assert (Hneq : ~equiv (center circ) pt).
{ rewrite <- dist_defined. intro Habs. rewrite dist_sym in Habs. rewrite Habs in *. apply (Rlt_irrefl 0).
  apply Rle_lt_trans with (radius circ); lra. }
pose (pt'' := ((pt + k * unitary (center circ - pt)))%R2).
assert (Hneq' : ~equiv (center circ) pt'').
{ unfold pt''. rewrite <- R2sub_origin. rewrite opp_distr_add, add_assoc.
  rewrite (unitary_id (center circ - pt)) at 1.
  rewrite <- minus_morph, add_morph, <- R2norm_dist, dist_sym.
  intro Habs. apply mul_integral in Habs. destruct Habs as [Habs | Habs].
  - lra.
  - rewrite <- R2sub_origin, <- unitary_is_origin in Hneq. contradiction. }
assert (Heq' : (pt - pt'' = -k * unitary (center circ - pt))%R2).
{ unfold pt''. now rewrite opp_distr_add, add_assoc, add_opp, add_comm, add_origin, minus_morph. }
assert (Heq : equiv (unitary (center circ - pt)) (unitary (center circ - pt''))).
{ unfold pt''. rewrite opp_distr_add, add_assoc.
  rewrite (unitary_id (center circ - pt)) at 2.
  rewrite <- minus_morph, add_morph.
  rewrite unitary_mul, unitary_idempotent; try reflexivity; [].
  rewrite <- R2norm_dist, dist_sym.
  lra. }
rewrite <- R2sub_origin in Hneq'. fold pt''.
rewrite <- (R2add_dist (-pt'')%R2 pt' pt).
rewrite Heq', Heq.
rewrite <- pos_Rsqr_lt; try apply dist_pos; [].
assert (Heq_pt' := decompose_on Hneq' (pt' - pt'')).
do 2 rewrite R2norm_dist. rewrite Heq_pt'.
assert (Hperp : perpendicular (product (pt' - pt'') (unitary (center circ - pt'')) * unitary (center circ - pt''))
                      (product (pt' - pt'') (orthogonal (center circ - pt'')) * orthogonal (center circ - pt''))).
{ apply perpendicular_mul_compat_l, perpendicular_mul_compat_r, unitary_orthogonal_perpendicular. }
rewrite Pythagoras in Hperp. rewrite Hperp. clear Hperp.
replace (product (pt' - pt'') (unitary (center circ - pt'')) * unitary (center circ - pt'') +
         product (pt' - pt'') (orthogonal (center circ - pt'')) * orthogonal (center circ - pt'') -
         - k * unitary (center circ - pt''))%R2
  with ((product (pt' - pt'') (unitary (center circ - pt'')) + k) * unitary (center circ - pt'') +
         product (pt' - pt'') (orthogonal (center circ - pt'')) * orthogonal (center circ - pt''))%R2
  by (destruct (unitary (center circ - pt'')), (orthogonal (center circ - pt'')); simpl; f_equal; lra).
assert (Hperp : perpendicular
                  ((product (pt' - pt'') (unitary (center circ - pt'')) + k) * unitary (center circ - pt''))
                  (product (pt' - pt'') (orthogonal (center circ - pt'')) * orthogonal (center circ - pt''))).
{ apply perpendicular_mul_compat_l, perpendicular_mul_compat_r, unitary_orthogonal_perpendicular. }
rewrite Pythagoras in Hperp. rewrite Hperp. clear Hperp.
apply Rplus_lt_compat_r.
rewrite pos_Rsqr_lt; try apply R2norm_pos; [].
do 2 rewrite R2norm_mul. rewrite R2norm_unitary; trivial; [].
assert (Hpos : 0 <= product (pt' - pt'') (unitary (center circ - pt''))).
{ admit. }
repeat rewrite Rabs_pos_eq; lra.
Admitted.


Axiom three_points_same_circle : forall c1 c2 pt1 pt2 pt3,
  NoDup (pt1 :: pt2 :: pt3 :: nil) ->
  on_circle c1 pt1 = true -> on_circle c1 pt2 = true -> on_circle c1 pt3 = true ->
  on_circle c2 pt1 = true -> on_circle c2 pt2 = true -> on_circle c2 pt3 = true ->
  c1 = c2.

(** ***  Definition of the [SEC]  **)

(** We assume the existence of a function [SEC] computing the smallest enclosing circle,
    given by center and radius. *)
Parameter SEC : list R2 -> circle.
(** The SEC is an enclosing circle. *)
Axiom SEC_spec1 : forall l, enclosing_circle (SEC l) l.
(** The SEC is the smallest one. *)
Axiom SEC_spec2 : forall l c, enclosing_circle c l -> radius (SEC l) <= radius c.
(** Extra specification in the degenerate case. *)
Axiom SEC_nil : radius (SEC nil) = 0.
(** Its definition does not depend on the order of points. *)
Declare Instance SEC_compat : Proper (@Permutation _ ==> Logic.eq) SEC.

Global Instance SEC_compat_bis : Proper (PermutationA Logic.eq ==> Logic.eq) SEC.
Proof. intros ? ? Heq. rewrite PermutationA_Leibniz in Heq. now rewrite Heq. Qed.

(* The last axiom is useful because of the following degeneracy fact. *)
Lemma enclosing_circle_nil : forall pt r, enclosing_circle {| center := pt; radius := r |} nil.
Proof. intros. unfold enclosing_circle. intros x Hin. elim Hin. Qed.

Definition center_eq c1 c2 := c1.(center) = c2.(center).
Definition radius_eq c1 c2 := c1.(radius) = c2.(radius).

(** Unicity proof of the radius of the SEC *)
Instance SEC_radius_compat :
  Proper (@Permutation _ ==> center_eq) SEC -> Proper (@Permutation _ ==> radius_eq) SEC.
Proof.
intros Hspec l1 l2 Hperm.
assert (Hup1 := SEC_spec1 l1). assert (Hdown1 := @SEC_spec2 l1).
assert (Hup2 := SEC_spec1 l2). assert (Hdown2 := @SEC_spec2 l2).
apply Rle_antisym.
- apply Hdown1. now rewrite Hperm.
- apply Hdown2. now rewrite <- Hperm.
Qed.

Lemma SEC_radius_pos : forall l, 0 <= radius (SEC l).
Proof.
intros [| pt ?].
+ now rewrite SEC_nil.
+ transitivity (dist pt (center (SEC (pt :: l)))).
  - apply dist_pos.
  - apply SEC_spec1. now left.
Qed.

(** Points on the SEC. *)
Definition on_SEC l := List.filter (on_circle (SEC l)) l.

Instance on_SEC_compat : Proper (PermutationA Logic.eq ==> PermutationA Logic.eq) on_SEC.
Proof.
intros l1 l2 Hl. unfold on_SEC. rewrite Hl at 2.
rewrite filter_extensionality_compat; try reflexivity.
intros ? ? ?. subst. now rewrite Hl.
Qed.

Lemma on_SEC_In : forall pt l, In pt (on_SEC l) <-> In pt l /\ on_circle (SEC l) pt = true.
Proof. intros. unfold on_SEC. apply filter_In. Qed.

(** ***  Results about the [SEC]  **)

(** ****  The radius of the SEC is the maximum distance between the center and any point in the list  **)

Definition max_dist pt l := List.fold_left (fun r x => Rmax r (dist x pt)) l 0%R.

Lemma max_dist_le_acc : forall pt l acc, acc <= List.fold_left (fun r x => Rmax r (dist x pt)) l acc.
Proof.
intros pt l. induction l as [| e l]; intro acc; simpl.
+ apply Rle_refl.
+ apply Rle_trans with (Rmax acc (dist e pt)).
  - apply Rmax_l.
  - apply IHl.
Qed.

Corollary max_dist_pos : forall pt l, 0 <= max_dist pt l.
Proof. intros. apply max_dist_le_acc. Qed.

Lemma max_dist_cons : forall pt x l, max_dist pt (x :: l) = Rmax (dist x pt) (max_dist pt l).
Proof.
intros. unfold max_dist. simpl. generalize 0%R. induction l; intro acc; simpl.
+ apply Rmax_comm.
+ rewrite <- IHl. f_equal. setoid_rewrite <- Rmax_assoc. f_equal. apply Rmax_comm.
Qed.

Lemma max_dist_le : forall pt x l, In x l -> dist x pt <= max_dist pt l.
Proof.
intros pt x l Hin.
unfold max_dist. generalize 0. induction l as [| e l]; intro acc; simpl.
* elim Hin.
* destruct Hin as [? | Hin]; subst.
  + apply Rle_trans with (Rmax acc (dist x pt)).
    - apply Rmax_r.
    - apply max_dist_le_acc.
  + now apply IHl.
Qed.

Lemma max_dist_exists : forall pt l, l <> nil -> exists x, In x l /\ dist x pt = max_dist pt l.
Proof.
intros pt l Hl. induction l as [| e1 l].
* now elim Hl.
* destruct l as [| e2 l].
  + exists e1. split; try now left. unfold max_dist. simpl. symmetry. apply Rmax_right.
    change (0 <= dist e1 pt). apply dist_pos.
  + destruct (Rle_dec (dist e1 pt) (max_dist pt (e2 :: l))).
    - destruct IHl as [x [Hin Heq]]; try discriminate; [].
      exists x. split; try now right. rewrite max_dist_cons, Heq. symmetry. now apply Rmax_right.
    - exists e1. split; try now left. rewrite max_dist_cons. symmetry.
      apply Rmax_left. apply Rlt_le. now apply Rnot_le_lt.
Qed.

Lemma radius_is_max_dist : forall l, radius (SEC l) = max_dist (center (SEC l)) l.
Proof.
intro l.
apply Rle_antisym.
+ pose (c := {| center := center (SEC l); radius := max_dist (center (SEC l)) l |}).
  assert (Hcircle : enclosing_circle c l). { unfold enclosing_circle. intros. now apply max_dist_le. }
  change (max_dist (center (SEC l)) l) with (radius c).
  now apply SEC_spec2.
+ destruct l as [| e l].
  - rewrite SEC_nil. compute; auto.
  - destruct (@max_dist_exists (center (SEC (e :: l))) (e :: l)) as [pt [Hin Heq]]; try discriminate; [].
    rewrite <- Heq. now apply SEC_spec1.
Qed.

Lemma max_dist_incl_compat : forall pt l1 l2, incl l1 l2 -> max_dist pt l1 <= max_dist pt l2.
Proof.
intros pt l1. induction l1; intros l2 Hincl.
+ cbn. apply max_dist_pos.
+ rewrite max_dist_cons. apply Rmax_lub.
  - apply max_dist_le. apply Hincl. now left.
  - apply IHl1. intros pt' Hin. apply Hincl. now right.
Qed.

(* If we add more points the radius of the SEC cannot decrease. *)
Lemma max_dist_enclosing : forall pt l, enclosing_circle {| center := pt; radius := max_dist pt l |} l.
Proof.
intros pt l. induction l as [| e l].
+ apply enclosing_circle_nil.
+ intros pt' Hin. simpl. inversion Hin.
  - subst. rewrite max_dist_cons. apply Rmax_l.
  - apply IHl in H. simpl in H. transitivity (max_dist pt l); trivial; [].
    rewrite max_dist_cons. apply Rmax_r.
Qed.

Lemma SEC_incl_compat : forall l1 l2, incl l1 l2 -> radius (SEC l1) <= radius (SEC l2).
Proof.
intros l1 l2 Hincl.
transitivity (max_dist (center (SEC l2)) l1).
- apply (SEC_spec2 (max_dist_enclosing (center (SEC l2)) l1)).
- rewrite radius_is_max_dist. now apply max_dist_incl_compat.
Qed.

(** There is at least one point on the [SEC]. *)
Lemma SEC_reached : forall l, l <> nil ->
  exists pt, In pt l /\ on_circle (SEC l) pt = true.
Proof.
intros. unfold on_circle. rewrite radius_is_max_dist.
setoid_rewrite Rdec_bool_true_iff. now apply max_dist_exists.
Qed.


Lemma max_dist_singleton: forall pt x, max_dist pt (x::nil) = dist x pt.
Proof.
  intros pt x.
  rewrite max_dist_cons.
  unfold max_dist. simpl fold_left. apply Rmax_left, dist_pos.
Qed.

Lemma enclosing_singleton : forall pt, enclosing_circle {| center := pt; radius := 0 |} (pt :: nil).
Proof.
  intros pt.
  red.
  intros pt' H.
  cbn.
  inversion H.
  - subst.
    destruct (dist_defined pt' pt').
    apply Req_le_sym.
    symmetry.
    apply H1.
    reflexivity.
  - inversion H0.
Qed.

(* TODO?
   Wrong with a general distance because of the coarse distance: d(x, y) = 1 <-> x <> y *)
Axiom SEC_unicity: forall l c,
    enclosing_circle c l
    -> (radius c <= radius (SEC l))%R
    -> c = SEC l.

Lemma SEC_singleton : forall pt, SEC (pt :: nil) = {| center := pt; radius := 0 |}.
Proof.
intro pt. symmetry. apply SEC_unicity.
- apply enclosing_singleton.
- simpl. rewrite radius_is_max_dist, max_dist_singleton. apply dist_pos.
Qed.

Opaque dist middle.
(* OK even when the points are the same *)
Lemma SEC_dueton : forall pt1 pt2,
  SEC (pt1 :: pt2 :: nil) = {| center := middle pt1 pt2; radius := /2 * dist pt1 pt2 |}.
Proof.
intros pt1 pt2. symmetry. apply SEC_unicity.
* intros pt Hin. simpl. inversion_clear Hin.
  + subst. now rewrite R2dist_middle.
  + inversion H; easy || subst. now rewrite middle_comm, R2dist_middle, dist_sym.
* simpl. rewrite <- R2dist_middle. rewrite radius_is_max_dist.
  pose (c := center (SEC (pt1 :: pt2 :: nil))). fold c. cbn.
  rewrite (Rmax_right 0); try apply dist_pos; [].
  rewrite <- pos_Rsqr_le.
  + cut ((dist pt1 (middle pt1 pt2))² + (dist pt1 (middle pt1 pt2))² <=
      (Rmax (dist pt1 c) (dist pt2 c))² + (Rmax (dist pt1 c) (dist pt2 c))²); try lra; [].
    transitivity ((dist pt1 c)² + (dist pt2 c)²).
    - assert (Heq : dist pt1 (middle pt1 pt2) = dist pt2 (middle pt1 pt2)).
      { now rewrite R2dist_middle, middle_comm, R2dist_middle, dist_sym. }
      rewrite Heq at 2. setoid_rewrite dist_sym. apply (middle_spec pt1 pt2 c).
    - apply Rplus_le_compat; rewrite pos_Rsqr_le;
      solve [apply Rmax_l | apply Rmax_r | apply dist_pos | apply Rmax_case; apply dist_pos].
  + apply dist_pos.
  + apply Rmax_case; apply dist_pos.
Qed.

(** ****  The [SEC] contains at least two points  **)

(** Idea of the proof:
    We already know that there is one point on the circle.
    If there is no other, we take the furthest point from c strictly inside the disk.
    We decrease the center and radius to make it end up on the circle.
    Thus, the original SEC was not minimal, a contradiction. *)

Function farthest_from_in_except (except c acc : R2) inl :=
match inl with
| nil => acc
| cons x inl' =>
  if equiv_dec x except then farthest_from_in_except except c acc inl'
  else if Rle_dec (dist x c) (dist c acc)
  then farthest_from_in_except except c acc inl' else farthest_from_in_except except c x inl'
end.

Lemma farthest_from_in_exc_In : forall except c acc inl,
    farthest_from_in_except except c acc inl = acc \/
    In (farthest_from_in_except except c acc inl) inl.
Proof.
intros except c acc inl.
functional induction (farthest_from_in_except except c acc inl);
try destruct IHr as [? | ?]; cbn; auto.
Qed.

Lemma farthest_from_in_except_In : forall exc c l, (exists pt, pt <> exc /\ In pt l) ->
  In (farthest_from_in_except exc c c l) l.
Proof.
intros exc c l Hl. induction l as [| e l].
* now elim Hl.
* cbn. destruct (equiv_dec e exc) as [Heq | Heq].
  + rewrite Heq in *. destruct l.
    - destruct Hl as [pt' [Habs Hin]]. elim Habs. now inversion Hin.
    - right. apply IHl. destruct Hl as [pt' [Hneq Hin]]. exists pt'. split; trivial.
      inversion Hin; subst; trivial; now elim Hneq.
  + destruct (Rle_dec (dist e c) (dist c c)) as [H | H].
    - assert (He : equiv e c).
      { rewrite <- dist_defined. transitivity (dist c c).
        + apply Rle_antisym; trivial.
          rewrite R2_dist_defined_2. apply dist_pos.
        + apply R2_dist_defined_2. }
      rewrite He. destruct (farthest_from_in_exc_In exc c c l); intuition.
    - destruct (farthest_from_in_exc_In exc c e l); intuition.
Qed.

Lemma farthest_from_in_except_diff : forall exc c acc l, acc <> exc -> farthest_from_in_except exc c acc l <> exc.
Proof.
intros exc c acc l. revert acc. induction l as [| e l]; intros acc Hdiff; cbn.
- assumption.
- destruct (equiv_dec e exc); auto.
  destruct (Rle_dec (dist e c) (dist c acc)); auto.
Qed.

Lemma farthest_from_in_except_le_acc : forall exc c l acc,
  dist c acc <= dist c (farthest_from_in_except exc c acc l).
Proof.
intros exc c l. induction l as [| e l]; intro acc; cbn.
+ apply Rle_refl.
+ destruct (equiv_dec e exc); auto.
  destruct (Rle_dec (dist e c) (dist c acc)) as [? | Hnle]; auto.
  apply Rnot_le_lt in Hnle. eapply Rle_trans.
  - apply Rlt_le. eassumption.
  - rewrite dist_sym. apply IHl.
Qed.

Lemma farthest_from_in_except_le : forall exc c l acc x,
  In x l -> x <> exc -> dist c x <= dist c (farthest_from_in_except exc c acc l).
Proof.
intros exc c l. induction l as [| e l]; intros acc x Hin Hneq.
* inversion Hin.
* inversion_clear Hin.
  + subst. clear IHl. cbn. destruct (equiv_dec x exc); try now cbn in *; contradiction.
    destruct (Rle_dec (dist x c) (dist c acc)) as [Hle | Hlt].
    - rewrite dist_sym. eapply Rle_trans; try eassumption. apply farthest_from_in_except_le_acc.
    - apply farthest_from_in_except_le_acc.
  + cbn. destruct (equiv_dec e exc); auto. destruct (Rle_dec (dist e c) (dist c acc)); auto.
Qed.

Lemma SEC_zero_radius_incl_singleton : forall l,
  radius (SEC l) = 0%R <-> exists pt, incl l (pt :: nil).
Proof.
intro l.
destruct l as [| e l].
* rewrite SEC_nil. intuition. exists (0, 0). intuition.
* split; intro H.
  + exists (center (SEC (e :: l))).
    intros x Hin. left. symmetry. change ( x == center (SEC (e :: l))).
    rewrite <- dist_defined. apply Rle_antisym.
    - rewrite <- H. now apply SEC_spec1.
    - apply dist_pos.
  + destruct H as [pt Hl].
    assert (Hall : forall x, In x (e :: l) -> x = pt). { intros ? Hin. apply Hl in Hin. now inversion_clear Hin. }
    clear Hl. apply Rle_antisym.
    - pose (c := {| center := pt; radius := 0 |}).
      change 0 with (radius c). apply SEC_spec2.
      intros x Hin. rewrite (Hall _ Hin). cbn. now rewrite R2_dist_defined_2.
    - transitivity (dist pt (center (SEC (e :: l)))).
      -- apply dist_pos.
      -- apply SEC_spec1. rewrite (Hall e ltac:(now left)). now left.
Qed.

Lemma SEC_reached_twice : forall l, (2 <= length l)%nat -> NoDup l ->
  exists pt1 pt2, In pt1 l /\ In pt2 l /\ pt1 <> pt2
    /\ on_circle (SEC l) pt1 = true /\ on_circle (SEC l) pt2 = true.
Proof.
intros l Hl Hnodup.
assert (Hnil : l <> nil). { destruct l; discriminate || simpl in Hl; omega. }
destruct (SEC_reached Hnil) as [pt1 [Hin1 Hon1]].
exists pt1.
(* Put [pt1] at the front of [l] to have easier manipulations. *)
assert (Hl' : exists l', Permutation l (pt1 :: l')).
{ rewrite <- InA_Leibniz in Hin1. apply (PermutationA_split _) in Hin1.
   setoid_rewrite PermutationA_Leibniz in Hin1. assumption. }
destruct Hl' as [l' Hl']. rewrite Hl' in *. setoid_rewrite Hl'. clear Hnil Hl' l.
simpl in Hl. apply le_S_n in Hl. rename l' into l.
destruct (Exists_dec (fun x => x <> pt1 /\ on_circle (SEC (pt1 :: l)) x = true)) with (pt1 :: l) as [HOK | Hsmall].
+ intro x. destruct (equiv_dec x pt1) as [Heq | Heq].
  - right. intuition.
  - destruct (on_circle (SEC (pt1 :: l)) x); intuition.
+ (* If there is another point on the circle *)
  rewrite Exists_exists in HOK. destruct HOK as [pt2 [Hin2 Heq2]].
  exists pt2; intuition.
+ (* If all other points are inside the circle, we can slightly reduce its radius by moving the center *)
  exfalso.
  pose (c := center (SEC (pt1 :: l))).
  pose (r := radius (SEC (pt1 :: l))).
  assert (Hr : r <> 0).
  { unfold r. rewrite SEC_zero_radius_incl_singleton. intros [pt Hincl].
    destruct l as [| pt2 ?]; simpl in Hl; try omega; [].
    inversion_clear Hnodup. apply H. left. transitivity pt.
    - specialize (Hincl pt2 ltac:(intuition)). simpl in Hincl. intuition.
    - specialize (Hincl pt1 ltac:(intuition)). simpl in Hincl. intuition. }
  (* pt2 := the farthest point of l from c (excluding pt1) *)
  pose (pt2 := farthest_from_in_except pt1 c c l).
  pose (d := dist c pt2). (* the maximum distance to c (except pt1) *)
  pose (r' := Rdiv (r + d) 2). (* the new radius *)
  pose (c' := (c + ((1 - r' / r) * (pt1 - c)))%R2). (* the new center *)
  assert (Hin2 : In pt2 l).
  { apply farthest_from_in_except_In. destruct l as [| e l].
    - cbn in Hl. omega.
    - inversion_clear Hnodup. cbn in H. exists e. intuition. }
  assert (Hmax : forall x, In x l -> x <> pt1 -> dist c x <= d).
  { intros. unfold d, pt2. now apply farthest_from_in_except_le. }
  assert (Hr2 : 0 < r). { apply Rle_neq_lt; auto. unfold r. apply SEC_radius_pos. }
  assert (Hr' : 0 <= r'). { assert (0 <= d). { unfold d. apply dist_pos. } unfold r'. lra. }
  (** The new circle has a smaller radius... *)
  assert (Hlt : r' < r).
  { unfold r'. cut (d < r); try lra; [].
    apply Rle_neq_lt.
    ++ unfold d, r, c. rewrite dist_sym. apply SEC_spec1. now right.
    ++ intro. do 2 subst. apply Hsmall. rewrite Exists_exists. exists pt2. repeat split.
       -- now right.
       -- clear -Hon1 Hnodup Hin2. unfold pt2. apply farthest_from_in_except_diff. intro Heq. subst c.
          (* BUG? subst without c does not work! *)
          rewrite <- Heq in Hon1 at 2. rewrite center_on_circle, SEC_zero_radius_incl_singleton in Hon1.
          destruct Hon1 as [pt Hincl].
          assert (pt = pt1). { specialize (Hincl pt1 ltac:(intuition)). simpl in Hincl. intuition. }
          assert (Hpt : pt = pt2). { specialize (Hincl pt2 ltac:(intuition)). simpl in Hincl. intuition. }
          subst pt. inversion_clear Hnodup. apply H. now rewrite Hpt.
       -- rewrite on_circle_true_iff. now rewrite dist_sym. }
  (** Yet, it is still enclosing, *)
  assert (Hnew : enclosing_circle {| center := c'; radius := r' |} (pt1 :: l)).
  { intros pt Hin. simpl center. simpl radius. destruct Hin.
    * subst pt. unfold c'. rewrite R2dist_ref_0.
      replace (pt1 - (c + (1 - r'/r) * (pt1 - c)))%R2 with (r'/ r * pt1 - (r' / r * c))%R2
        by (destruct pt1, c; cbn; f_equal; ring).
      rewrite <- R2dist_ref_0. rewrite R2mul_dist.
      rewrite on_circle_true_iff in Hon1. unfold c. rewrite Hon1.
      fold r. rewrite Rabs_pos_eq; [field_simplify; lra |].
      unfold Rdiv. now apply Fourier_util.Rle_mult_inv_pos.
    * transitivity (dist pt c + dist c c'); [| transitivity (d + dist c c')].
      + apply triang_ineq.
      + apply Rplus_le_compat_r. rewrite dist_sym. unfold d, pt2.
        apply farthest_from_in_except_le; trivial. intro. subst. inversion_clear Hnodup. contradiction.
      + unfold c'. rewrite R2dist_ref_0.
        replace (c - (c + (1 - r' / r) * (pt1 - c)))%R2 with ((1 - r' / r) * c - ((1 - r' / r) * pt1))%R2
          by (destruct pt1, c; cbn; f_equal; ring).
        rewrite <- R2dist_ref_0. rewrite R2mul_dist. rewrite on_circle_true_iff in Hon1.
        unfold c. rewrite dist_sym. rewrite Hon1. fold r.
        rewrite Rabs_pos_eq.
        - unfold r'. now field_simplify.
        - cut (r' / r <= 1); try lra. unfold Rdiv. rewrite <- (Rinv_r r); trivial. auto with real. }
  (** A contradiction. *)
  apply (Rle_not_lt r' r); trivial.
  unfold r. change r' with (radius {| center := c'; radius := r' |}).
  now apply SEC_spec2.
Qed.

(** ***  Results about [on_SEC]  **)

Lemma on_SEC_nil : forall l, on_SEC l = nil <-> l = nil.
Proof.
intro l. split; intro H.
- destruct l as [| e l]; trivial. exfalso.
  destruct (@SEC_reached (e :: l)) as [pt Hpt]; try discriminate.
  rewrite <- on_SEC_In in Hpt. rewrite H in Hpt. inversion Hpt.
- subst. cbn. reflexivity.
Qed.

Lemma on_SEC_singleton : forall pt, on_SEC (pt :: nil) = pt :: nil.
Proof.
intro. cbn. rewrite SEC_singleton. unfold on_circle. cbn. rewrite R2_dist_defined_2.
destruct (Rdec_bool 0 0) eqn:Htest; trivial. rewrite Rdec_bool_false_iff in Htest. now elim Htest.
Qed.

Lemma on_SEC_singleton_is_singleton : forall pt l, NoDup l -> on_SEC l = pt :: nil -> l = pt :: nil.
Proof.
intros pt l Hnodup Hfilter.
destruct l as [| pt1 [| pt2 l']] eqn:Hl.
  + cbn in *. assumption.
  + cbn in *. destruct (on_circle (SEC (pt1 :: nil)) pt1); trivial; discriminate.
  + destruct (@SEC_reached_twice (pt1 :: pt2 :: l'))
      as [pt_1 [pt_2 [Hpt_1 [Hpt_2 [Hdiff [H1 H2]]]]]].
    * simpl. omega.
    * rewrite <- Hl. now subst.
    * assert (In pt_1 (on_SEC (pt1 :: pt2 :: l'))). { unfold on_SEC. rewrite filter_In. now split. }
      assert (In pt_2 (on_SEC (pt1 :: pt2 :: l'))). { unfold on_SEC. rewrite filter_In. now split. }
      exfalso. apply Hdiff. rewrite Hfilter in *.
      repeat match goal with
             | H : In ?x nil  |- _ => inversion H
             | H : In ?x (?y :: nil) |- _ => inversion_clear H; auto
             end. now subst.
Qed.

Lemma on_SEC_dueton : forall pt1 pt2, on_SEC (pt1 :: pt2 :: nil) = pt1 :: pt2 :: nil.
Proof.
intros pt1 pt2. cbn. rewrite SEC_dueton. unfold on_circle. cbn.
destruct (Rdec_bool (dist pt1 (middle pt1 pt2)) (/ 2 * dist pt1 pt2)) eqn:Hpt1.
- destruct (Rdec_bool (dist pt2 (middle pt1 pt2)) (/ 2 * dist pt1 pt2)) eqn:Hpt2; trivial.
  exfalso.
  rewrite Rdec_bool_false_iff in Hpt2. apply Hpt2.
  setoid_rewrite dist_sym at 2. rewrite middle_comm. setoid_rewrite R2dist_ref_0.
  Local Transparent middle.
  unfold middle. rewrite <- (Rabs_pos_eq (/2)); try lra. rewrite <- R2mul_dist, mul_origin. f_equal.
  destruct pt1, pt2. compute. f_equal; field.
- exfalso.
  rewrite Rdec_bool_false_iff in Hpt1. apply Hpt1.
  setoid_rewrite R2dist_ref_0.
  unfold middle. rewrite <- (Rabs_pos_eq (/2)); try lra. rewrite <- R2mul_dist, mul_origin. f_equal.
  destruct pt1, pt2. compute. f_equal; field.
Qed.

Lemma enclosing_twice_same_SEC : forall l1 l2,
  enclosing_circle (SEC l1) l2 -> enclosing_circle (SEC l2) l1 -> SEC l1 = SEC l2.
Proof.
intros l1 l2 Hencl12 Hencl21. apply SEC_unicity.
- assumption.
- now apply SEC_spec2.
Qed.

Lemma SEC_min_radius : forall pt1 pt2 l, In pt1 l -> In pt2 l -> /2 * dist pt1 pt2 <= radius (SEC l).
Proof.
intros pt1 pt2 l Hpt1 Hpt2.
assert (Hperm : exists l', Permutation l (pt1 :: l')).
{ rewrite <- InA_Leibniz in Hpt1. setoid_rewrite <- PermutationA_Leibniz.
  apply PermutationA_split; autoclass. }
destruct Hperm as [l' Hperm]. rewrite Hperm in *. clear Hpt1 Hperm l.
destruct (equiv_dec pt1 pt2) as [Heq | Heq].
+ rewrite Heq. rewrite R2_dist_defined_2. replace (/2 * 0) with 0 by ring.
  rewrite radius_is_max_dist. apply max_dist_pos.
+ assert (Hperm : exists l, Permutation l' (pt2 :: l)).
  { rewrite <- InA_Leibniz in Hpt2. setoid_rewrite <- PermutationA_Leibniz.
    apply PermutationA_split; autoclass.
    inversion_clear Hpt2; trivial. subst. now elim Heq. }
  destruct Hperm as [l Hperm]. rewrite Hperm in *. clear Hpt2 Hperm l'.
  change (/2 * dist pt1 pt2) with (radius {| center := middle pt1 pt2; radius := /2 * dist pt1 pt2 |}).
  rewrite <- SEC_dueton. apply SEC_incl_compat. intro. cbn. intuition.
Qed.

Lemma SEC_add_same : forall pt l,
  dist pt (center (SEC l)) <= radius (SEC l) -> (SEC (pt :: l)) = SEC l.
Proof.
intros pt l H.
apply SEC_unicity.
- intro.
  intros H0.
  apply SEC_spec1.
  simpl.
  right;auto.
- apply SEC_spec2.
  intros x hin.
  simpl in hin.
  destruct hin; subst; trivial.
  now apply SEC_spec1.
Qed.

(* Actually, we have a strongler result stating that we can remove multiple copies of elements. *)
Lemma SEC_alls : forall pt n, (0 < n)%nat ->  SEC (alls pt n) = {| center := pt; radius := 0 |}.
Proof.
intros pt n Hn. induction n.
+ omega.
+ destruct n; simpl.
  - apply SEC_singleton.
  - rewrite SEC_add_same; auto with arith. apply SEC_spec1. now left.
Qed.

(* Given two the sec₁ = SEC l and sec₂ = SEC (pt :: l), we build a better SEC sec₃ for (pt :: l).  *)
Theorem on_SEC_critical_on_SEC: forall pt l,
  radius (SEC l) < radius (SEC (pt :: l)) -> InA equiv pt (on_SEC (pt :: l)).
Proof.
intros pt l Hlt.
pose (c₁ := center (SEC l)).
pose (r₁ := radius (SEC l)).
pose (c₂ := center (SEC (pt :: l))).
pose (r₂ := radius (SEC (pt :: l))).
fold r₁ r₂ in Hlt.
(* First eliminate the cases where l is empty or contains only copies of a single element. *)
assert (Hl : l = nil \/ (exists pt, l = alls pt (length l) /\ l <> nil)
          \/ exists pt1 pt2, pt1 <> pt2 /\ In pt1 l /\ In pt2 l).
{ clear. induction l as [| e l].
  * now left.
  * right.
    destruct IHl as [HL | [[pt [Hl Hnil]] | [pt1 [pt2 [Hneq [Hpt1 Hpt2]]]]]].
    + subst. left. simpl. exists e. split; trivial; discriminate.
    + destruct (equiv_dec e pt) as [Heq | Heq].
      - left. rewrite Heq. exists pt. simpl. now rewrite <- Hl.
      - right. exists pt, e. intuition.
        right. rewrite Hl. destruct l; simpl; intuition.
    + right. exists pt1, pt2. intuition. }
destruct Hl as [Hl | [[pt1 [Hl Hnil]] | [pt1 [pt2 [Hneq [Hpt1 Hpt2]]]]]].
* subst. rewrite on_SEC_singleton. now left.
* destruct (equiv_dec pt pt1) as [Heq | Heq].
  + rewrite Heq, Hl. change (pt1 :: alls pt1 (length l)) with (alls pt1 (S (length l))).
    unfold on_SEC. rewrite (filter_InA _), on_circle_true_iff, SEC_alls; try omega; []. split.
    - now left.
    - simpl. now rewrite dist_defined.
  + assert (Hsec : SEC (pt :: l) = {| center := middle pt pt1; radius := /2 * dist pt pt1 |}).
    { assert (Hlen : (length l <> 0)%nat) by auto using length_0.
      rewrite Hl. clear Hl Hnil.
      induction (length l) as [| [| n]].
      + now elim Hlen.
      + simpl. apply SEC_dueton.
      + assert (Hperm : Permutation (pt :: alls pt1 (S (S n))) (pt1 :: pt :: alls pt1 (S n)))
          by (simpl; constructor).
        rewrite Hperm. rewrite SEC_add_same.
        - apply IHn. discriminate.
        - apply SEC_spec1. now right; left. }
    unfold on_SEC. rewrite (filter_InA _), Hsec, on_circle_true_iff. simpl. split.
    - now left.
    - apply R2dist_middle.
* (* Now the real case, with at least two elements inside l. *)
  assert (Hlt_r₁ : 0 < r₁).
  { unfold r₁. apply Rle_neq_lt.
    + apply SEC_radius_pos.
    + intro Habs. symmetry in Habs. rewrite SEC_zero_radius_incl_singleton in Habs.
      destruct Habs as [pt' Hincl]. apply Hneq. transitivity pt'.
      - specialize (Hincl pt1 ltac:(intuition)). simpl in Hincl. intuition.
      - specialize (Hincl pt2 ltac:(intuition)). simpl in Hincl. intuition. }
  destruct (InA_dec equiv_dec pt (on_SEC (pt :: l))) as [? | Hout]; trivial; exfalso.
  (* As pt is not on the circle, its distance to the center is smaller than the radius. *)
  assert (Hlt_pt_2 : dist pt c₂ < r₂).
  { apply Rle_neq_lt.
    - apply SEC_spec1. now left.
    - intro Habs. apply Hout. unfold on_SEC. rewrite (filter_InA _).
      split; intuition. now rewrite on_circle_true_iff. }
  (* If all other points are inside a smaller SEC, we can find a better SEC *)
  destruct (equiv_dec c₂ c₁) as [Heq_c | Heq_c].
  + (* Both centers are the same: we can have a better circle than the SEC with radius [dist pt c]. *)
    pose (r₃ := Rmax (dist pt c₂) (radius (SEC l))). (* the new radius *)
    pose (circ := {| center := c₂; radius := r₃ |}). (* the better circle *)
    apply (Rlt_irrefl r₃). apply Rlt_le_trans with r₂.
    - unfold r₃. now apply Rmax_lub_lt.
    - change r₃ with (radius circ). unfold r₂. apply SEC_spec2.
      intros pt' Hin. destruct Hin.
      ++ subst pt'. unfold circ, r₃. simpl. apply Rmax_l.
      ++ unfold circ, r₃. simpl. transitivity r₁.
         -- rewrite Heq_c. now apply SEC_spec1.
         -- apply Rmax_r.
  + (* Both centers are different, we move the center c₂ to get a better SEC. *)
    destruct (equiv_dec pt c₂) as [Heq | ?].
    - (* if pt = c₂, we take c₃ = c₁ and r₃ = dist c₁ c₂. *)
      pose (r₃ := dist c₂ c₁).
      assert (Hlt_r₃_r₂ : r₁ < r₃ < r₂).
      { unfold r₃. split.
        + apply Rnot_le_lt. rewrite <- Heq. intro Habs. apply SEC_add_same in Habs.
          unfold r₂ in Hlt. rewrite Habs in Hlt. apply (Rlt_irrefl _ Hlt).
        + admit. }
      assert (enclosing_circle {| center := c₁; radius := r₃ |} (pt :: l)).
      { intros pt' Hin. simpl. destruct Hin.
        + subst pt'. unfold r₃. rewrite Heq. reflexivity.
        + transitivity r₁.
          - now apply SEC_spec1.
          - now apply Rlt_le. }
      (* A contradiction *)
      apply (Rle_not_lt r₃ r₂); try easy; [].
      unfold r₂. change r₃ with (radius {| center := c₁; radius := r₃ |}).
      now apply SEC_spec2.
    - (* Otherwise, we move by [ε/2] on the line [pt c]. *)
      pose (d := dist pt c₂).
      pose (ε := r₂ - d). (* the room we have *)
      pose (r₃ := (r₂ + d) / 2). (* the new radius *)
      pose (ratio := ε / (2 * d)).
      pose (c₃ := (c₂ - (ratio * (pt - c₂)))%R2). (* the new center *)
      assert (Hr₃ : r₃ = d + ε / 2) by (unfold ε, r₃; field).
      assert (Hr : r₂ <> 0).
      { unfold r₂. rewrite SEC_zero_radius_incl_singleton. intros [pt' Hincl].
        apply Hneq. transitivity pt'.
        - specialize (Hincl pt1 ltac:(intuition)). simpl in Hincl. intuition.
        - specialize (Hincl pt2 ltac:(intuition)). simpl in Hincl. intuition. }
      assert (Hle_d : 0 <= d) by apply dist_pos.
      assert (Hlt_d : 0 < d).
      { apply Rle_neq_lt; trivial. unfold d. intro Habs. symmetry in Habs.
        rewrite dist_defined in Habs. contradiction. }
      assert (Hlt_r₂ : 0 < r₂). { apply Rle_neq_lt; auto. unfold r₂. apply SEC_radius_pos. }
      assert (Hlt_r₃ : 0 < r₃) by (unfold r₃; lra).
        assert (Hle_r₃ : 0 <= r₃) by lra.
      (* The new circle has a smaller radius *)
      assert (Hlt_d_r : d < r₂).
      { apply Rle_neq_lt.
        ++ unfold d, r₂, c₂. apply SEC_spec1. now left.
          ++ unfold d, r₂, c₂. rewrite <- on_circle_true_iff. intro Habs.
           apply Hout. unfold on_SEC. rewrite (filter_InA _). intuition. }
      assert (Hlt_r₃_r₂ : r₃ < r₂) by (unfold r₃; lra).
      (* Yet, it is still enclosing *)
      assert (Hlt_ε : 0 < ε) by (unfold ε; lra).
      assert (Hratio_pos : 0 < ratio).
      { unfold ratio, Rdiv.
        apply Rle_neq_lt.
        - apply Fourier_util.Rle_mult_inv_pos; lra.
        - unfold Rdiv. intro Habs. symmetry in Habs. apply Rmult_integral in Habs.
          assert (Hlt_inv_d := Rinv_0_lt_compat _ Hlt_d).
          destruct Habs as [? | Habs]; lra || rewrite Rinv_mult_distr in Habs; lra. }
        assert (Hdist : dist c₂ c₃ = ε / 2).
        { unfold c₃, ratio. rewrite <- add_origin at 1. setoid_rewrite add_comm.
          rewrite R2add_dist, dist_sym. rewrite R2norm_dist, opp_origin, add_origin.
          rewrite R2norm_opp, R2norm_mul, Rabs_pos_eq.
          - rewrite <- R2norm_dist. fold d. field. lra.
          - apply Fourier_util.Rle_mult_inv_pos; lra. }
      (* Yet, it is still enclosing *)
      assert (Hnew : enclosing_circle {| center := c₃; radius := r₃ |} (pt :: l)).
      { intros pt' Hin. cbn. destruct Hin.
        * subst pt'. transitivity (dist pt c₂ + dist c₂ c₃).
          + apply triang_ineq.
          + rewrite Hdist. fold d. rewrite Hr₃. reflexivity.
        * admit. }
      (* A contradiction *)
      apply (Rle_not_lt r₃ r₂); trivial.
      unfold r₂. change r₃ with (radius {| center := c₃; radius := r₃ |}).
      now apply SEC_spec2.
Admitted.

Lemma SEC_add_same' : forall pt l,
  dist pt (center (SEC (pt::l))) < radius (SEC (pt::l)) -> (SEC (pt :: l)) = SEC l.
Proof.
intros pt l H.
apply SEC_unicity.
+ intros ? ?. apply SEC_spec1. now right.
+ apply Rnot_lt_le. intro abs.
  absurd (InA equiv pt (on_SEC (pt::l))).
  - rewrite InA_Leibniz, on_SEC_In.
    intros [_ Hcirc].
    apply on_circle_true_iff in Hcirc.
    lra.
  - now apply on_SEC_critical_on_SEC.
Qed.


Lemma on_SEC_add_same : forall pt l, dist pt (center (SEC l)) < radius (SEC l) ->
  equivlistA equiv (on_SEC (pt :: l)) (on_SEC l).
Proof.
intros pt l H x.
unfold on_SEC. setoid_rewrite (filter_InA _). rewrite SEC_add_same.
- split; intros [Hin Hcircle]; split; trivial.
  + inversion_clear Hin; trivial.
    unfold on_circle in Hcircle. rewrite Rdec_bool_true_iff, H0 in Hcircle.
    rewrite Hcircle in H. lra.
  + now right.
- now left.
Qed.

Lemma SEC_append_same : forall l1 l2, (forall pt, In pt l1 -> dist pt (center (SEC l2)) <= radius (SEC l2))
               -> SEC (l1 ++ l2) = SEC l2.
Proof.
intros l1 l2 Hl1. induction l1.
- reflexivity.
- cbn.
  assert (Hrec : forall pt : R2, In pt l1 -> dist pt (center (SEC l2)) <= radius (SEC l2)).
  { intros pt Hin. apply Hl1. now right. }
  specialize (IHl1 Hrec). rewrite <- IHl1.
  apply SEC_add_same. rewrite IHl1. apply Hl1. now left.
Qed.

Lemma SEC_append_same' : forall l1 l2,
    (forall pt, In pt l1 -> dist pt (center (SEC (l1++l2))) < radius (SEC (l1++l2)))
    -> SEC (l1 ++ l2) = SEC l2.
Proof.
  intros l1 l2 Hl1. induction l1.
- reflexivity.
- cbn.
  setoid_rewrite <- IHl1.
  + apply SEC_add_same'. apply Hl1. now left.
  + intros pt Hin.
    assert (hinpt : In pt (a::l1)).
    { right.
      assumption. }
    assert (hpt:=Hl1 pt hinpt).
    assert (hina : In a (a::l1)).
    { left.
      reflexivity. }
    assert (ha:=Hl1 a hina).
    clear Hl1 hinpt hina.
    assert (h:=SEC_add_same' a (l1 ++ l2) ha).
    setoid_rewrite <- h.
    assumption.
Qed.

Lemma middle_in_SEC_diameter : forall pt1 pt2,
  dist (middle pt1 pt2) (center (SEC (pt1 :: pt2 :: nil))) <= radius (SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2.
rewrite SEC_dueton. cbn.
rewrite R2_dist_defined_2, <- (Rmult_0_l 0).
apply Rmult_le_compat; try lra; [].
apply dist_pos.
Qed.

Lemma middle_strictly_in_SEC_diameter : forall pt1 pt2, pt1 <> pt2 ->
  dist (middle pt1 pt2) (center (SEC (pt1 :: pt2 :: nil))) < radius (SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2 Hdiff.
assert (Hle := middle_in_SEC_diameter pt1 pt2). destruct Hle as [Hlt | Heq]; trivial.
rewrite SEC_dueton in Heq. simpl in Heq. rewrite R2_dist_defined_2 in Heq.
assert (Hsame : dist pt1 pt2 = 0) by lra. now rewrite dist_defined in Hsame.
Qed.

Lemma SEC_middle_diameter : forall pt1 pt2, SEC (middle pt1 pt2 :: pt1 :: pt2 :: nil) = SEC (pt1 :: pt2 :: nil).
Proof. intros. apply SEC_add_same, middle_in_SEC_diameter. Qed.

(* Require Pactole.MMultiset.Preliminary. *)
Lemma on_SEC_NoDupA : forall l, NoDupA equiv l -> NoDupA equiv (on_SEC l).
Proof. intros. unfold on_SEC. now apply (Util.Preliminary.NoDupA_filter_compat _). Qed.

Lemma on_SEC_middle_diameter : forall pt1 pt2, ~pt1 == pt2 ->
  PermutationA equiv (on_SEC (middle pt1 pt2 :: pt1 :: pt2 :: nil)) (on_SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2 Hdiff.
assert (~middle pt1 pt2 == pt1). { rewrite <- middle_eq in Hdiff. intuition. }
assert (~middle pt1 pt2 == pt2).
{ assert (Hdiff' : ~pt2 == pt1) by intuition. rewrite <- middle_eq in Hdiff'. rewrite middle_comm. intuition. }
apply (NoDupA_equivlistA_PermutationA _).
- apply on_SEC_NoDupA. repeat constructor; intro Hin; inversion_clear Hin; intuition;
  inversion_clear H1; intuition; inversion_clear H2.
- apply on_SEC_NoDupA. repeat constructor; intro Hin; inversion_clear Hin; intuition; inversion_clear H1.
- now apply on_SEC_add_same, middle_strictly_in_SEC_diameter.
Qed.

Lemma filter_idempotent {A} : forall f (l : list A), filter f (filter f l) = filter f l.
Proof.
intros f l. induction l as [| e l].
- reflexivity.
- cbn. destruct (f e) eqn:Hfe; cbn; try rewrite Hfe; now (f_equal + idtac).
Qed.

Lemma on_SEC_is_max_dist : forall l pt pt', In pt l -> In pt' (on_SEC l) ->
  dist pt (center (SEC l)) <= dist pt' (center (SEC l)).
Proof.
intros l pt pt' Hin Hin'. unfold on_SEC in Hin'.
rewrite <- InA_Leibniz, (filter_InA _), on_circle_true_iff in Hin'.
destruct Hin' as [_ Hin']. rewrite Hin'. now apply SEC_spec1.
Qed.

Lemma split_on_SEC: forall l,
  PermutationA equiv l ((on_SEC l)++filter (fun x => negb (on_circle (SEC l) x)) l).
Proof.
intros l. unfold on_SEC.
change (on_circle (SEC l)) with (fun x : R2 => (on_circle (SEC l) x)).
rewrite <- (map_id (filter (fun x : R2 => on_circle (SEC l) x) l)).
rewrite <- (map_id (filter (fun x : R2 => negb (on_circle (SEC l) x)) l)).
rewrite PermutationA_Leibniz, <- map_cond_Permutation.
rewrite (map_ext (fun x : R2 => if on_circle (SEC l) x then x else x) (fun x => x)).
- now rewrite map_id.
- intro. now destruct_match.
Qed.

Lemma SEC_on_SEC : forall l,  SEC l = SEC (on_SEC l) .
Proof.
intros l.
rewrite (split_on_SEC l) at 1.
rewrite PermutationA_app_comm;autoclass.
apply SEC_append_same'.
intros pt H.
apply Rle_neq_lt.
- apply SEC_spec1, in_or_app. now left.
- apply filter_In in H. destruct H as [? H'].
  rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, on_circle_true_iff in H'.
  rewrite PermutationA_app_comm, <- split_on_SEC; autoclass.
Qed.

Corollary on_SEC_idempotent : forall l, PermutationA equiv (on_SEC (on_SEC l)) (on_SEC l).
Proof. intro l. unfold on_SEC at 1 3. unfold on_SEC at 2. rewrite (SEC_on_SEC l). now rewrite filter_twice. Qed.

Lemma on_SEC_pair_is_diameter : forall pt1 pt2 l, on_SEC l = pt1 :: pt2 :: nil ->
  SEC l = {| center := middle pt1 pt2; radius := /2 * dist pt1 pt2 |}.
Proof. intros pt1 pt2 l Hsec. rewrite SEC_on_SEC, Hsec. apply SEC_dueton. Qed.


Lemma enclosing_same_on_SEC_is_same_SEC : forall l1 l2,
  enclosing_circle (SEC l2) l1 ->
  (forall pt, In pt (on_SEC l2) -> In pt l1) ->
  SEC l1 = SEC l2.
Proof.
intros l1 l2 Hencl Hincl.
symmetry. apply SEC_unicity; trivial.
rewrite (SEC_on_SEC l2). apply SEC_spec2.
intros pt Hin. apply Hincl in Hin. now apply SEC_spec1.
Qed.

(** **  Results about barycenters, SEC and triangles  **)

Lemma barycenter_3_pts_inside_SEC : forall pt1 pt2 pt3,
  dist (barycenter_3_pts pt1 pt2 pt3) (center (SEC (pt1 :: pt2 :: pt3 :: nil)))
  <= radius (SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof.
intros pt1 pt2 pt3. unfold barycenter_3_pts. do 2 rewrite mul_distr_add.
remember (center (SEC (pt1 :: pt2 :: pt3 :: nil))) as c.
transitivity (dist (/3 * pt1)%R2 (/3 * c)%R2 + dist (/3 * pt2)%R2 (/3 * c)%R2 + dist (/3 * pt3)%R2 (/3 * c)%R2).
+ replace c with (/3 * c + (/3 * c + /3 * c))%R2 at 1.
  - etransitivity. apply R2dist_subadditive. rewrite Rplus_assoc.
    apply Rplus_le_compat; try reflexivity. apply R2dist_subadditive.
  - clear Heqc. destruct c. compute. f_equal; field.
+ repeat rewrite R2mul_dist; try lra; [].
  rewrite (Rabs_pos_eq (/3) ltac:(lra)).
  remember (radius (SEC (pt1 :: pt2 :: pt3 :: nil))) as r.
  replace r with (/3 * r + /3 * r + /3 * r) by field.
  repeat apply Rplus_le_compat; (apply Rmult_le_compat; try lra || apply dist_pos; []);
  subst; apply SEC_spec1; intuition.
Qed.

Lemma triangle_barycenter_inside_aux : forall pt1 pt2,
  pt1 <> pt2 -> on_circle (SEC (pt1 :: pt1 :: pt2 :: nil)) (barycenter_3_pts pt1 pt1 pt2) = false.
Proof.
intros pt1 pt2 Hneq.
rewrite SEC_add_same.
- rewrite SEC_dueton. apply Bool.not_true_iff_false. rewrite on_circle_true_iff. simpl.
  rewrite square_dist_equiv; try (now assert (Hle := dist_pos pt1 pt2); lra); [].
  unfold barycenter_3_pts, middle. rewrite square_dist_simpl, R_sqr.Rsqr_mult, square_dist_simpl.
  intro Habs. apply Hneq. destruct pt1, pt2; simpl in Habs. unfold Rsqr in Habs. field_simplify in Habs.
  pose (x := (r² + r1² - 2 * r * r1) + (r0² + r2² - 2 * r0 * r2)).
  assert (Heq0 : x = 0). { unfold x. unfold Rsqr in *. field_simplify in Habs. field_simplify. lra. }
  clear Habs. unfold x in *. clear x. do 2 rewrite <- R_sqr.Rsqr_minus in Heq0.
  apply Rplus_eq_R0 in Heq0; try apply Rle_0_sqr; []. unfold Rsqr in Heq0. destruct Heq0 as [Heq0 Heq0'].
  apply Rsqr_0_uniq in Heq0. apply Rsqr_0_uniq in Heq0'. f_equal; lra.
- apply SEC_spec1. intuition.
Qed.

Lemma triangle_barycenter_inside : forall pt1 pt2 pt3,
  ~(pt1 = pt2 /\ pt1 = pt3) -> on_circle (SEC (pt1 :: pt2 :: pt3 :: nil)) (barycenter_3_pts pt1 pt2 pt3) = false.
Proof.
intros pt1 pt2 pt3 Hneq.
(* if there are only two different points, we use triangle_barycenter_inside_aux. *)
destruct (equiv_dec pt1 pt2) as [Heq12 | Heq12];
[| destruct (equiv_dec pt1 pt3) as [Heq13 | Heq13]; [| destruct (equiv_dec pt2 pt3) as [Heq23 | Heq23]]].
* assert (Hneq12 : pt1 <> pt3) by now intro; subst; auto. rewrite <- Heq12.
  now apply triangle_barycenter_inside_aux.
* rewrite <- Heq13.
  assert (Hperm : Permutation (pt1 :: pt2 :: pt1 :: nil) (pt1 :: pt1 :: pt2 :: nil)) by do 2 constructor.
  rewrite Hperm. rewrite (barycenter_3_pts_compat Hperm). apply triangle_barycenter_inside_aux. auto.
* rewrite <- Heq23.
  assert (Hperm : Permutation (pt1 :: pt2 :: pt2 :: nil) (pt2 :: pt2 :: pt1 :: nil)) by now do 3 econstructor.
  rewrite Hperm. rewrite (barycenter_3_pts_compat Hperm). apply triangle_barycenter_inside_aux. auto.
* (* All three points are different, we consider the size of on_SEC *)
  assert (Hnodup : NoDup (pt1 :: pt2 :: pt3 :: nil)) by (repeat constructor; simpl in *; intuition).
  destruct (on_SEC (pt1 :: pt2 :: pt3 :: nil)) as [| pt1' [| pt2' [| pt3' [| ? ?]]]] eqn:Hsec.
  + rewrite on_SEC_nil in Hsec. discriminate.
  + apply on_SEC_singleton_is_singleton in Hsec; trivial. discriminate.
  + (* 2 points on SEC, hence a diameter [pt1' pt2'] with middle c. Let pt3' be the last point.
       Then barycenter pt1 pt2 pt3 - c = 1/3 (pt3' - c).
       If pt3' = c then bary = c and d(bary, c) = 0 <> radius.
       Otherwise, d(bary, c) = 1/3 dist(pt3', c) <> radius = dist(pt3', c). *)
    assert (Hincl : incl (pt1' :: pt2' :: nil) (pt1 :: pt2 :: pt3 :: nil)).
    { intro. rewrite <- Hsec. unfold on_SEC. rewrite filter_In. intuition. }
    assert (Hdiff' : ~equiv pt1' pt2').
    { assert (Hnodup' : NoDupA equiv (pt1' :: pt2' :: nil)).
      { rewrite <- Hsec. apply on_SEC_NoDupA. now rewrite NoDupA_Leibniz. }
    rewrite NoDupA_Leibniz in Hnodup'. inversion_clear Hnodup'. clear Hsec. cbn in *. intro. subst. intuition. }
    assert (Hpair := on_SEC_pair_is_diameter _ Hsec). rewrite Hpair. apply Bool.not_true_iff_false.
    rewrite on_circle_true_iff. simpl radius.
    change (center {| center := middle pt1' pt2'; radius := / 2 * dist pt1' pt2' |}) with (middle pt1' pt2').
    (* Define pt3'. *)
    assert (Hpt3' : exists pt3', Permutation (pt1' :: pt2' :: pt3' :: nil) (pt1 :: pt2 :: pt3 :: nil)).
    { assert (Hpt1' := Hincl pt1' ltac:(intuition)).
      assert (Hpt2' := Hincl pt2' ltac:(intuition)).
      simpl in Hpt1', Hpt2'. decompose [or] Hpt1'; decompose [or] Hpt2'; clear Hpt1' Hpt2'; repeat subst;
      try match goal with
        | H : False |- _ => elim H
        | H : ~equiv ?x ?x |- _ => elim H; reflexivity
      end.
      - exists pt3. do 4 constructor.
      - exists pt2. do 4 constructor.
      - exists pt3. do 4 constructor.
      - exists pt1. do 4 econstructor.
      - exists pt2. now do 3 econstructor.
      - exists pt1. now do 4 econstructor. }
    destruct Hpt3' as [pt3' Hperm].
    rewrite <- (barycenter_3_pts_compat Hperm).
    rewrite R2norm_dist. unfold barycenter_3_pts, middle.
    destruct (equiv_dec pt3' (1/2 * (pt1' + pt2')))%R2 as [Heq | Heq].
    - assert (Hzero : (/3 * (pt1' + (pt2' + pt3')) - 1/2 * (pt1' + pt2') = origin)%R2).
      { rewrite Heq. destruct pt1', pt2'. simpl. f_equal; field. }
      rewrite Hzero. rewrite R2norm_origin. apply not_eq_sym. erewrite <- Rmult_0_r.
      intro Habs. rewrite <- dist_defined in Hdiff'. apply Rmult_eq_reg_l in Habs; lra.
    - replace ((/ 3 * (pt1' + (pt2' + pt3')) - 1 / 2 * (pt1' + pt2')))%R2
        with (/3 *(pt3' - 1 / 2 * (pt1' + pt2')))%R2.
      -- rewrite R2norm_mul. rewrite Rabs_pos_eq; try lra; [].
         rewrite <- R2norm_dist.
         assert (Hpt3' : dist pt3' (center (SEC (pt1 :: pt2 :: pt3 :: nil)))
                         <= radius (SEC (pt1 :: pt2 :: pt3 :: nil))).
         { apply SEC_spec1. rewrite <- Hperm. intuition. }
         rewrite Hpair in Hpt3'. simpl radius in Hpt3'. unfold center in Hpt3'. fold (middle pt1' pt2').
         apply Rlt_not_eq. eapply Rlt_le_trans; try eassumption; [].
         change (~pt3' == (1 / 2 * (pt1' + pt2'))%R2) in Heq.
         rewrite <- dist_defined in Heq. setoid_rewrite <- Rmult_1_l at 9.
         apply Rmult_lt_compat_r; lra || apply Rle_neq_lt; auto using dist_pos.
      -- destruct pt1', pt2', pt3'. simpl. f_equal; field.
  + (* let c be the center of the SEC and r its radius.
       If bary is on the circle, the triangular inequality 3 * d(bary, c) <= d(pt1, c) + d(pt2, c) + d(pt3, c)
       is actually an equality.  Therefore, these three vectors are colinear and of same length (circle).
       As one end is always c, two points must be the same, a contradiction. *)
    assert (Hperm : Permutation (pt1' :: pt2' :: pt3' :: nil) (pt1 :: pt2 :: pt3 :: nil)).
    { rewrite <- PermutationA_Leibniz. rewrite <- NoDupA_Leibniz in Hnodup.
      apply (NoDupA_inclA_length_PermutationA _); trivial.
      - rewrite <- Hsec. now apply on_SEC_NoDupA.
      - rewrite <- Hsec. unfold on_SEC. intros ? Hin. now rewrite (filter_InA _) in Hin. }
    rewrite <- Hsec in Hperm. apply Bool.not_true_is_false. rewrite on_circle_true_iff.
    pose (c := center (SEC (pt1 :: pt2 :: pt3 :: nil))).
    pose (r := radius (SEC (pt1 :: pt2 :: pt3 :: nil))).
    fold r c.
    (* pt1, pt2, pt3 are on the circle, so d(ptX, c) = r. *)
    assert (Hpt1 : dist pt1 c = r).
    { unfold c, r. rewrite <- on_circle_true_iff. eapply proj2. rewrite <- filter_In.
      unfold on_SEC in Hperm. rewrite Hperm. now left. }
    assert (Hpt2 : dist pt2 c = r).
    { unfold c, r. rewrite <- on_circle_true_iff. eapply proj2. rewrite <- filter_In.
      unfold on_SEC in Hperm. rewrite Hperm. now right; left. }
    assert (Hpt3 : dist pt3 c = r).
    { unfold c, r. rewrite <- on_circle_true_iff. eapply proj2. rewrite <- filter_In.
      unfold on_SEC in Hperm. rewrite Hperm. now right; right; left. }
    (* Modifyng goal to have the right shape for the equality case of the triangular inequality. *)
    replace c with (/3 * (c + c + c))%R2 by (destruct c; simpl; f_equal; field).
    unfold barycenter_3_pts. rewrite R2mul_dist, Rabs_pos_eq; try lra; [].
    replace r with (/3 * (r + r + r)) by field.
    intro Habs. apply Rmult_eq_reg_l in Habs; try lra; [].
    (* We use the triangular equality to get colinearity results. *)
    destruct (triang_ineq_eq3 (c + c + c) (pt1 + c + c) (pt1 + pt2 + c) (pt1 + pt2 + pt3))%R2 as [Hcol1 Hcol2].
    - rewrite add_assoc, dist_sym in Habs. rewrite Habs.
      repeat rewrite R2add_dist. setoid_rewrite add_comm.
      repeat rewrite R2add_dist. setoid_rewrite dist_sym.
      now rewrite Hpt1, Hpt2, Hpt3.
    - replace (pt1 + c + c - (c + c + c))%R2 with (pt1 - c)%R2 in * by (destruct pt1, c; simpl; f_equal; field).
      replace (pt1 + pt2 + c - (c + c + c))%R2 with (pt1 - c + (pt2 - c))%R2 in Hcol1
        by (destruct pt1, pt2, c; simpl; f_equal; field).
      replace (pt1 + pt2 + pt3 - (c + c + c))%R2 with (pt1 - c + ((pt2 - c) + (pt3 - c)))%R2 in Hcol2
        by (destruct pt1, pt2, pt3, c; simpl; f_equal; field).
      (* The radius is not zero, otherwise all points would be the center, a contradiction. *)
      assert (Hr : r <> 0).
      { intro Hr. rewrite Hr in *. apply Heq12. transitivity c.
        - now rewrite <- dist_defined.
        - now rewrite <- dist_defined, dist_sym. }
      assert (Hc_pt1 : ~equiv pt1 c) by now rewrite <- dist_defined, Hpt1.
      assert (Hc_pt2 : ~equiv pt2 c) by now rewrite <- dist_defined, Hpt2.
      (* Simplify the colinearity results. *)
      symmetry in Hcol2. rewrite colinear_add in Hcol1, Hcol2.
      rewrite <- R2sub_origin in Hc_pt1, Hc_pt2.
      assert (Hcol3 : colinear (pt1 - c) (pt3 - c)).
      { apply colinear_trans with (pt2 - c)%R2; trivial. rewrite <- colinear_add.
        apply colinear_trans with (pt1 - c)%R2; trivial. now symmetry. }
      apply colinear_decompose in Hcol1; trivial; [].
      apply colinear_decompose in Hcol3; trivial; [].
      assert (Heq_pt1 := unitary_id (pt1 - c)%R2).
      repeat rewrite <- ?R2norm_dist, ?Hpt1, ?Hpt2, ?Hpt3 in *.
      (* Use the expression of colinearity by two possible equality. *)
      destruct Hcol1 as [Hcol1 | Hcol1], Hcol3 as [Hcol3 | Hcol3];
      apply Heq12 + apply Heq13 + apply Heq23; apply add_reg_r with (- c)%R2; congruence.
  + assert (Hle : (length (on_SEC (pt1 :: pt2 :: pt3 :: nil)) <= 3)%nat).
    { unfold on_SEC. rewrite filter_length. simpl length at 1. omega. }
    rewrite Hsec in Hle. simpl in Hle. omega.
Qed.

Lemma barycenter_3_pts_strictly_inside_SEC : forall pt1 pt2 pt3, ~(pt1 = pt2 /\ pt1 = pt3) ->
  dist (barycenter_3_pts pt1 pt2 pt3) (center (SEC (pt1 :: pt2 :: pt3 :: nil)))
  < radius (SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof.
intros pt1 pt2 pt3 Hdiff.
assert (Hle := barycenter_3_pts_inside_SEC pt1 pt2 pt3).
destruct Hle as [? | Heq]; trivial.
assert (Hcircle : on_circle (SEC (pt1 :: pt2 :: pt3 :: nil)) (barycenter_3_pts pt1 pt2 pt3) = false).
{ destruct (equiv_dec pt1 pt2).
  - assert (Hperm : PermutationA equiv (pt1 :: pt2 :: pt3 :: nil) (pt1 :: pt3 :: pt2 :: nil)).
    { now repeat constructor. }
    rewrite Hperm. rewrite PermutationA_Leibniz in Hperm. rewrite (barycenter_3_pts_compat Hperm).
    apply triangle_barycenter_inside. intro. intuition.
  - now apply triangle_barycenter_inside. }
unfold on_circle in Hcircle. rewrite Rdec_bool_false_iff in Hcircle. contradiction.
Qed.

Lemma on_SEC_barycenter_triangle : forall pt1 pt2 pt3, ~(pt1 = pt2 /\ pt1 = pt3) ->
  equivlistA equiv (on_SEC (barycenter_3_pts pt1 pt2 pt3 :: pt1 :: pt2 :: pt3 :: nil))
                   (on_SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof. intros. now apply on_SEC_add_same, barycenter_3_pts_strictly_inside_SEC. Qed.

Axiom equilateral_SEC : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Equilateral ->
  SEC (pt1 :: pt2 :: pt3 :: nil) =
  {| center := barycenter_3_pts pt1 pt2 pt3;
     radius := dist (barycenter_3_pts pt1 pt2 pt3) pt1 |}.

Lemma equilateral_barycenter_not_eq : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Equilateral -> ~pt1 == pt2 -> ~barycenter_3_pts pt1 pt2 pt3 == pt1.
Proof.
intros pt1 pt2 pt3 Htriangle Hneq.
assert (Hcenter : center (SEC (pt1 :: pt2 :: pt3 :: nil)) = barycenter_3_pts pt1 pt2 pt3).
{ apply equilateral_SEC in Htriangle. now rewrite Htriangle. }
assert (Hradius : radius (SEC (pt1 :: pt2 :: pt3 :: nil)) = dist (barycenter_3_pts pt1 pt2 pt3) pt1).
{ apply equilateral_SEC in Htriangle. now rewrite Htriangle. }
rewrite <- dist_defined. rewrite <- Hradius, <- center_on_circle.
rewrite Hcenter. now rewrite triangle_barycenter_inside.
Qed.

Lemma equilateral_NoDupA : forall ptx pty ptz,
  classify_triangle ptx pty ptz = Equilateral -> ptx <> pty ->
  NoDupA equiv (ptx :: pty :: ptz :: nil).
Proof.
intros ptx pty ptz Htriangle Hdiff.
functional induction (classify_triangle ptx pty ptz) as [Heq1 Heq2 | | | |]; try discriminate.
rewrite Rdec_bool_true_iff in *. repeat constructor; intro Hin;
repeat match goal with
  | H : equiv _ _ |- _ => rewrite H in *
  | H : InA _ _ _ |- _ => inversion_clear H
end.
- now elim Hdiff.
- rewrite R2_dist_defined_2 in *. symmetry in Heq2. rewrite dist_defined in Heq2. now symmetry in Heq2.
- rewrite R2_dist_defined_2 in *. now rewrite dist_defined in Heq1.
Qed.

Lemma equilateral_barycenter_NoDupA : forall ptx pty ptz,
  classify_triangle ptx pty ptz = Equilateral -> ptx <> pty ->
  NoDupA equiv (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil).
Proof.
intros ptx pty ptz Htriangle Hdiff.
constructor.
- intro Hin.
  repeat match goal with
    | H : InA _ _ _ |- _ => inversion_clear H
  end.
  + now apply (equilateral_barycenter_not_eq _ Htriangle).
  + assert (Hperm : Permutation (ptx :: pty :: ptz :: nil) (pty :: ptx :: ptz :: nil)) by constructor.
    rewrite (barycenter_3_pts_compat Hperm) in H0. rewrite (classify_triangle_compat Hperm) in Htriangle.
    apply (equilateral_barycenter_not_eq _ Htriangle); trivial.
    intuition.
  + assert (Hperm : Permutation (ptx :: pty :: ptz :: nil) (ptz :: ptx :: pty :: nil)).
    { now etransitivity; repeat constructor. }
    rewrite (barycenter_3_pts_compat Hperm) in H. rewrite (classify_triangle_compat Hperm) in Htriangle.
    apply (equilateral_barycenter_not_eq _ Htriangle); trivial.
    functional induction (classify_triangle ptz ptx pty) as [Heq1 Heq2 | | | |]; try discriminate.
    rewrite Rdec_bool_true_iff in *.
    cbn. intro. subst.
    rewrite R2_dist_defined_2 in *. symmetry in Heq1. now rewrite dist_defined in Heq1.
- now apply equilateral_NoDupA.
Qed.

(** Tactic solving permutations proofs for up to 4 elements.
    Some cases with 4 elements are not yet treated. *)
Ltac permut_3_4 :=
  try match goal with
      | |- @Permutation _ _ _ => apply PermutationA_Leibniz
      end;
  match goal with
  | |- @PermutationA _ _ ?l ?l => reflexivity
  | |- @PermutationA _ _ (?a::?l) (?a::?l2) =>
    constructor 2;[reflexivity | permut_3_4 ]
  | |- @PermutationA _ _ (?a::?b::?l) (?b::?a::?l2) =>
    transitivity (b::a::l); [constructor 3|constructor 2; [reflexivity|constructor 2; [reflexivity|permut_3_4]]]
  | |- @PermutationA _ _ (?a::?b::?c::nil) (?c::?a::?b::nil) =>
    apply PermutationA_app_comm with (l₁:=a::b::nil)(l₂:=c::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::nil) (?b::?c::?a::nil) =>
    apply PermutationA_app_comm with (l₁:=a::nil)(l₂:=b::c::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?d::?a::?b::?c::nil) =>
    apply PermutationA_app_comm with (l₁:=a::nil)(l₂:=b::c::d::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?c::?d::?a::?b::nil) =>
    apply PermutationA_app_comm with (l₁:=a::b::nil)(l₂:=c::d::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?d::?a::?b::?c::nil) =>
    apply PermutationA_app_comm with (l₁:=a::b::c::nil)(l₂:=d::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?a::?d::?b::?c::nil) =>
    constructor 2; 
    apply PermutationA_app_comm with (l₁:=b::c::nil)(l₂:=d::nil);try autoclass
  | |- @PermutationA _ _ (?a::?b::?c::nil) (?c::?b::?a::nil) =>
    transitivity (b::c::a::nil);
    [ apply PermutationA_app_comm with (l₁:=a::nil)(l₂:=b::c::nil);try autoclass
    | constructor 3;reflexivity
    ]
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?b::?d::?a::?c::nil) =>
    transitivity (b::c::d::a::nil);
    [ apply PermutationA_app_comm with (l₁:=a::nil)(l₂:=b::c::d::nil);try autoclass
    | constructor 2;
      [reflexivity
      | apply PermutationA_app_comm with (l₁:=c::nil)(l₂:=d::a::nil);try autoclass ]
    ]
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?b::?c::?a::?d::nil) =>
    transitivity (a::d::b::c::nil);
    [ constructor 2;
      [reflexivity
      | apply PermutationA_app_comm with (l₁:=b::c::nil)(l₂:=d::nil);try autoclass ]
    | apply PermutationA_app_comm with (l₁:=a::d::nil)(l₂:=b::c::nil);try autoclass ]
  | |- @PermutationA _ _ (?a::?b::?c::?d::nil) (?d::?c::?b::?a::nil) =>
    transitivity (c::d::b::a::nil);
    [ transitivity (c::d::a::b::nil);
      [ apply PermutationA_app_comm with (l₁:=a::b::nil)(l₂:=c::d::nil);try autoclass
      | do 2 constructor 2; constructor 3 ]
    | constructor 3;reflexivity ]
  end.

(* In a equilateral triangle x y z with barycenter b, if the middle of [b,y]
   is equal to x then the triangle is degenerated.  *)
Lemma equilateral_barycenter_degenerated: forall ptx pty ptopp white mid,
    classify_triangle ptx pty ptopp = Equilateral ->
    white = barycenter_3_pts ptx pty ptopp ->
    mid = middle ptopp white ->
    ptx = mid ->
    ptx = ptopp.
Proof.
  intros ptx pty ptopp white mid hequil hwhite hmid h.
  subst mid.
  assert (h_dist:=R2dist_middle white ptopp).
  assert (h_dist_bary:=@equilateral_SEC ptx pty ptopp hequil).
  assert (h_permut:Permutation (ptopp :: pty :: ptx :: nil) (ptx :: pty :: ptopp :: nil) ).
  { permut_3_4. }
  assert (hequil':classify_triangle ptopp pty ptx = Equilateral).
  { rewrite <- hequil.
    eapply classify_triangle_compat.
    assumption. }
  assert (h_dist_bary':=@equilateral_SEC  ptopp pty ptx hequil').
  rewrite h_permut in h_dist_bary'.
  rewrite h_dist_bary' in h_dist_bary.
  injection h_dist_bary.
  intro h_disteq.
  intro h_baryeq'.
  rewrite h_baryeq' in h_disteq.
  setoid_rewrite <- hwhite in h_disteq.
  rewrite h_disteq in h_dist.
  rewrite h in h_dist.
  rewrite middle_comm in h_dist.
  assert (dist white (middle ptopp white) = 0%R).
  { lra. }
  assert (h_white_ptopp:(equiv white ptopp)). 
  { apply dist_defined in H.
    symmetry in H.
    rewrite middle_comm in H.
    now rewrite middle_eq in H.
  }
  assert (h_white_ptx:(equiv white ptx)).
  { rewrite <- h in H.
    now apply dist_defined in H.
  }
  rewrite <- h_white_ptopp, h_white_ptx.
  reflexivity.
Qed.

Lemma equilateral_barycenter_degenerated_gen: forall ptx pty ptz ptopp white mid,
    classify_triangle ptx pty ptz = Equilateral ->
    white = barycenter_3_pts ptx pty ptz ->
    In ptopp (ptx :: pty :: ptz :: nil) -> 
    mid = middle ptopp white ->
    In mid (ptx :: pty :: ptz :: nil) ->
    mid = ptopp.
Proof.
  intros ptx pty ptz ptopp white mid hequil hwhite hptopp hmid h.
  simpl in h.
  decompose [or] h;clear h;try contradiction.
  - subst ptx.
    simpl in hptopp.
    decompose [or] hptopp;clear hptopp;try contradiction.
    + assumption.
    + subst pty.
      apply (@equilateral_barycenter_degenerated mid ptz ptopp white mid);auto.
      * erewrite classify_triangle_compat;eauto; permut_3_4.
      * erewrite barycenter_3_pts_compat;eauto; permut_3_4.
    + subst ptz.
      apply (@equilateral_barycenter_degenerated mid pty ptopp white mid);auto.
  - subst pty.
    simpl in hptopp.
    decompose [or] hptopp;clear hptopp;try contradiction.
    + subst ptx.
      apply (@equilateral_barycenter_degenerated mid ptz ptopp white mid);auto.
      * erewrite classify_triangle_compat;eauto;permut_3_4.
      * erewrite barycenter_3_pts_compat;eauto;permut_3_4.
    + assumption.
    + subst ptz.
      eapply equilateral_barycenter_degenerated with (pty:=ptx) ; eauto.
      * erewrite classify_triangle_compat;eauto;permut_3_4.
      * subst white.
        erewrite barycenter_3_pts_compat;eauto;permut_3_4.
  - subst ptz.
    simpl in hptopp.
    decompose [or] hptopp;clear hptopp;try contradiction.
    + subst ptx.
      apply (@equilateral_barycenter_degenerated mid pty ptopp white mid);auto.
      * erewrite classify_triangle_compat;eauto;permut_3_4.
      * erewrite barycenter_3_pts_compat;eauto;permut_3_4.
    + subst pty.
      eapply equilateral_barycenter_degenerated with (pty:=ptx) ; eauto.
      * erewrite classify_triangle_compat;eauto;permut_3_4.
      * subst white.
        erewrite barycenter_3_pts_compat;eauto;permut_3_4.
    + assumption.
Qed.
