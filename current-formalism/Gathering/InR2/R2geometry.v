Require Import Rbase R_sqrt Rbasic_fun.
Require Import Psatz.
Require Import RelationPairs.
Require Import Morphisms.
Require Import SetoidPermutation.
Require Import Omega.
Import List Permutation SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Configurations.


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


(** **  R² as a vector space over R  **)

Module R2def : RealMetricSpaceDef with Definition t := (R * R)%type
                                  with Definition eq := @Logic.eq (R * R)
(*                                  with Definition eq_dec := Rdec *)
                                  with Definition origin := (0, 0)%R
                                  with Definition dist := fun x y => sqrt ((fst x - fst y)² + (snd x - snd y)²)
                                  with Definition add := fun x y => let '(x1, x2) := x in
                                                                    let '(y1, y2) := y in (x1 + y1, x2 + y2)%R
                                  with Definition mul := fun k r => let '(x, y) := r in (k * x, k * y)%R
                                  with Definition opp := fun r => let '(x, y) := r in (-x, -y)%R.
  
  Definition t := (R * R)%type.
  Definition origin := (0, 0)%R.
  Definition eq := @Logic.eq (R * R).
  Definition dist x y := sqrt ((fst x - fst y)² + (snd x - snd y)²).
  
  Definition add x y := let '(x1, x2) := x in let '(y1, y2) := y in (x1 + y1, x2 + y2)%R.
  Definition mul k r := let '(x, y) := r in (k * x, k * y)%R.
  Definition opp r := let '(x, y) := r in (-x, -y)%R.
  
  Ltac solve_R := repeat intros [? ?] || intro; compute; f_equal; ring.
  
  Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance opp_compat : Proper (eq ==> eq) opp.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Definition eq_equiv := @eq_equivalence (R * R).
  
  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. unfold eq. decide equality; apply Rdec. Qed.
  
  Lemma dist_defined : forall x y : t, dist x y = 0%R <-> eq x y.
  Proof.
  intros x y. unfold eq, dist. split; intro Heq.
  + apply sqrt_eq_0 in Heq.
    - apply Rplus_eq_R0 in Heq; try apply Rle_0_sqr; [].
      destruct Heq as [Hx Hy].
      apply Rsqr_0_uniq, Rminus_diag_uniq in Hx.
      apply Rsqr_0_uniq, Rminus_diag_uniq in Hy.
      destruct x, y; simpl in *; subst; reflexivity.
    - replace 0%R with (0 + 0)%R by ring. apply Rplus_le_compat; apply Rle_0_sqr.
  + subst. do 2 rewrite (Rminus_diag_eq _ _ (reflexivity _)). rewrite Rsqr_0, Rplus_0_l. apply sqrt_0.
  Qed.
  
  Lemma dist_sym : forall y x : t, dist x y = dist y x.
  Proof. intros. unfold dist. now setoid_rewrite R_sqr.Rsqr_neg_minus at 1 2. Qed.
  
  Lemma triang_ineq : forall x y z : t, (dist x z <= dist x y + dist y z)%R.
  Proof.
  intros [? ?] [? ?] [? ?]. unfold dist. simpl.
  apply (Rgeom.triangle r r0 r3 r4 r1 r2).
  Qed.
  
  Lemma add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. solve_R. Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. solve_R. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. solve_R. Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. solve_R. Qed.
  
  Lemma mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. solve_R. Qed.
  
  Lemma mul_distr_add : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. solve_R. Qed.
  
  Lemma add_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  Proof. solve_R. Qed.
  
  Lemma mul_1 : forall u, eq (mul 1 u) u.
  Proof. solve_R. Qed.
  
  Lemma non_trivial : exists u v, ~eq u v.
  Proof. exists (0, 0), (0, 1). compute. injection. auto using R1_neq_R0. Qed.
End R2def.


Module R2 := MakeRealMetricSpace(R2def).

Delimit Scope R2_scope with R2.
Bind Scope R2_scope with R2.t.
Notation "u + v" := (R2.add u v) : R2_scope.
Notation "k * u" := (R2.mul k u) : R2_scope.
Notation "- u" := (R2.opp u) : R2_scope.
Notation "u - v" := (R2.add u (R2.opp v)) : R2_scope.

Corollary square_dist_equiv : forall pt1 pt2 k, 0 <= k ->
  (R2.dist pt1 pt2 = k <-> (R2.dist pt1 pt2)² = k²).
Proof.
intros pt1 pt2 k Hk. split; intro Heq.
+ now rewrite Heq.
+ unfold R2.dist, R2def.dist in *. rewrite Rsqr_sqrt in Heq.
  - rewrite Heq. now rewrite sqrt_Rsqr.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma square_dist_simpl : forall pt1 pt2, (R2.dist pt1 pt2)² = (fst pt1 - fst pt2)² + (snd pt1 - snd pt2)².
Proof.
intros pt1 pt2. unfold R2.dist, R2def.dist. rewrite Rsqr_sqrt; trivial.
replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma R2_dist_defined_2 : forall pt, R2.dist pt pt = 0.
Proof.
  intros pt.
  rewrite R2.dist_defined.
  reflexivity.
Qed.
Hint Resolve R2_dist_defined_2.

Lemma R2add_dist : forall w u v, R2.dist (u + w) (v + w) = R2.dist u v.
Proof.
intros [? ?] [? ?] [? ?]. unfold R2.dist, R2def.dist. f_equal. cbn.
replace (r1 + r - (r3 + r)) with (r1 - r3) by ring.
replace (r2 + r0 - (r4 + r0)) with (r2 - r4) by ring.
reflexivity.
Qed.

Lemma R2mul_dist : forall k u v, R2.dist (k * u) (k * v) = Rabs k * R2.dist u v.
Proof.
intros k [? ?] [? ?]. unfold R2.dist, R2def.dist. cbn.
apply pos_Rsqr_eq.
- apply sqrt_pos.
- apply Rmult_le_pos; apply Rabs_pos || apply sqrt_pos.
- rewrite Rsqr_sqrt.
  + rewrite R_sqr.Rsqr_mult. rewrite Rsqr_sqrt.
    * repeat rewrite ?R_sqr.Rsqr_mult, ?R_sqr.Rsqr_plus, ?R_sqr.Rsqr_minus, <- ?R_sqr.Rsqr_abs. unfold Rsqr. lra.
    * replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
  + replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply Rle_0_sqr.
Qed.

Lemma R2dist_subadditive : forall u u' v v', R2.dist (u + v) (u' + v') <= R2.dist u u' + R2.dist v v'.
Proof.
intros. etransitivity. apply (R2.triang_ineq _ (u' + v)%R2).
rewrite R2add_dist. setoid_rewrite R2.add_comm. rewrite R2add_dist. reflexivity.
Qed.

Lemma R2dist_ref_0 : forall u v, R2.dist u v = R2.dist (u - v)%R2 R2.origin.
Proof. intros u v. now rewrite <- (R2add_dist (-v)), R2.add_opp. Qed.

Lemma R2sub_origin : forall u v, R2.eq (u - v) R2.origin <-> R2.eq u v.
Proof.
intros u v. split; intro Heq.
- now rewrite <- R2.dist_defined, <- (R2add_dist (- v)), R2.add_opp, R2.dist_defined.
- now rewrite Heq, R2.add_opp.
Qed.

(** **  Simplification tactics  **)

Transparent R2.origin R2def.origin R2.eq_dec R2.eq R2def.eq R2.dist R2def.dist.

Ltac unfoldR2 := unfold R2.origin, R2def.origin, R2.eq_dec, R2.eq, R2def.eq, R2.dist, R2def.dist.

Tactic Notation "unfoldR2" "in" ident(H) :=
  unfold R2.origin, R2def.origin, R2.eq_dec, R2.eq, R2def.eq, R2.dist, R2def.dist in H.

(** Small decision tactics for vectors simplifying v = v and v <> v. *)
Ltac R2dec := repeat
  match goal with
    | |- context[R2.eq_dec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (R2.eq_dec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ?x <> ?x |- _ => elim H; reflexivity
    | Heq : R2.eq ?x ?y, Hneq : ~R2.eq ?y ?x |- _ => symmetry in Heq; contradiction
    | Heq : R2.eq ?x ?y, Hneq : ~R2.eq ?x ?y |- _ => contradiction
  end.

Ltac R2dec_full :=
  match goal with
    | |- context[R2.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (R2.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac R2dec_full_in H :=
  match type of H with
    | context[R2.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (R2.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.
Tactic Notation "R2dec_full" "in" ident(H) := R2dec_full_in H.

Ltac normalize_R2dist pt1' pt2' pt3' :=
  (repeat progress (rewrite ?Rdec_bool_false_iff
                    , ?Rdec_bool_true_iff , ?(R2.dist_sym pt2' pt1')
                    , ?(R2.dist_sym pt3' pt1'), ?(R2.dist_sym pt3' pt2') in *));
    try match goal with
        | H: ~( _ <= _) |- _ => apply Rnot_le_lt in H
        end.

Ltac null x :=
  let Hnull := fresh "Hnull" in
  destruct (R2.eq_dec x R2.origin) as [Hnull | Hnull]; [rewrite Hnull in * |].


Definition R2dec_bool (x y : R2.t) := if R2.eq_dec x y then true else false.

Lemma R2dec_bool_true_iff (x y : R2.t) : R2dec_bool x y = true <-> x = y.
Proof.
  unfold R2dec_bool.
  destruct (R2.eq_dec x y);split;try discriminate;auto.
Qed.

Lemma R2dec_bool_false_iff (x y : R2.t) : R2dec_bool x y = false <-> x <> y.
Proof.
  unfold R2dec_bool.
  destruct (R2.eq_dec x y); split; try discriminate;auto.
  intros abs.
  rewrite e in abs.
  elim abs; auto.
Qed.


(** **  Poor man's formalization of euclidean spaces  **)

(* FIXME: we should instead have a proper formalisation of euclidean spaces! *)
Definition product (u v : R2.t) := fst u * fst v + snd u * snd v.
Definition R2norm u := sqrt (product u u).
Definition orthogonal (u : R2.t) : R2.t := /(R2norm u) * (snd u, - fst u).
Definition unitary u := (/(R2norm u) * u)%R2.
Definition perpendicular u v := product u v = 0.
Definition colinear (u v : R2.t) := perpendicular u (orthogonal v).


(* Compatibilities *)
Instance product_compat : Proper (R2.eq ==> R2.eq ==> eq) product.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

Instance R2norm_compat : Proper (R2.eq ==> eq) R2norm.
Proof. intros u v Heq. now rewrite Heq. Qed.

Instance orthogonal_compat : Proper (R2.eq ==> R2.eq) orthogonal.
Proof. intros u v Heq. now rewrite Heq. Qed.

(* could be strengthen with [colinear] (up to sign) *)
Instance unitary_compat : Proper (R2.eq ==> R2.eq) unitary.
Proof. intros u v Heq. unfold unitary. now rewrite Heq. Qed.

Instance perpendicular_compat : Proper (R2.eq ==> R2.eq ==> iff) perpendicular.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

Instance colinear_compat : Proper (R2.eq ==> R2.eq ==> iff) colinear.
Proof. intros u1 u2 Hu v1 v2 Hv. now rewrite Hu, Hv. Qed.

(** *** Results about [product]  **)

Lemma product_0_l : forall u, product R2.origin u = 0.
Proof. intros [x y]. unfold product; simpl. field. Qed.

Lemma product_0_r : forall u, product u R2.origin = 0.
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

Lemma R2norm_dist : forall u v, R2.dist u v = R2norm (u - v)%R2.
Proof. intros [x1 y1] [x2 y2]. unfold R2norm, R2.dist, R2def.dist. reflexivity. Qed.

Lemma R2norm_0 : forall u, R2norm u = 0 <-> R2.eq u R2.origin.
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
- now rewrite R2.minus_morph, R2.mul_1.
Qed.

Lemma square_R2norm_equiv : forall u k, 0 <= k -> (R2norm u = k <-> (R2norm u)² = k²).
Proof. intros u k Hk. split; intro Heq; try congruence; []. apply pos_Rsqr_eq; trivial. apply R2norm_pos. Qed.

Corollary squared_R2norm : forall u v, R2norm u = R2norm v <-> (R2norm u)² = (R2norm v)².
Proof. intros u v. apply square_R2norm_equiv. apply R2norm_pos. Qed.

Lemma squared_R2norm_product : forall u, (R2norm u)² = product u u.
Proof. intro. unfold R2norm. rewrite Rsqr_sqrt; trivial. apply product_self_pos. Qed.

(** ***  Results about [orthogonal]  **)

Lemma orthogonal_perpendicular : forall u, perpendicular u (orthogonal u).
Proof.
intro u. destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- unfold perpendicular. now rewrite Hnull, product_0_l.
- destruct u as [x y]. unfold perpendicular, orthogonal, product. simpl. field. now rewrite R2norm_0.
Qed.

Lemma orthogonal_origin : R2.eq (orthogonal R2.origin) R2.origin.
Proof. unfold orthogonal. simpl. now rewrite Ropp_0, Rmult_0_r. Qed.

Lemma R2norm_orthogonal : forall u, ~R2.eq u R2.origin -> R2norm (orthogonal u) = 1.
Proof.
intros u Hnull. rewrite <- R2norm_0 in Hnull. unfold orthogonal. rewrite R2norm_mul. rewrite Rabs_pos_eq.
- unfold R2norm in *. destruct u. unfold product in *. simpl in *.
  replace (r0 * r0 + - r * - r) with (r * r + r0 * r0) by ring. now apply Rinv_l.
- apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply R2norm_pos.
Qed.

Lemma orthogonal_opp : forall u, R2.eq (orthogonal (- u)) (- orthogonal u).
Proof.
intro u. null u.
- now rewrite R2.opp_origin, orthogonal_origin, R2.opp_origin.
- destruct u as [? ?]. unfold orthogonal. rewrite R2norm_opp. cbn. hnf. now f_equal; field; rewrite R2norm_0.
Qed.

(* False in general because k may change the direction (but not the orientation) of u *)
Lemma orthogonal_mul : forall k u, 0 < k -> R2.eq (orthogonal (k * u)) (orthogonal u).
Proof.
intros k u Hk. null u.
- now rewrite R2.mul_origin, orthogonal_origin.
- rewrite <- R2norm_0 in Hnull. unfold orthogonal.
  rewrite R2norm_mul, Rabs_pos_eq; try (now apply Rlt_le); [].
  destruct u. simpl. hnf. f_equal; field; split; auto with real.
Qed.

(** ***  Results about [unitary]  **)

Lemma R2norm_unitary : forall u, ~R2.eq u R2.origin -> R2norm (unitary u) = 1.
Proof.
intros u Hnull.
assert (R2norm u <> 0). { now rewrite R2norm_0. }
unfold unitary. rewrite R2norm_mul, Rabs_pos_eq.
- now apply Rinv_l.
- apply Rlt_le. apply Rinv_0_lt_compat. apply Rle_neq_lt; auto; []. apply R2norm_pos.
Qed.

Lemma unitary_origin : unitary R2.origin = R2.origin.
Proof. unfold unitary. apply R2.mul_origin. Qed.

Lemma unitary_id : forall u, R2.eq u ((R2norm u) * unitary u).
Proof.
intro u. unfold unitary. rewrite R2.mul_morph.
destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- rewrite Hnull. now rewrite R2.mul_origin.
- rewrite Rinv_r, R2.mul_1; try easy; []. now rewrite R2norm_0.
Qed.

Lemma unitary_idempotent : forall u, R2.eq (unitary (unitary u)) (unitary u).
Proof.
intro u. destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- rewrite Hnull. now rewrite unitary_origin at 1.
- unfold unitary at 1. rewrite R2norm_unitary; trivial; []. replace (/1) with 1 by field. apply R2.mul_1.
Qed.

Lemma unitary_product : forall u v, product u v = R2norm u * R2norm v * product (unitary u) (unitary v).
Proof. intros. setoid_rewrite unitary_id at 1 2. rewrite product_mul_l, product_mul_r. field. Qed.

Lemma unitary_orthogonal : forall u, unitary (orthogonal u) = orthogonal u.
Proof.
intro u. destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- rewrite Hnull. rewrite orthogonal_origin. apply unitary_origin.
- unfold unitary. rewrite R2norm_orthogonal; trivial; []. replace (/1) with 1 by field. now rewrite R2.mul_1.
Qed.

Lemma orthogonal_unitary : forall u, orthogonal (unitary u) = orthogonal u.
Proof.
intro u. destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- rewrite Hnull. now rewrite unitary_origin.
- unfold orthogonal. rewrite R2norm_unitary; trivial; []. unfold unitary. simpl.
  rewrite <- R2norm_0 in Hnull. now destruct u; f_equal; simpl; field.
Qed.

(** ***  Results about [perpendicular]  **)

Lemma perpendicular_origin_l : forall u, perpendicular R2.origin u.
Proof. intros [? ?]; compute. field. Qed.

Lemma perpendicular_origin_r : forall u, perpendicular u R2.origin.
Proof. intros [? ?]; compute. field. Qed.

Lemma perpendicular_opp_compat_l : forall u v, perpendicular (- u) v <-> perpendicular u v.
Proof.
intros u v. unfold perpendicular. split; intro Hperp.
- rewrite <- R2.mul_1, R2.mul_opp, <- R2.minus_morph, product_mul_l in Hperp. lra.
- rewrite <- R2.mul_1, R2.mul_opp, <- R2.minus_morph, product_mul_l, Hperp. field.
Qed.

Lemma perpendicular_opp_compat_r : forall u v, perpendicular u (- v) <-> perpendicular u v.
Proof.
intros u v. unfold perpendicular. split; intro Hperp.
- setoid_rewrite <- R2.mul_1 in Hperp at 2. rewrite R2.mul_opp, <- R2.minus_morph, product_mul_r in Hperp. lra.
- setoid_rewrite <- R2.mul_1 at 2. rewrite R2.mul_opp, <- R2.minus_morph, product_mul_r, Hperp. field.
Qed.

Lemma perpendicular_mul_compat_l : forall k u v, perpendicular u v -> perpendicular (k * u) v.
Proof. intros k u v Hperp. unfold perpendicular. rewrite product_mul_l, Hperp. field. Qed.

Lemma perpendicular_mul_compat_r : forall k u v, perpendicular u v -> perpendicular u (k * v).
Proof. intros k u v Hperp. unfold perpendicular. rewrite product_mul_r, Hperp. field. Qed.

Lemma perpendicular_sym : forall u v, perpendicular u v <-> perpendicular v u.
Proof. intros. unfold perpendicular. now rewrite product_comm. Qed.

Lemma perpendicular_mul_compat_l_iff : forall k u v, k <> 0 -> (perpendicular (k * u) v <-> perpendicular u v).
Proof.
intros k u v Hk. split; intro Hperp.
- rewrite <- R2.mul_1. rewrite <- (Rinv_l k); trivial; []. rewrite <- R2.mul_morph.
  now apply perpendicular_mul_compat_l.
- now apply perpendicular_mul_compat_l.
Qed.

Lemma perpendicular_mul_compat_r_iff : forall k u v, k <> 0 -> (perpendicular u (k * v) <-> perpendicular u v).
Proof.
intros k u v Hk. split; intro Hperp.
- rewrite <- (R2.mul_1 v). rewrite <- (Rinv_l k); trivial; []. rewrite <- R2.mul_morph.
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
  - destruct u, v. unfold perpendicular, orthogonal, product in *. simpl in *.
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

Lemma perpendicular_unitary_compat_l : forall u v, perpendicular u v -> perpendicular (unitary u) v.
Proof.
intros u v Hperp. destruct (R2.eq_dec u R2.origin) as [Hnull | Hnull].
- rewrite Hnull, unitary_origin. unfold perpendicular, product. simpl. field.
- unfold perpendicular. unfold unitary. rewrite product_mul_l, Hperp. field. now rewrite R2norm_0.
Qed.

Lemma perpendicular_unitary_compat_r : forall u v, perpendicular u v -> perpendicular u (unitary v).
Proof.
intros u v Hperp. destruct (R2.eq_dec v R2.origin) as [Hnull | Hnull].
- rewrite Hnull, unitary_origin. unfold perpendicular, product. simpl. field.
- unfold perpendicular. unfold unitary. rewrite product_mul_r, Hperp. field. now rewrite R2norm_0.
Qed.

Lemma unitary_orthogonal_perpendicular : forall u, perpendicular (unitary u) (orthogonal u).
Proof. intro. apply perpendicular_unitary_compat_l, orthogonal_perpendicular. Qed.

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

Lemma perpendicular_twice_colinear : forall u v w, perpendicular u v -> perpendicular v w -> colinear u w.
Proof.
intros u v w Huv Hvw.
null u; [| null w].
+ apply perpendicular_origin_l.
+ unfold colinear. rewrite orthogonal_origin. apply perpendicular_origin_r.
+ unfold colinear, perpendicular, orthogonal, product in *. simpl.
  replace (fst u * (/ R2norm w * snd w) + snd u * (/ R2norm w * - fst w))
    with (/ R2norm w * (fst u * snd w + snd u * - fst w)) by ring.
Admitted.

Lemma perpendicular_dec : forall u v, {perpendicular u v} + {~perpendicular u v}.
Proof. intros u v. unfold perpendicular. apply Rdec. Defined.

(** ***  Results about [colinear]  **)

Lemma colinear_dec : forall u v, {colinear u v} + {~colinear u v}.
Proof. intros u v. unfold colinear. apply perpendicular_dec. Defined.

Instance colinear_equiv : Equivalence colinear.
Proof. unfold colinear. split.
+ intro. apply orthogonal_perpendicular.
+ intros u v H. now rewrite perpendicular_sym, perpendicular_orthogonal_shift.
+ intros u v w Huv Hvw. apply perpendicular_twice_colinear with (orthogonal v).
  - assumption.
  - now rewrite perpendicular_orthogonal_shift.
Qed.

Lemma colinear_origin_l : forall u, colinear R2.origin u.
Proof. intro u. unfold colinear. apply perpendicular_origin_l. Qed.

Lemma colinear_origin_r : forall u, colinear u R2.origin.
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

Instance perpendicular_colinear_compat : Proper (colinear ==> colinear ==> iff) perpendicular.
Proof.
intros u u' Hu v v' Hv. split; intro Hperp.
+ rewrite <- perpendicular_orthogonal_compat. change (colinear (orthogonal u') v').
  rewrite <- Hv, <- colinear_orthogonal_shift, <- Hu, colinear_orthogonal_shift.
  unfold colinear. now rewrite perpendicular_orthogonal_compat.
+ rewrite <- perpendicular_orthogonal_compat. change (colinear (orthogonal u) v).
  rewrite Hv, <- colinear_orthogonal_shift, Hu, colinear_orthogonal_shift.
  unfold colinear. now rewrite perpendicular_orthogonal_compat.
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

Theorem triang_ineq_eq : forall u v w,
  R2.dist u w = R2.dist u v + R2.dist v w -> colinear (w - u) (v - u) /\ colinear (w - u) (w - v).
Proof.
Admitted.

(* Beurk! *)
Theorem decompose_on : forall u, ~R2.eq u R2.origin -> forall v,
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

Corollary colinear_decompose : forall u, ~R2.eq u R2.origin -> forall v,
  colinear u v -> R2.eq v (R2norm v * unitary u)%R2 \/ R2.eq v (- R2norm v * unitary u)%R2.
Proof.
intros u Hnull v Huv. rewrite (decompose_on Hnull v).
symmetry in Huv. rewrite Huv. rewrite R2.mul_0, R2.add_origin.
rewrite R2norm_mul. rewrite R2norm_unitary, Rmult_1_r; trivial.
destruct (Rle_dec 0 (product v (unitary u))) as [Hle | Hle].
- left. f_equal. now rewrite Rabs_pos_eq.
- right. f_equal. now rewrite Rabs_left, Ropp_involutive; auto with real.
Qed.

(* A very ugly proof! *)
Lemma segment_bisector_spec : forall pt1 pt2 pt, ~R2.eq pt1 pt2 ->
  R2.dist pt1 pt = R2.dist pt pt2 <-> exists k, R2.eq pt (R2.middle pt1 pt2 + k * orthogonal (pt2 - pt1))%R2.
Proof.
intros pt1 pt2 pt Hnull. split; intro Hpt.
+ pose (ptx := (pt - pt1)%R2).
  exists (product ptx (orthogonal (pt2 - pt1))).
  assert (Hneq : ~R2.eq (pt2 - pt1) R2.origin).
  { intro Habs. apply Hnull. destruct pt1, pt2; simpl in *. injection Habs; intros; hnf; f_equal; lra. }
  rewrite R2.add_comm. rewrite <- R2.dist_defined. rewrite <- (R2add_dist (- pt1)). fold ptx.
  rewrite <- R2.add_assoc. replace (R2.middle pt1 pt2 - pt1)%R2 with (1/2 * (pt2 - pt1))%R2
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
  setoid_rewrite <- (R2add_dist (- pt1)) at 2 in Hpt. rewrite R2.dist_sym in Hpt.
  do 2 rewrite R2norm_dist in Hpt. fold u ptx in Hpt.
  assert (Hsquare : (R2norm ptx)² = (R2norm (ptx - u))²) by now rewrite Hpt.
  rewrite R2norm_sub in Hsquare. rewrite <- R2norm_0 in Hneq.
  assert (Heq : R2norm u = 2 * product ptx (unitary u)).
  { unfold unitary. rewrite product_mul_r. apply Rmult_eq_reg_l with (R2norm u); trivial; [].
    change (R2norm u * R2norm u) with (R2norm u)². field_simplify; trivial; []. lra. }
  rewrite Heq. unfold Rsqr. field.
+ destruct Hpt as [k Hpt]. rewrite Hpt. unfold R2.middle. do 2 rewrite R2norm_dist.
  rewrite R2.opp_distr_add. rewrite <- (R2.add_comm (-pt2)). repeat rewrite R2.add_assoc.
  replace (pt1 - (1 / 2 * (pt1 + pt2)))%R2 with (- (/2 * (pt2 - pt1)))%R2
    by (destruct pt1, pt2; simpl; f_equal; field).
  replace (- pt2 + 1 / 2 * (pt1 + pt2))%R2 with (- (/2 * (pt2 - pt1)))%R2
    by (destruct pt1, pt2; simpl; f_equal; field).
  assert (Hperp : perpendicular (- (/2 * (pt2 - pt1))) (k * orthogonal (pt2 - pt1)))
    by apply perpendicular_opp_compat_l, perpendicular_mul_compat_l,
             perpendicular_mul_compat_r, orthogonal_perpendicular.
  rewrite squared_R2norm. rewrite Pythagoras in Hperp. rewrite Hperp.
  setoid_rewrite <- R2norm_opp at 3. rewrite <- Pythagoras.
  apply perpendicular_opp_compat_l, perpendicular_opp_compat_r,
        perpendicular_mul_compat_l, perpendicular_mul_compat_r, orthogonal_perpendicular.
Qed.

(** **  Triangles  **)

Inductive triangle_type :=
  | Equilateral
  | Isosceles (vertex : R2.t)
  | Scalene.

Function classify_triangle (pt1 pt2 pt3 : R2.t) : triangle_type :=
  if Rdec_bool (R2.dist pt1 pt2) (R2.dist pt2 pt3)
  then if Rdec_bool (R2.dist pt1 pt3) (R2.dist pt2 pt3)
       then Equilateral
       else Isosceles pt2
  else if Rdec_bool (R2.dist pt1 pt3) (R2.dist pt2 pt3) then Isosceles pt3
  else if Rdec_bool (R2.dist pt1 pt2) (R2.dist pt1 pt3) then Isosceles pt1
  else Scalene.

Function opposite_of_max_side (pt1 pt2 pt3 : R2.t) :=
  let len12 := R2.dist pt1 pt2 in
  let len23 := R2.dist pt2 pt3 in
  let len13 := R2.dist pt1 pt3 in
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
    functional induction (classify_triangle a b c);auto;
    functional induction (classify_triangle a' b' c');auto
  end;
  normalize_R2dist pt1' pt2' pt3';try contradiction;
  try match goal with
      | H1:?A <> ?B, H2: ?B = ?A |- _ => symmetry in H2;contradiction
      | H1:?A <> ?B, H2: ?A = ?C , H3: ?C = ?B  |- _ =>
        assert (A=B) by (transitivity C;auto)
        ;contradiction
      | H1:?A <> ?B, H2: ?A = ?C , H3: ?B = ?C  |- _ =>
        assert (A=B) by (transitivity C;auto)
        ;try contradiction; try (symmetry; contradiction)
      | H1:?A <> ?B, H2: ?C = ?A , H3: ?C = ?B  |- _ =>
        assert (A=B) by (transitivity C;auto)
        ;try contradiction; try (symmetry; contradiction)
      | H1:?A <> ?B, H2: ?C = ?A , H3: ?B = ?C  |- _ =>
        assert (A=B) by (transitivity C;auto)
        ;try contradiction; try (symmetry; contradiction)
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
  <-> R2.dist pt1 pt2 = R2.dist pt2 pt3 /\ R2.dist pt1 pt3 = R2.dist pt2 pt3.
Proof.
intros pt1 pt2 pt3. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *; split; intro; intuition discriminate.
Qed.

Lemma classify_triangle_Isosceles_spec : forall pt1 pt2 pt3 pt,
  classify_triangle pt1 pt2 pt3 = Isosceles pt
  <-> (pt = pt1 /\ R2.dist pt1 pt2 = R2.dist pt1 pt3 /\ R2.dist pt1 pt2 <> R2.dist pt2 pt3)
   \/ (pt = pt2 /\ R2.dist pt2 pt1 = R2.dist pt2 pt3 /\ R2.dist pt2 pt1 <> R2.dist pt1 pt3)
   \/ (pt = pt3 /\ R2.dist pt3 pt1 = R2.dist pt3 pt2 /\ R2.dist pt3 pt1 <> R2.dist pt1 pt2).
Proof.
intros pt1 pt2 pt3 pt. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *;
repeat lazymatch goal with
  | H : context[R2.dist pt2 pt1] |- _ => rewrite (R2.dist_sym pt1 pt2) in H
  | H : context[R2.dist pt3 pt1] |- _ => rewrite (R2.dist_sym pt1 pt3) in H
  | H : context[R2.dist pt3 pt2] |- _ => rewrite (R2.dist_sym pt2 pt3) in H
  | |- context[R2.dist pt2 pt1] => rewrite (R2.dist_sym pt1 pt2)
  | |- context[R2.dist pt3 pt1] => rewrite (R2.dist_sym pt1 pt3)
  | |- context[R2.dist pt3 pt2] => rewrite (R2.dist_sym pt2 pt3)
  | H : context[R2.dist ?x ?y = _] |- context[R2.dist ?x ?y] => setoid_rewrite H; clear H
end;
split; intro H; discriminate || (progress decompose [or and] H; clear H) || (injection H; intro);
subst; trivial; try contradiction.
+ right; left. subst. repeat split. intro Heq. rewrite Heq in *. intuition.
+ match goal with H : ?x <> ?x |- _ => now elim H end.
+ do 2 right. subst. repeat split; trivial. intro Heq. rewrite Heq in *. intuition.
+ repeat match goal with
    | H : R2.dist _ _ = _ |- _ => rewrite H in *; clear H
    | H : ?x <> ?x |- _ => now elim H
  end.
+ left. now repeat split.
Qed.

Lemma classify_triangle_Scalene_spec : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Scalene
  <-> R2.dist pt1 pt2 <> R2.dist pt2 pt3
   /\ R2.dist pt1 pt2 <> R2.dist pt1 pt3
   /\ R2.dist pt1 pt3 <> R2.dist pt2 pt3.
Proof.
intros pt1 pt2 pt3. functional induction (classify_triangle pt1 pt2 pt3);
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *; split; intro; intuition discriminate.
Qed.

(** **  Barycenter and middle  **)

(* Barycenter is the center of SEC for an equilateral triangle *)

Definition barycenter_3_pts (pt1 pt2 pt3:R2.t) := R2.mul (Rinv 3) (R2.add pt1 (R2.add pt2 pt3)).

Lemma barycenter_3_pts_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    barycenter_3_pts pt1 pt2 pt3 =  barycenter_3_pts pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' Hperm.
  rewrite <- PermutationA_Leibniz, (PermutationA_3 _) in Hperm.
  decompose [or and] Hperm; clear Hperm; subst;
  reflexivity || unfold barycenter_3_pts; f_equal;
  (* FIXME: find a better way to normalize the sum? field? *)
  repeat match goal with
         | |- context C [ (R2.add pt1' (R2.add pt3' pt2')) ] => rewrite (@R2.add_comm pt3')
         | |- context C [ (R2.add pt2' (R2.add pt1' pt3')) ] =>
           rewrite (@R2.add_assoc pt2' pt1' pt3'); rewrite (@R2.add_comm pt2' pt1');
           rewrite <- (@R2.add_assoc pt1' pt2' pt3')
         | |- context C [ (R2.add pt2' (R2.add pt3' pt1')) ] =>
           rewrite (@R2.add_comm pt3' pt1')
         | |- context C [ (R2.add pt3' (R2.add pt1' pt2')) ] =>
           rewrite (@R2.add_comm pt3' (R2.add pt1' pt2'));
             rewrite <- (@R2.add_assoc pt1' pt2' pt3')
         | |- context C [ (R2.add pt3' (R2.add pt2' pt1')) ] =>
           rewrite (@R2.add_comm pt2' pt1')
         end; reflexivity.
Qed.

Axiom Barycenter_spec: forall pt1 pt2 pt3 B: R2.t,
    barycenter_3_pts pt1 pt2 pt3 = B -> 
    forall p,
      (R2.dist B pt1)² + (R2.dist B pt2)² + (R2.dist B pt3)²
      <= (R2.dist p pt1)² + (R2.dist p pt2)² + (R2.dist p pt3)².

(* False if we are not in an euclidian space!
   Take for instance the coarse distance d(x,y) = 1 <-> x <> y, and pt1, pt2 pt3 different.
   Then any one of them is a barycenter. *)
Axiom Barycenter_spec_unicity: forall pt1 pt2 pt3 B: R2.t,
    barycenter_3_pts pt1 pt2 pt3 = B <-> 
    forall p, p <> B ->
              (R2.dist B pt1)² + (R2.dist B pt2)² + (R2.dist B pt3)²
              < (R2.dist p pt1)² + (R2.dist p pt2)² + (R2.dist p pt3)².

Definition is_middle pt1 pt2 B := forall p,
  (R2.dist B pt1)² + (R2.dist B pt2)² <= (R2.dist p pt1)² + (R2.dist p pt2)².
Definition is_barycenter_3_pts pt1 pt2 pt3 B := forall p,
  (R2.dist B pt1)² + (R2.dist B pt2)² + (R2.dist B pt3)² <= (R2.dist p pt1)² + (R2.dist p pt2)² + (R2.dist p pt3)².

Lemma R2dist_middle : forall pt1 pt2,
  R2.dist pt1 (R2.middle pt1 pt2) = /2 * R2.dist pt1 pt2.
Proof.
intros pt1 pt2.
replace pt1 with (/2 * pt1 + /2 * pt1)%R2 at 1.
+ unfold R2.middle. rewrite R2.mul_distr_add. setoid_rewrite R2.add_comm.
  replace (1/2) with (/2) by field. rewrite R2add_dist.
  rewrite R2mul_dist. rewrite Rabs_pos_eq; lra.
+ rewrite R2.add_morph. replace (/ 2 + / 2) with 1 by field. apply R2.mul_1.
Qed.

Lemma middle_comm : forall ptx pty,
    R2.eq (R2.middle ptx pty) (R2.middle pty ptx).
Proof.
  intros ptx pty.
  unfold R2.middle.
  rewrite R2.add_comm.
  reflexivity.
Qed.

Lemma middle_shift : forall ptx pty, R2.eq (R2.middle ptx pty - ptx) (pty - R2.middle ptx pty).
Proof. unfold R2.middle. unfoldR2. destruct ptx, pty; simpl; hnf; f_equal; field. Qed.

Lemma middle_eq : forall ptx pty,
    R2.eq (R2.middle ptx pty) ptx <-> R2.eq ptx pty.
Proof.
  unfold R2.middle, R2.eq, R2def.eq.
  intros [? ?] [? ?].
  split; intro h.
  - inversion h; clear h; f_equal; lra.
  - inversion_clear h.
    cbv.
    f_equal; lra.
Qed.

Lemma middle_spec : forall pt1 pt2, is_middle pt1 pt2 (R2.middle pt1 pt2).
Proof.
intros pt1 pt2 pt.
setoid_rewrite R2.dist_sym. rewrite R2dist_middle, middle_comm, R2dist_middle, R2.dist_sym.
rewrite R_sqr.Rsqr_mult. unfold Rsqr at 1 3. field_simplify.
transitivity ((R2.dist pt1 pt + R2.dist pt2 pt)² / 2).
+ replace (2 * (R2.dist pt2 pt1)² / 4) with ((R2.dist pt2 pt1)² / 2) by field.
  cut ((R2.dist pt2 pt1)² <= (R2.dist pt1 pt + R2.dist pt2 pt)²); try lra; [].
  rewrite pos_Rsqr_le.
  - rewrite (R2.dist_sym pt pt1), Rplus_comm. apply R2.triang_ineq.
  - apply R2.dist_pos.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply R2.dist_pos.
+ assert (Hle : 0 <= (R2.dist pt1 pt - R2.dist pt2 pt)²) by apply Rle_0_sqr.
  rewrite R_sqr.Rsqr_minus in Hle. rewrite R_sqr.Rsqr_plus. lra.
Qed.

(* This is true because we use the euclidean distance. *)
Lemma middle_is_R2middle : forall pt1 pt2 pt, is_middle pt1 pt2 pt -> R2.eq pt (R2.middle pt1 pt2).
Proof.
intros pt1 pt2 pt Hpt. specialize (Hpt (R2.middle pt1 pt2)).
(* First, we simplify out R2.middle pt1 pt2. *)
assert (Hmid : (R2.dist (R2.middle pt1 pt2) pt1)² + (R2.dist (R2.middle pt1 pt2) pt2)² = (R2.dist pt1 pt2)² / 2).
{ setoid_rewrite R2.dist_sym. rewrite R2dist_middle, middle_comm, R2dist_middle.
  rewrite (R2.dist_sym pt1 pt2). rewrite R_sqr.Rsqr_mult. unfold Rsqr. field. }
rewrite Hmid in Hpt.
(* Then, we prove that pt is at the same distance of pt1 and pt2. *)
assert (Hle : (R2.dist pt1 pt2)² <= (R2.dist pt1 pt + R2.dist pt pt2)²).
{ rewrite pos_Rsqr_le.
  - apply R2.triang_ineq.
  - apply R2.dist_pos.
  - replace 0 with (0 + 0) by ring. apply Rplus_le_compat; apply R2.dist_pos. }
assert (Hpt' : 2 * (R2.dist pt pt1)² + 2 * (R2.dist pt pt2)² <= (R2.dist pt1 pt2)²) by lra.
clear Hpt. rename Hpt' into Hpt.
rewrite R_sqr.Rsqr_plus in Hle.
assert (Heq0 : (R2.dist pt1 pt - R2.dist pt pt2)² = 0).
{ apply antisymmetry.
  - rewrite R_sqr.Rsqr_minus. apply Rle_minus. rewrite R2.dist_sym in Hpt. lra.
  - apply Rle_0_sqr. }
apply Rsqr_0_uniq in Heq0. apply Rminus_diag_uniq in Heq0.
(* That distance is half the distance between pt1 and pt2. *)
assert (Hhalf : R2.dist pt1 pt = R2.dist pt1 pt2 / 2).
{ apply antisymmetry.
  + rewrite <- pos_Rsqr_le.
    - rewrite <- Heq0 in *. rewrite (R2.dist_sym pt1 pt) in Hpt. ring_simplify in Hpt.
      unfold Rdiv. rewrite R_sqr.Rsqr_mult. unfold Rsqr in *. lra.
    - apply R2.dist_pos.
    - assert (Rpos := R2.dist_pos pt1 pt2). lra.
  + assert (Hgoal := R2.triang_ineq pt1 pt pt2). lra. }
(* now, we rule out the dummy case pt1 = pt2. *)
destruct (R2.eq_dec pt1 pt2) as [Heq12 | Heq12].
+ rewrite Heq12, R2_dist_defined_2 in Hhalf.
  replace (0/2) with 0 in Hhalf by field. rewrite R2.dist_defined in Hhalf.
  rewrite <- Hhalf, Heq12. unfold R2.middle. destruct pt2; simpl; hnf; f_equal; field.
+ (* Finally, we use the specification of segment bisector and prove that k is 0. *)
  rewrite segment_bisector_spec in Heq0; trivial; [].
  destruct Heq0 as [k Heq]. rewrite Heq.
  cut (k = 0); try (now intro; subst; rewrite R2.mul_0, R2.add_origin); [].
  rewrite R2.dist_sym, R2norm_dist, Heq in Hhalf. apply (f_equal Rsqr) in Hhalf. revert Hhalf.
  replace (R2.middle pt1 pt2 + k * orthogonal (pt2 - pt1) - pt1)%R2
    with (1 / 2 * (pt2 - pt1) + k * orthogonal (pt2 - pt1))%R2.
  - rewrite R2norm_add. repeat rewrite ?R2norm_mul, ?R_sqr.Rsqr_mult, <- ?R_sqr.Rsqr_abs.
    rewrite product_mul_l, product_mul_r. rewrite orthogonal_perpendicular.
    assert (pt2 - pt1 <> R2.origin)%R2.
    { rewrite <- R2.dist_defined. rewrite <- (R2add_dist pt1).
      setoid_rewrite R2.add_comm at 3. rewrite R2.add_origin.
      rewrite <- R2.add_assoc. setoid_rewrite R2.add_comm at 2. rewrite R2.add_opp, R2.add_origin.
      rewrite R2.dist_sym. rewrite R2.dist_defined. auto. }
    rewrite R2norm_orthogonal; trivial; [].
    rewrite R_sqr.Rsqr_1, Rmult_1_r. repeat rewrite Rmult_0_r. rewrite Rplus_0_r.
    rewrite R2.dist_sym, R2norm_dist. setoid_rewrite R_sqr.Rsqr_div; try lra.
    unfold Rsqr. intro. assert (Hk : k*k = 0) by lra.
    now apply Rsqr_0_uniq.
  - unfold R2.middle. destruct pt1, pt2; simpl. f_equal; field;
    rewrite R2norm_0; unfold R2.origin, R2def.origin; intros [= ? ?]; apply Heq12; hnf; f_equal; lra.
Qed.

Corollary is_middle_uniq : forall pt1 pt2 mid1 mid2,
  is_middle pt1 pt2 mid1 -> is_middle pt1 pt2 mid2 -> mid1 = mid2.
Proof. intros ? ? ? ? H1 H2. apply middle_is_R2middle in H1. apply middle_is_R2middle in H2. congruence. Qed.

Lemma colinear_middle : forall pt1 pt2, colinear (pt2 - pt1) (pt2 - R2.middle pt1 pt2).
Proof.
intros pt1 pt2.
destruct (R2.eq_dec pt1 pt2) as [Heq | Hneq].
+ rewrite Heq, R2.add_opp. apply colinear_origin_l.
+ assert (Hmid : ~R2.eq (pt2 - R2.middle pt1 pt2) R2.origin).
  { intro Habs. apply Hneq. unfold R2.middle. destruct pt1, pt2; compute in *.
    injection Habs. intros. f_equal; lra. }
  unfold colinear, orthogonal, perpendicular, R2.middle, product.
  destruct pt1 as [x1 y1], pt2 as [x2 y2]. cbn. field.
  now rewrite R2norm_0.
Qed.

(* TODO? *)
Axiom bary3_spec: forall pt1 pt2 pt3,
  is_barycenter_3_pts pt1 pt2 pt3 (barycenter_3_pts pt1 pt2 pt3).
Axiom bary3_unique: forall x y z a b,
    is_barycenter_3_pts x y z a -> is_barycenter_3_pts x y z b -> R2.eq a b.


(** **  Circles and SEC  *)

(** ***  General results about circles  **)

Record circle := {
  center : R2.t;
  radius : R}.

Definition enclosing_circle (c : circle) l := forall x, In x l -> R2.dist x (center c) <= (radius c).
Definition on_circle (c : circle) x := Rdec_bool (R2.dist x (center c)) (radius c).

Instance enclosing_circle_compat : forall c, Proper (@Permutation _ ==> iff) (enclosing_circle c).
Proof.
repeat intro. unfold enclosing_circle.
do 2 rewrite <- Forall_forall. apply Forall_Permutation_compat; trivial.
intros ? ? ?. now subst.
Qed.

Instance on_circle_compat : Proper (eq ==> R2.eq ==> eq) on_circle.
Proof. repeat intro. unfoldR2 in H0. now subst. Qed.

Lemma on_circle_true_iff : forall c pt, on_circle c pt = true <-> R2.dist pt (center c) = radius c.
Proof. intros c pt. unfold on_circle. now rewrite Rdec_bool_true_iff. Qed.

(* If the radius of circle is not zero then the center is not part of it. *)
Lemma center_not_on_circle : forall c,
    on_circle c (center c) = false <-> radius  c<> 0%R.
Proof.
  intro.
  split;[ intros hrad | intro honcirc];unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
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

(* useless
(** If two radii are clinear, they form a diameter of the circle. *)
Lemma colinear_diameter : forall pt1 pt2 circ, ~R2.eq pt1 pt2 ->
  on_circle circ pt1 = true -> on_circle circ pt2 = true ->
  (colinear (pt1 - center circ) (pt2 - center circ) <-> R2.eq (center circ) (R2.middle pt1 pt2)).
Proof.
intros pt1 pt2 circ Hneq Hpt1 Hpt2. split; intro H.
* apply colinear_decompose in H.
  + rewrite on_circle_true_iff in *. unfold R2.middle. rewrite <- R2norm_dist in H. destruct H.
    - (* Absurd case: pt1 and pt2 are teh same point *)
      elim Hneq. apply (R2.add_reg_r (- center circ)).
      rewrite H. rewrite Hpt2, <- Hpt1. rewrite R2norm_dist, <- unitary_id. reflexivity.
    - (* Normal case: pt1 and pt2 form a diameter *)
      symmetry. rewrite <- R2sub_origin.
      replace (1/2 * (pt1 + pt2) - center circ)%R2 with (1/2 * (pt1 - center circ) + 1/2 * (pt2 - center circ))%R2
        by (destruct pt1, pt2, (center circ); cbn; hnf; f_equal; field).
      rewrite H. rewrite Hpt2, <- Hpt1.
      rewrite R2norm_dist, R2.minus_morph, <- unitary_id, R2.mul_opp.
      rewrite R2.add_opp. reflexivity.
  + rewrite R2sub_origin. intro Habs.
    assert (Heq0 : radius circ = 0) by now rewrite <- center_on_circle, <- Habs.
    rewrite on_circle_true_iff, Heq0, R2.dist_defined in *. apply Hneq. congruence.
* rewrite H. transitivity (pt2 - pt1)%R2.
  + rewrite <- colinear_opp_compat_r, R2.opp_distr_add, R2.opp_opp, (R2.add_comm (-pt2)).
    rewrite middle_comm. symmetry. apply colinear_middle.
  + apply colinear_middle.
Qed.
*)

(** The vectors generated by three points on a circle cannot be colinear. *)
Lemma circle_not_colinear : forall pt1 pt2 pt3 circ,
  ~R2.eq pt1 pt2 -> ~R2.eq pt1 pt3 -> ~R2.eq pt2 pt3 ->
  on_circle circ pt1 = true -> on_circle circ pt2 = true -> on_circle circ pt3 = true ->
  ~colinear (pt3 - pt2) (pt2 - pt1).
Proof.
intros pt1 pt2 pt3 circ Hneq12 Hneq13 Hneq23 Hpt1 Hpt2 Hpt3 Hcol.
apply colinear_decompose in Hcol; try (rewrite R2sub_origin; congruence); [].
rewrite on_circle_true_iff in *.
Admitted.

Lemma simple_system : forall u1 u2 v1 v2 x y A B : R,
  ~(u1 = 0 /\ u2 = 0) -> (* non null vector *)
  u1 * v2 - u2 * v1 <> 0 -> (* non colinear vectors *)
  (x * u1 = y * v1 + A /\ x * u2 = y * v2 + B
  <-> y = (u2 * A - u1 * B) / (u1 * v2 - u2 * v1)
      /\ (u2 <> 0 /\ x = y * v2 / u2 + B / u2 \/ u1 <> 0 /\ x = y * v1 / u1 + A / u1)).
Proof.
intros u1 u2 v1 v2 x y A B Hnull Hproduct.
split; intro Hequations.
+ destruct Hequations as [Heqn1 Heqn2].
  assert (Hor : u1 <> 0 \/ u2 <> 0) by lra.
  clear Hnull. destruct Hor; split.
  - apply (f_equal (Rmult u1)) in Heqn2.
    replace (u1 * (x * u2)) with (u2 * (x * u1)) in Heqn2 by ring.
    rewrite Heqn1 in Heqn2.
    assert (Heqn_y : (u1 * v2 - u2 * v1) * y = u2 * A - u1 * B) by lra.
    rewrite <- Heqn_y. now field.
  - right; split; trivial. apply Rmult_eq_reg_l with u1; trivial. rewrite Rmult_comm, Heqn1. now field.
  - apply (f_equal (Rmult u2)) in Heqn1.
    replace (u2 * (x * u1)) with (u1 * (x * u2)) in Heqn1 by ring.
    rewrite Heqn2 in Heqn1.
    assert (Heqn_y : (u1 * v2 - u2 * v1) * y = u2 * A - u1 * B) by lra.
    rewrite <- Heqn_y. now field.
  - left; split; trivial. apply Rmult_eq_reg_l with u2; trivial. rewrite Rmult_comm, Heqn2. now field.
+ destruct Hequations as [? [[? ?] | [? ?]]]; subst; now split; field.
Qed.

(* Another (but hardcore) solution would be to solve analytically the equation system giving the position
   of the center, thus it would be unique. Then finding the radius is (comparatively) easy. *)
Lemma three_points_same_circle : forall c1 c2 pt1 pt2 pt3,
  NoDup (pt1 :: pt2 :: pt3 :: nil) ->
  on_circle c1 pt1 = true -> on_circle c1 pt2 = true -> on_circle c1 pt3 = true ->
  on_circle c2 pt1 = true -> on_circle c2 pt2 = true -> on_circle c2 pt3 = true ->
  c1 = c2.
Proof.
intros [c1 r1] [c2 r2] pt1 pt2 pt3 Hnodup Hc1_pt1 Hc1_pt2 Hc1_pt3 Hc2_pt1 Hc2_pt2 Hc2_pt3.
assert (Hneq12 : ~R2.eq pt1 pt2). { inversion_clear Hnodup. simpl in *. intuition. }
assert (Hneq13 : ~R2.eq pt1 pt3). { inversion_clear Hnodup. simpl in *. intuition. }
assert (Hneq23 : ~R2.eq pt2 pt3). { inversion_clear Hnodup. inversion_clear H0. simpl in *. intuition. }
pose (n21 := R2norm (pt2 - pt1)). pose (n32 := R2norm (pt3 - pt2)).
assert (Hnorm21 : n21 <> 0).
{ unfold n21. rewrite R2norm_0. rewrite <- (R2.add_opp pt1). intro Habs. apply Hneq12.
  destruct pt1, pt2; cbn in Habs; hnf in Habs; injection Habs; intros; hnf; f_equal; lra. }
assert (Hnorm32 : n32 <> 0).
{ unfold n32. rewrite R2norm_0. rewrite <- (R2.add_opp pt2). intro Habs. apply Hneq23.
  destruct pt2, pt3; cbn in Habs; hnf in Habs; injection Habs; intros; hnf; f_equal; lra. }
assert (Hcol : ~colinear (pt3 - pt2) (pt2 - pt1))
  by now apply (circle_not_colinear {| center := c1; radius := r1 |}).
unfold on_circle in *; cbn in *; rewrite Rdec_bool_true_iff, R2.dist_sym in *.
(* We caracterise the location of c1 as the intersection of two segment bisectors. *)
assert (Heq12 : R2.dist pt1 c1 = R2.dist c1 pt2) by (rewrite R2.dist_sym in Hc1_pt1; congruence).
rewrite segment_bisector_spec in Heq12; trivial; []. destruct Heq12  as [k1 Hk1].
assert (Heq23 : R2.dist pt2 c1 = R2.dist c1 pt3) by (rewrite R2.dist_sym in Hc1_pt2; congruence).
rewrite segment_bisector_spec in Heq23; trivial; []. destruct Heq23  as [k1' Hk1'].
(* Falling back on coordinates, we get a 2x2 system. *)
assert (Heqn := Hk1'). rewrite Hk1 in Heqn.
unfold R2.middle in Heqn. cbn in Heqn. fold n21 n32 in Heqn.
destruct c1 as [x_c1 y_c1], pt1 as [x_pt1 y_pt1], pt2 as [x_pt2 y_pt2], pt3 as [x_pt3 y_pt3].
cbn in Heqn. hnf in Heqn.
assert (Heqn1 := f_equal fst Heqn). assert (Heqn2 := f_equal snd Heqn). simpl in Heqn1, Heqn2.
clear Heqn.
assert (Heqn1' : k1 * (/ n21 * (y_pt2 + - y_pt1))
                 = k1' * (/ n32 * (y_pt3 + - y_pt2)) + 1 / 2 * (x_pt3 - x_pt1)) by lra.
assert (Heqn2' : k1 * (/ n21 * - (x_pt2 + - x_pt1))
                 = k1' * (/ n32 * - (x_pt3 + - x_pt2))   + 1 / 2 * (y_pt3 - y_pt1)) by lra.
assert (Hequations := conj Heqn1' Heqn2').
clear Heqn1 Heqn2 Heqn1' Heqn2'.
assert (Hinv_n21 := Rinv_neq_0_compat _ Hnorm21).
assert (Hnull : ~ (/ n21 * (y_pt2 + - y_pt1) = 0 /\ / n21 * - (x_pt2 + - x_pt1) = 0)).
{ intro Habs. apply Hneq12. hnf. destruct Habs. f_equal.
  - cut ((x_pt2 + - x_pt1) = 0); try lra; []. setoid_rewrite <- Ropp_involutive. f_equal. rewrite Ropp_0.
    apply Rmult_eq_reg_l with (/n21); trivial; []. rewrite H0. lra.
  - cut ((y_pt2 + - y_pt1) = 0); try lra; [].
    apply Rmult_eq_reg_l with (/n21); trivial; []. rewrite H. lra. }
(* The vectors are not parallel. *)
assert (Hindep : / n21 * (y_pt2 + - y_pt1) * (/ n32 * - (x_pt3 + - x_pt2)) -
                 / n21 * - (x_pt2 + - x_pt1) * (/ n32 * (y_pt3 + - y_pt2)) <> 0).
{ clear -Hcol Hnorm21 Hnorm32. unfold colinear, orthogonal in Hcol.
  rewrite perpendicular_mul_compat_r_iff in Hcol; try (now unfold n21 in Hnorm21; apply Rinv_neq_0_compat); [].
  simpl in Hcol.
  replace (/ n21 * (y_pt2 + - y_pt1) * (/ n32 * - (x_pt3 + - x_pt2)) -
           / n21 * - (x_pt2 + - x_pt1) * (/ n32 * (y_pt3 + - y_pt2)))
    with (/ n21 * / n32 * ((y_pt2 - y_pt1) * (x_pt2 - x_pt3) - (y_pt3 - y_pt2) * (x_pt1 - x_pt2))) by ring.
  apply Rinv_neq_0_compat in Hnorm21. apply Rinv_neq_0_compat in Hnorm32.
  repeat apply Rmult_integral_contrapositive_currified; trivial; [].
  unfold perpendicular, product in Hcol. simpl in Hcol. lra. }
rewrite simple_system in Hequations; trivial.
destruct Hequations as [Hval_k1' _].
(* Idem for c2. *)
assert (Heq12 : R2.dist (x_pt1, y_pt1) c2 = R2.dist c2  (x_pt2, y_pt2))
  by (rewrite R2.dist_sym in Hc2_pt1; congruence).
rewrite segment_bisector_spec in Heq12; try (now intuition); []. destruct Heq12  as [k2 Hk2].
assert (Heq23 : R2.dist  (x_pt2, y_pt2) c2 = R2.dist c2 (x_pt3, y_pt3))
  by (rewrite R2.dist_sym in Hc2_pt2; congruence).
rewrite segment_bisector_spec in Heq23; try (now intuition); []. destruct Heq23  as [k2' Hk2'].
(* We get the second 2x2 system. *)
assert (Heqn := Hk2'). rewrite Hk2 in Heqn.
unfold R2.middle, orthogonal in Heqn. fold n21 n32 in Heqn. cbn in Heqn. 
destruct c2 as [x_c2 y_c2]. cbn in Heqn. hnf in Heqn.
assert (Heqn1 := f_equal fst Heqn). assert (Heqn2 := f_equal snd Heqn). simpl in Heqn1, Heqn2.
clear Heqn.
assert (Heqn1' : k2 * (/ n21 * (y_pt2 + - y_pt1))
                 = k2' * (/ n32 * (y_pt3 + - y_pt2)) + 1 / 2 * (x_pt3 - x_pt1)) by lra.
assert (Heqn2' : k2 * (/ n21 * - (x_pt2 + - x_pt1))
                 = k2' * (/ n32 * - (x_pt3 + - x_pt2))   + 1 / 2 * (y_pt3 - y_pt1)) by lra.
assert (Hequations := conj Heqn1' Heqn2').
clear Heqn1 Heqn2 Heqn1' Heqn2'.
rewrite simple_system in Hequations; trivial.
destruct Hequations as [Hval_k2' _].
assert (Heq_c : R2.eq (x_c1, y_c1) (x_c2, y_c2)).
{ rewrite Hk1', Hk2'. subst. reflexivity. }
f_equal.
- assumption.
- rewrite <- Hc1_pt1, <- Hc2_pt1. rewrite Heq_c. reflexivity.
Qed.

(** ***  Definition of the [SEC]  **)

(** We assume the existence of a primitive SEC computing the smallest enclosing circle,
    given by center and radius. *)
Parameter SEC : list R2.t -> circle.
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
+ transitivity (R2.dist pt (center (SEC (pt :: l)))).
  - apply R2.dist_pos.
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

Definition max_dist pt l := List.fold_left (fun r x => Rmax r (R2.dist x pt)) l 0%R.

Lemma max_dist_le_acc : forall pt l acc, acc <= List.fold_left (fun r x => Rmax r (R2.dist x pt)) l acc.
Proof.
intros pt l. induction l as [| e l]; intro acc; simpl.
+ apply Rle_refl.
+ apply Rle_trans with (Rmax acc (R2.dist e pt)).
  - apply Rmax_l.
  - apply IHl.
Qed.

Corollary max_dist_pos : forall pt l, 0 <= max_dist pt l.
Proof. intros. apply max_dist_le_acc. Qed.

(*
Lemma max_dist_le_mono : forall pt l, Proper (Rle ==> Rle) (List.fold_left (fun r x => Rmax r (R2.dist x pt)) l).
Proof.
intros pt l. induction l; intros acc1 acc2 Hle; simpl.
+ assumption.
+ apply IHl. now apply Rle_max_compat_r.
Qed.
*)
Lemma max_dist_cons : forall pt x l, max_dist pt (x :: l) = Rmax (R2.dist x pt) (max_dist pt l).
Proof.
intros. unfold max_dist. simpl. generalize 0%R. induction l; intro acc; simpl.
+ apply Rmax_comm.
+ rewrite <- IHl. f_equal. setoid_rewrite <- Rmax_assoc. f_equal. apply Rmax_comm.
Qed.

Lemma max_dist_le : forall pt x l, In x l -> R2.dist x pt <= max_dist pt l.
Proof.
intros pt x l Hin.
unfold max_dist. generalize 0. induction l as [| e l]; intro acc; simpl.
* elim Hin.
* destruct Hin as [? | Hin]; subst.
  + apply Rle_trans with (Rmax acc (R2.dist x pt)).
    - apply Rmax_r.
    - apply max_dist_le_acc.
  + now apply IHl.
Qed.

Lemma max_dist_exists : forall pt l, l <> nil -> exists x, In x l /\ R2.dist x pt = max_dist pt l.
Proof.
intros pt l Hl. induction l as [| e1 l].
* now elim Hl.
* destruct l as [| e2 l].
  + exists e1. split; try now left. unfold max_dist. simpl. symmetry. apply Rmax_right. apply R2.dist_pos.
  + destruct (Rle_dec (R2.dist e1 pt) (max_dist pt (e2 :: l))).
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


Lemma SEC_reached : forall l, l <> nil ->
  exists pt, In pt l /\ on_circle (SEC l) pt = true.
Proof.
intros. unfold on_circle. rewrite radius_is_max_dist.
setoid_rewrite Rdec_bool_true_iff. now apply max_dist_exists.
Qed.


Lemma max_dist_singleton: forall pt x, max_dist pt (x::nil) = R2.dist x pt.
Proof.
  intros pt x.
  rewrite max_dist_cons.
  cbn.
  apply Rmax_left.
  apply R2.dist_pos.
Qed.

Lemma enclosing_singleton : forall pt, enclosing_circle {| center := pt; radius := 0 |} (pt :: nil).
Proof.
  intros pt.
  red.
  intros pt' H.
  cbn.
  inversion H.
  - subst.
    destruct (R2.dist_defined pt' pt').
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
- simpl. rewrite radius_is_max_dist, max_dist_singleton. apply R2.dist_pos.
Qed.

(* OK even when the points are the same *)
Lemma SEC_dueton : forall pt1 pt2,
  SEC (pt1 :: pt2 :: nil) = {| center := R2.middle pt1 pt2; radius := /2 * R2.dist pt1 pt2 |}.
Proof.
intros pt1 pt2. symmetry. apply SEC_unicity.
* intros pt Hin. simpl. inversion_clear Hin.
  + subst. now rewrite R2dist_middle.
  + inversion H; easy || subst. now rewrite middle_comm, R2dist_middle, R2.dist_sym.
* simpl. rewrite <- R2dist_middle. rewrite radius_is_max_dist.
  pose (c := center (SEC (pt1 :: pt2 :: nil))). fold c. cbn.
  rewrite (Rmax_right 0); try apply R2.dist_pos; [].
  rewrite <- pos_Rsqr_le.
  + cut ((R2.dist pt1 (R2.middle pt1 pt2))² + (R2.dist pt1 (R2.middle pt1 pt2))² <=
      (Rmax (R2.dist pt1 c) (R2.dist pt2 c))² + (Rmax (R2.dist pt1 c) (R2.dist pt2 c))²); try lra; [].
    transitivity ((R2.dist pt1 c)² + (R2.dist pt2 c)²).
    - assert (Heq : R2.dist pt1 (R2.middle pt1 pt2) = R2.dist pt2 (R2.middle pt1 pt2)).
      { now rewrite R2dist_middle, middle_comm, R2dist_middle, R2.dist_sym. }
      rewrite Heq at 2. setoid_rewrite R2.dist_sym. apply (middle_spec pt1 pt2 c).
    - apply Rplus_le_compat; rewrite pos_Rsqr_le;
      solve [apply Rmax_l | apply Rmax_r | apply R2.dist_pos | apply Rmax_case; apply R2.dist_pos].
  + apply R2.dist_pos.
  + apply Rmax_case; apply R2.dist_pos.
Qed.

Function farthest_from_in c acc inl :=
match inl with
| nil => c
| cons x inl' =>
  if Rle_dec (R2.dist x c) (R2.dist c acc)
  then farthest_from_in c acc inl' else farthest_from_in c x inl'
end.

Lemma farthest_In: forall c acc inl,
    farthest_from_in c acc inl = c \/
    farthest_from_in c acc inl = acc \/
    In (farthest_from_in c acc inl) inl.
Proof.
  intros c acc inl.
  functional induction (farthest_from_in c acc inl);auto.
  - destruct IHt as [IHt1 | [IHt2 | IHt3]];auto.
    cbn;auto.
  - destruct IHt as [IHt1 | [IHt2 | IHt3]];cbn;auto.
Qed.

Lemma farthest_In_c: forall c inl,
    farthest_from_in c c inl = c \/
    In (farthest_from_in c c inl) inl.
Proof.
  intros c inl.
  generalize (farthest_In c c inl).
  intros H.
  intuition.
Qed.

Function farthest_from_in_except (except c acc : R2.t) inl :=
match inl with
| nil => acc
| cons x inl' =>
  if R2.eq_dec x except then farthest_from_in_except except c acc inl'
  else if Rle_dec (R2.dist x c) (R2.dist c acc)
  then farthest_from_in_except except c acc inl' else farthest_from_in_except except c x inl'
end.

Lemma farthest_from_in_exc_In : forall except c acc inl,
    farthest_from_in_except except c acc inl = acc \/
    In (farthest_from_in_except except c acc inl) inl.
Proof.
intros except c acc inl.
functional induction (farthest_from_in_except except c acc inl); auto;
destruct IHt as [? | ?]; cbn; auto.
Qed.

Lemma farthest_from_in_except_In : forall exc c l, (exists pt, pt <> exc /\ In pt l) ->
  In (farthest_from_in_except exc c c l) l.
Proof.
intros exc c l Hl. induction l as [| e l].
* now elim Hl.
* cbn. destruct (R2.eq_dec e exc) as [Heq | Heq].
  + rewrite Heq in *. destruct l.
    - destruct Hl as [pt' [Habs Hin]]. elim Habs. now inversion Hin.
    - right. apply IHl. destruct Hl as [pt' [Hneq Hin]]. exists pt'. split; trivial.
      inversion Hin; subst; trivial; now elim Hneq.
  + destruct (Rle_dec (R2.dist e c) (R2.dist c c)) as [H | H].
    - assert (He : R2.eq e c).
      { rewrite <- R2.dist_defined. transitivity (R2.dist c c).
        + apply Rle_antisym; trivial.
          rewrite R2_dist_defined_2. apply R2.dist_pos.
        + apply R2_dist_defined_2. }
      rewrite He. destruct (farthest_from_in_exc_In exc c c l); intuition.
    - destruct (farthest_from_in_exc_In exc c e l); intuition.
Qed.

Lemma farthest_from_in_except_diff : forall exc c acc l, acc <> exc -> farthest_from_in_except exc c acc l <> exc.
Proof.
intros exc c acc l. revert acc. induction l as [| e l]; intros acc Hdiff; cbn.
- assumption.
- destruct (R2.eq_dec e exc); auto.
  destruct (Rle_dec (R2.dist e c) (R2.dist c acc)); auto.
Qed.

Lemma farthest_from_in_except_le_acc : forall exc c l acc,
  R2.dist c acc <= R2.dist c (farthest_from_in_except exc c acc l).
Proof.
intros exc c l. induction l as [| e l]; intro acc; cbn.
+ apply Rle_refl.
+ destruct (R2.eq_dec e exc); auto.
  destruct (Rle_dec (R2.dist e c) (R2.dist c acc)) as [? | Hnle]; auto.
  apply Rnot_le_lt in Hnle. eapply Rle_trans.
  - apply Rlt_le. eassumption.
  - rewrite R2.dist_sym. apply IHl.
Qed.

Lemma farthest_from_in_except_le : forall exc c l acc x,
  In x l -> x <> exc -> R2.dist c x <= R2.dist c (farthest_from_in_except exc c acc l).
Proof.
intros exc c l. induction l as [| e l]; intros acc x Hin Hneq.
* inversion Hin.
* inversion_clear Hin.
  + subst. clear IHl. cbn. destruct (R2.eq_dec x exc); try now cbn in *; contradiction.
    destruct (Rle_dec (R2.dist x c) (R2.dist c acc)) as [Hle | Hlt].
    - rewrite R2.dist_sym. eapply Rle_trans; try eassumption. apply farthest_from_in_except_le_acc.
    - apply farthest_from_in_except_le_acc.
  + cbn. destruct (R2.eq_dec e exc); auto. destruct (Rle_dec (R2.dist e c) (R2.dist c acc)); auto.
Qed.

Lemma SEC_zero_radius_incl_singleton : forall l,
  radius (SEC l) = 0%R <-> exists pt, incl l (pt :: nil).
Proof.
intro l.
destruct l as [| e l].
* rewrite SEC_nil. intuition. exists (0, 0). intuition.
* split; intro H.
  + exists (center (SEC (e :: l))).
    intros x Hin. left. symmetry. rewrite <- R2.dist_defined. apply Rle_antisym.
    - rewrite <- H. now apply SEC_spec1.
    - apply R2.dist_pos.
  + destruct H as [pt Hl].
    assert (Hall : forall x, In x (e :: l) -> x = pt). { intros ? Hin. apply Hl in Hin. now inversion_clear Hin. }
    clear Hl. apply Rle_antisym.
    - pose (c := {| center := pt; radius := 0 |}).
      change 0 with (radius c). apply SEC_spec2.
      intros x Hin. rewrite (Hall _ Hin). cbn. now rewrite R2_dist_defined_2.
    - transitivity (R2.dist pt (center (SEC (e :: l)))).
      -- apply R2.dist_pos.
      -- apply SEC_spec1. rewrite (Hall e ltac:(now left)). now left.
Qed.

(* Idea:
   We already know that there is one point on the circle.
   If there is no other, we take the furthest point from c strictly inside the disk.
   We decrease the center and radius to make it end up on the circle.
   Thus, the original SEC was not minimal, a contradiction. *)
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
+ intro x. destruct (R2.eq_dec x pt1) as [Heq | Heq].
  - right. intuition.
  - destruct (on_circle (SEC (pt1 :: l)) x); intuition.
+ (* If there is another point on the sphere *)
  rewrite Exists_exists in HOK. destruct HOK as [pt2 [Hin2 Heq2]].
  exists pt2; intuition.
+ (* If all other points are inside the sphere, we can slightly reduce its radius by moving the center *)
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
  pose (d := R2.dist c pt2). (* the maximum distance to c (except pt1) *)
  pose (r' := Rdiv (r + d) 2). (* the new radius *)
  pose (c' := (c + ((1 - r' / r) * (pt1 - c)))%R2). (* the new center *)
  assert (Hin2 : In pt2 l).
  { apply farthest_from_in_except_In. destruct l as [| e l].
    - cbn in Hl. omega.
    - inversion_clear Hnodup. cbn in H. exists e. intuition. }
  assert (Hmax : forall x, In x l -> x <> pt1 -> R2.dist c x <= d).
  { intros. unfold d, pt2. now apply farthest_from_in_except_le. }
  assert (Hr2 : 0 < r). { apply Rle_neq_lt; auto. unfold r. apply SEC_radius_pos. }
  assert (Hr' : 0 <= r'). { assert (0 <= d). { unfold d. apply R2.dist_pos. } unfold r'. lra. }
  (* The new circle has a smaller radius *)
  assert (Hlt : r' < r).
  { unfold r'. cut (d < r); try lra; [].
    apply Rle_neq_lt.
    ++ unfold d, r, c. rewrite R2.dist_sym. apply SEC_spec1. now right.
    ++ intro. do 2 subst. apply Hsmall. rewrite Exists_exists. exists pt2. repeat split.
       -- now right.
       -- clear -Hon1 Hnodup Hin2. unfold pt2. apply farthest_from_in_except_diff. intro Heq. subst.
          rewrite <- Heq in Hon1 at 2. rewrite center_on_circle, SEC_zero_radius_incl_singleton in Hon1.
          destruct Hon1 as [pt Hincl].
          assert (pt = pt1). { specialize (Hincl pt1 ltac:(intuition)). simpl in Hincl. intuition. }
          assert (Hpt : pt = pt2). { specialize (Hincl pt2 ltac:(intuition)). simpl in Hincl. intuition. }
          subst pt. inversion_clear Hnodup. apply H. now rewrite Hpt.
       -- rewrite on_circle_true_iff. now rewrite R2.dist_sym. }
  (* Yet, it is still enclosing *)
  assert (Hnew : enclosing_circle {| center := c'; radius := r' |} (pt1 :: l)).
  { intros pt Hin. cbn. destruct Hin.
    * subst pt. unfold c'. rewrite R2dist_ref_0.
      replace (pt1 - (c + (1 - r'/r) * (pt1 - c)))%R2 with (r'/ r * pt1 - (r' / r * c))%R2
        by (destruct pt1, c; unfoldR2; cbn; f_equal; ring).
      rewrite <- R2dist_ref_0. rewrite R2mul_dist.
      rewrite on_circle_true_iff in Hon1. unfold c. rewrite Hon1.
      fold r. rewrite Rabs_pos_eq; [field_simplify; lra |].
      unfold Rdiv. now apply Fourier_util.Rle_mult_inv_pos.
    * transitivity (R2.dist pt c + R2.dist c c'); [| transitivity (d + R2.dist c c')].
      + apply R2.triang_ineq.
      + apply Rplus_le_compat_r. rewrite R2.dist_sym. unfold d, pt2.
        apply farthest_from_in_except_le; trivial. intro. subst. inversion_clear Hnodup. contradiction.
      + unfold c'. rewrite R2dist_ref_0.
        replace (c - (c + (1 - r' / r) * (pt1 - c)))%R2 with ((1 - r' / r) * c - ((1 - r' / r) * pt1))%R2
          by (destruct pt1, c; unfoldR2; cbn; f_equal; ring).
        rewrite <- R2dist_ref_0. rewrite R2mul_dist. rewrite on_circle_true_iff in Hon1.
        unfold c. rewrite R2.dist_sym. rewrite Hon1. fold r.
        rewrite Rabs_pos_eq.
        - unfold r'. now field_simplify.
        - cut (r' / r <= 1); try lra. unfold Rdiv. rewrite <- (Rinv_r r); trivial. auto with real. }
  (* A contradiction *)
  apply (Rle_not_lt r' r); trivial.
  unfold r. change r' with (radius {| center := c'; radius := r' |}).
  now apply SEC_spec2.
Qed.

(** ***  Results about [on_SEC]  **)

Lemma on_SEC_nil : forall l, on_SEC l = nil <-> l = nil.
Proof.
intro l. split; intro H.
- destruct l; trivial. exfalso.
  destruct (@SEC_reached (t :: l)) as [pt Hpt]; try discriminate.
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
destruct (Rdec_bool (R2.dist pt1 (R2.middle pt1 pt2)) (/ 2 * R2.dist pt1 pt2)) eqn:Hpt1.
- destruct (Rdec_bool (R2.dist pt2 (R2.middle pt1 pt2)) (/ 2 * R2.dist pt1 pt2)) eqn:Hpt2; trivial.
  exfalso.
  rewrite Rdec_bool_false_iff in Hpt2. apply Hpt2.
  setoid_rewrite R2.dist_sym at 2. rewrite middle_comm. setoid_rewrite R2dist_ref_0.
  unfold R2.middle. rewrite <- (Rabs_pos_eq (/2)); try lra. rewrite <- R2mul_dist, R2.mul_origin. f_equal.
  destruct pt1, pt2. compute. f_equal; field.
- exfalso.
  rewrite Rdec_bool_false_iff in Hpt1. apply Hpt1.
  setoid_rewrite R2dist_ref_0.
  unfold R2.middle. rewrite <- (Rabs_pos_eq (/2)); try lra. rewrite <- R2mul_dist, R2.mul_origin. f_equal.
  destruct pt1, pt2. compute. f_equal; field.
Qed.

Lemma enclosing_twice_same_SEC : forall l1 l2,
  enclosing_circle (SEC l1) l2 -> enclosing_circle (SEC l2) l1 -> SEC l1 = SEC l2.
Proof.
intros l1 l2 Hencl12 Hencl21. apply SEC_unicity.
- assumption.
- now apply SEC_spec2.
Qed.

Lemma SEC_min_radius : forall pt1 pt2 l, In pt1 l -> In pt2 l -> /2 * R2.dist pt1 pt2 <= radius (SEC l).
Proof.
intros pt1 pt2 l Hpt1 Hpt2.
assert (Hperm : exists l', Permutation l (pt1 :: l')).
{ rewrite <- InA_Leibniz in Hpt1. setoid_rewrite <- PermutationA_Leibniz.
  apply PermutationA_split; autoclass. }
destruct Hperm as [l' Hperm]. rewrite Hperm in *. clear Hpt1 Hperm l.
destruct (R2.eq_dec pt1 pt2) as [Heq | Heq].
+ rewrite Heq. rewrite R2_dist_defined_2. replace (/2 * 0) with 0 by ring.
  rewrite radius_is_max_dist. apply max_dist_pos.
+ assert (Hperm : exists l, Permutation l' (pt2 :: l)).
  { rewrite <- InA_Leibniz in Hpt2. setoid_rewrite <- PermutationA_Leibniz.
    apply PermutationA_split; autoclass.
    inversion_clear Hpt2; trivial. subst. now elim Heq. }
  destruct Hperm as [l Hperm]. rewrite Hperm in *. clear Hpt2 Hperm l'.
  change (/2 * R2.dist pt1 pt2) with (radius {| center := R2.middle pt1 pt2; radius := /2 * R2.dist pt1 pt2 |}).
  rewrite <- SEC_dueton. apply SEC_incl_compat. intro. cbn. intuition.
Qed.

Lemma SEC_add_same :
  forall pt l, R2.dist pt (center (SEC l)) <= radius (SEC l)
               -> (SEC (pt :: l)) = SEC l.
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

Lemma on_SEC_add_same : forall pt l, R2.dist pt (center (SEC l)) < radius (SEC l) ->
  equivlistA R2.eq (on_SEC (pt :: l)) (on_SEC l).
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

Lemma SEC_append_same : forall l1 l2, (forall pt, In pt l1 -> R2.dist pt (center (SEC l2)) <= radius (SEC l2))
               -> SEC (l1 ++ l2) = SEC l2.
Proof.
intros l1 l2 Hl1. induction l1.
- reflexivity.
- cbn.
  assert (Hrec : forall pt : R2.t, In pt l1 -> R2.dist pt (center (SEC l2)) <= radius (SEC l2)).
  { intros pt Hin. apply Hl1. now right. }
  specialize (IHl1 Hrec). rewrite <- IHl1.
  apply SEC_add_same. rewrite IHl1. apply Hl1. now left.
Qed.

Lemma middle_in_SEC_diameter : forall pt1 pt2,
  R2.dist (R2.middle pt1 pt2) (center (SEC (pt1 :: pt2 :: nil))) <= radius (SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2.
rewrite SEC_dueton. cbn.
rewrite R2_dist_defined_2, <- (Rmult_0_l 0).
apply Rmult_le_compat; try lra; [].
apply R2.dist_pos.
Qed.

Lemma middle_strictly_in_SEC_diameter : forall pt1 pt2, pt1 <> pt2 ->
  R2.dist (R2.middle pt1 pt2) (center (SEC (pt1 :: pt2 :: nil))) < radius (SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2 Hdiff.
assert (Hle := middle_in_SEC_diameter pt1 pt2). destruct Hle as [Hlt | Heq]; trivial.
rewrite SEC_dueton in Heq. simpl in Heq. rewrite R2_dist_defined_2 in Heq.
assert (Hsame : R2.dist pt1 pt2 = 0) by lra. now rewrite R2.dist_defined in Hsame.
Qed.

Lemma SEC_middle_diameter : forall pt1 pt2, SEC (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil) = SEC (pt1 :: pt2 :: nil).
Proof. intros. apply SEC_add_same, middle_in_SEC_diameter. Qed.

Require Pactole.MMultiset.Preliminary.
Lemma on_SEC_NoDupA : forall l, NoDupA R2.eq l -> NoDupA R2.eq (on_SEC l).
Proof. intros. unfold on_SEC. now apply (Preliminary.NoDupA_filter_compat _). Qed.

Lemma on_SEC_middle_diameter : forall pt1 pt2, pt1 <> pt2 ->
  PermutationA R2.eq (on_SEC (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)) (on_SEC (pt1 :: pt2 :: nil)).
Proof.
intros pt1 pt2 Hdiff.
assert (R2.middle pt1 pt2 <> pt1). { rewrite <- middle_eq in Hdiff. intuition. }
assert (R2.middle pt1 pt2 <> pt2).
{ assert (Hdiff' : pt2 <> pt1) by intuition. rewrite <- middle_eq in Hdiff'. rewrite middle_comm. intuition. }
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

(* TODO? *)
Lemma SEC_on_SEC : forall l, SEC l = SEC (on_SEC l).
Proof.
intro l.
assert (Hperm := partition_Permutation (on_circle (SEC l)) l).
rewrite Permutation_app_comm, MMultiset.Preliminary.partition_filter in Hperm. simpl in Hperm.
rewrite <- Hperm at 1. unfold on_SEC.
apply SEC_append_same.
intros pt Hin.
rewrite filter_In, Bool.negb_true_iff in Hin. destruct Hin as [Hin Hout].
apply SEC_spec1.
Admitted.

Corollary on_SEC_idempotent : forall l, PermutationA R2.eq (on_SEC (on_SEC l)) (on_SEC l).
Proof. intro l. unfold on_SEC at 1 3. unfold on_SEC at 2. rewrite (SEC_on_SEC l). now rewrite filter_twice. Qed.

Lemma on_SEC_pair_is_diameter : forall pt1 pt2 l, on_SEC l = pt1 :: pt2 :: nil ->
  SEC l = {| center := R2.middle pt1 pt2; radius := /2 * R2.dist pt1 pt2 |}.
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


Lemma barycenter_3_pts_inside_SEC : forall pt1 pt2 pt3,
  R2.dist (barycenter_3_pts pt1 pt2 pt3) (center (SEC (pt1 :: pt2 :: pt3 :: nil)))
  <= radius (SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof.
intros pt1 pt2 pt3. unfold barycenter_3_pts. do 2 rewrite R2.mul_distr_add.
remember (center (SEC (pt1 :: pt2 :: pt3 :: nil))) as c.
transitivity (R2.dist (/3 * pt1) (/3 * c) + R2.dist (/3 * pt2) (/3 * c) + R2.dist (/3 * pt3) (/3 * c)).
+ replace c with (/3 * c + (/3 * c + /3 * c))%R2 at 1.
  - etransitivity. apply R2dist_subadditive. rewrite Rplus_assoc.
    apply Rplus_le_compat; try reflexivity. apply R2dist_subadditive.
  - clear Heqc. destruct c. compute. f_equal; field.
+ repeat rewrite R2mul_dist; try lra; [].
  rewrite (Rabs_pos_eq (/3) ltac:(lra)).
  remember (radius (SEC (pt1 :: pt2 :: pt3 :: nil))) as r.
  replace r with (/3 * r + /3 * r + /3 * r) by field.
  repeat apply Rplus_le_compat; (apply Rmult_le_compat; try lra || apply R2.dist_pos; []);
  subst; apply SEC_spec1; intuition.
Qed.

Lemma triangle_barycenter_inside_aux : forall pt1 pt2,
  pt1 <> pt2 -> on_circle (SEC (pt1 :: pt1 :: pt2 :: nil)) (barycenter_3_pts pt1 pt1 pt2) = false.
Proof.
intros pt1 pt2 Hneq.
rewrite SEC_add_same.
- rewrite SEC_dueton. apply Bool.not_true_iff_false. rewrite on_circle_true_iff. simpl.
  rewrite square_dist_equiv; try (now assert (Hle := R2.dist_pos pt1 pt2); lra); [].
  unfold barycenter_3_pts, R2.middle. rewrite square_dist_simpl, R_sqr.Rsqr_mult, square_dist_simpl.
  intro Habs. apply Hneq. destruct pt1, pt2; simpl in Habs. unfold Rsqr in Habs. field_simplify in Habs.
  pose (x := (r² + r1² - 2 * r * r1) + (r0² + r2² - 2 * r0 * r2)).
  assert (Heq0 : x = 0). { unfold x. unfold Rsqr in *. field_simplify in Habs. field_simplify. lra. }
  clear Habs. unfold x in *. clear x. do 2 rewrite <- R_sqr.Rsqr_minus in Heq0.
  apply Rplus_eq_R0 in Heq0; try apply Rle_0_sqr; []. unfold Rsqr in Heq0. destruct Heq0 as [Heq0 Heq0'].
  apply Rsqr_0_uniq in Heq0. apply Rsqr_0_uniq in Heq0'. f_equal; lra.
- apply SEC_spec1. intuition.
Qed.

(* TODO *)
Lemma triangle_barycenter_inside : forall pt1 pt2 pt3,
  ~(pt1 = pt2 /\ pt1 = pt3) -> on_circle (SEC (pt1 :: pt2 :: pt3 :: nil)) (barycenter_3_pts pt1 pt2 pt3) = false.
Proof.
intros pt1 pt2 pt3 Hneq.
destruct (R2.eq_dec pt1 pt2) as [Heq12 | Heq12];
[| destruct (R2.eq_dec pt1 pt3) as [Heq13 | Heq13]; [| destruct (R2.eq_dec pt2 pt3) as [Heq23 | Heq23]]].
* assert (Hneq12 : pt1 <> pt3) by now intro; subst; auto. rewrite <- Heq12.
  now apply triangle_barycenter_inside_aux.
* rewrite <- Heq13.
  assert (Hperm : Permutation (pt1 :: pt2 :: pt1 :: nil) (pt1 :: pt1 :: pt2 :: nil)) by do 2 constructor.
  rewrite Hperm. rewrite (barycenter_3_pts_compat Hperm). apply triangle_barycenter_inside_aux. auto.
* rewrite <- Heq23.
  assert (Hperm : Permutation (pt1 :: pt2 :: pt2 :: nil) (pt2 :: pt2 :: pt1 :: nil)) by now do 3 econstructor.
  rewrite Hperm. rewrite (barycenter_3_pts_compat Hperm). apply triangle_barycenter_inside_aux. auto.
* assert (Hnodup : NoDup (pt1 :: pt2 :: pt3 :: nil)) by (repeat constructor; simpl in *; intuition).
  destruct (on_SEC (pt1 :: pt2 :: pt3 :: nil)) as [| pt1' [| pt2' [| pt3' [| ? ?]]]] eqn:Hsec.
  + rewrite on_SEC_nil in Hsec. discriminate.
  + apply on_SEC_singleton_is_singleton in Hsec; trivial. discriminate.
  + apply on_SEC_pair_is_diameter in Hsec. rewrite Hsec. apply Bool.not_true_iff_false.
    rewrite on_circle_true_iff. simpl.
    rewrite square_dist_equiv; try (now assert (Hle := R2.dist_pos pt1' pt2'); lra); [].
    unfold barycenter_3_pts, R2.middle. rewrite square_dist_simpl, R_sqr.Rsqr_mult, square_dist_simpl.
    destruct pt1, pt2, pt3, pt1', pt2'; simpl. unfold Rsqr. intro Habs. field_simplify in Habs.
    admit.
  + assert (Hperm : Permutation (pt1' :: pt2' :: pt3' :: nil) (pt1 :: pt2 :: pt3 :: nil)).
    { rewrite <- PermutationA_Leibniz. rewrite <- NoDupA_Leibniz in Hnodup.
      apply (NoDupA_inclA_length_PermutationA _); trivial.
      - rewrite <- Hsec. now apply on_SEC_NoDupA.
      - rewrite <- Hsec. unfold on_SEC. intros ? Hin. now rewrite (filter_InA _) in Hin. }
    rewrite <- Hsec in Hperm.
    admit.
  + assert (Hle : (length (on_SEC (pt1 :: pt2 :: pt3 :: nil)) <= 3)%nat).
    { unfold on_SEC. rewrite filter_length. simpl length at 1. omega. }
    rewrite Hsec in Hle. simpl in Hle. omega.
Admitted.

Lemma barycenter_3_pts_strictly_inside_SEC : forall pt1 pt2 pt3, ~(pt1 = pt2 /\ pt1 = pt3) ->
  R2.dist (barycenter_3_pts pt1 pt2 pt3) (center (SEC (pt1 :: pt2 :: pt3 :: nil)))
  < radius (SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof.
intros pt1 pt2 pt3 Hdiff.
assert (Hle := barycenter_3_pts_inside_SEC pt1 pt2 pt3).
destruct Hle as [? | Heq]; trivial.
assert (Hcircle : on_circle (SEC (pt1 :: pt2 :: pt3 :: nil)) (barycenter_3_pts pt1 pt2 pt3) = false).
{ destruct (R2.eq_dec pt1 pt2).
  - assert (Hperm : PermutationA R2.eq (pt1 :: pt2 :: pt3 :: nil) (pt1 :: pt3 :: pt2 :: nil)).
    { now repeat constructor. }
    rewrite Hperm. rewrite PermutationA_Leibniz in Hperm. rewrite (barycenter_3_pts_compat Hperm).
    apply triangle_barycenter_inside. intro. intuition.
  - now apply triangle_barycenter_inside. }
unfold on_circle in Hcircle. rewrite Rdec_bool_false_iff in Hcircle. contradiction.
Qed.

Lemma on_SEC_barycenter_triangle : forall pt1 pt2 pt3, ~(pt1 = pt2 /\ pt1 = pt3) ->
  equivlistA R2.eq (on_SEC (barycenter_3_pts pt1 pt2 pt3 :: pt1 :: pt2 :: pt3 :: nil))
                   (on_SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof. intros. now apply on_SEC_add_same, barycenter_3_pts_strictly_inside_SEC. Qed.

Axiom equilateral_SEC : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Equilateral ->
  SEC (pt1 :: pt2 :: pt3 :: nil) =
  {| center := barycenter_3_pts pt1 pt2 pt3;
     radius := R2.dist (barycenter_3_pts pt1 pt2 pt3) pt1 |}.

Lemma equilateral_barycenter_not_eq : forall pt1 pt2 pt3,
  classify_triangle pt1 pt2 pt3 = Equilateral -> pt1 <> pt2 -> barycenter_3_pts pt1 pt2 pt3 <> pt1.
Proof.
intros pt1 pt2 pt3 Htriangle Hneq.
assert (Hcenter : center (SEC (pt1 :: pt2 :: pt3 :: nil)) = barycenter_3_pts pt1 pt2 pt3).
{ apply equilateral_SEC in Htriangle. now rewrite Htriangle. }
assert (Hradius : radius (SEC (pt1 :: pt2 :: pt3 :: nil)) = R2.dist (barycenter_3_pts pt1 pt2 pt3) pt1).
{ apply equilateral_SEC in Htriangle. now rewrite Htriangle. }
rewrite <- R2.dist_defined. rewrite <- Hradius, <- center_on_circle.
rewrite Hcenter. now rewrite triangle_barycenter_inside.
Qed.

Lemma equilateral_NoDupA : forall ptx pty ptz,
  classify_triangle ptx pty ptz = Equilateral -> ptx <> pty ->
  NoDupA R2.eq (ptx :: pty :: ptz :: nil).
Proof.
intros ptx pty ptz Htriangle Hdiff.
functional induction (classify_triangle ptx pty ptz) as [Heq1 Heq2 | | | |]; try discriminate.
rewrite Rdec_bool_true_iff in *. repeat constructor; intro Hin;
repeat match goal with
  | H : R2.eq _ _ |- _ => rewrite H in *
  | H : InA _ _ _ |- _ => inversion_clear H
end.
- now elim Hdiff.
- rewrite R2_dist_defined_2 in *. symmetry in Heq2. rewrite R2.dist_defined in Heq2. now symmetry in Heq2.
- rewrite R2_dist_defined_2 in *. now rewrite R2.dist_defined in Heq1.
Qed.

Lemma equilateral_barycenter_NoDupA : forall ptx pty ptz,
  classify_triangle ptx pty ptz = Equilateral -> ptx <> pty ->
  NoDupA R2.eq (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil).
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
    intro. subst.
    rewrite R2_dist_defined_2 in *. symmetry in Heq1. now rewrite R2.dist_defined in Heq1.
- now apply equilateral_NoDupA.
Qed.
