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


(* For the triangle inequality *)
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

Lemma pos_sqrt_eq : forall x y, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof. Admitted.

Lemma sqrt_sqrt_id : forall x, 0 <= x -> Rpow_def.pow (sqrt x) 2 = x.
Proof. Admitted.

Lemma Rsqr_pos : forall x, 0 <= x * x.
Proof.
intro. rewrite <- (Rmult_0_l 0). destruct (Rle_lt_dec 0 x).
- apply Rmult_le_compat; lra.
- replace (x * x) with (-x * -x) by ring. apply Rmult_le_compat; lra.
Qed.

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
apply pos_sqrt_eq.
- apply sqrt_pos.
- apply Rmult_le_pos; apply Rabs_pos || apply sqrt_pos.
- assert (Heq := R_sqr.Rsqr_abs k). unfold Rsqr in Heq. ring_simplify in Heq.
  unfold Rsqr. ring_simplify. rewrite <- Heq. repeat rewrite sqrt_sqrt_id.
  + cbn. field.
  + rewrite <- Rplus_0_l at 1. apply Rplus_le_compat; apply Rsqr_pos.
  + rewrite <- Rplus_0_l at 1. apply Rplus_le_compat; apply Rsqr_pos.
Qed.

Lemma R2dist_subadditive : forall u u' v v', R2.dist (u + v) (u' + v') <= R2.dist u u' + R2.dist v v'.
Proof.
intros. etransitivity. apply (R2.triang_ineq _ (u' + v)%R2).
rewrite R2add_dist. setoid_rewrite R2.add_comm. rewrite R2add_dist. reflexivity.
Qed.

Lemma R2dist_ref_0 : forall u v, R2.dist u v = R2.dist (u + - v)%R2 R2.origin.
Proof. intros u v. now rewrite <- (R2add_dist (-v)), R2.add_opp. Qed.


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

(* A location is determined by distances to 3 points. *)
Lemma GPS : forall x y z t1 t2, x <> y -> y <> z -> x <> z ->
  R2.dist t1 x = R2.dist t2 x -> R2.dist t1 y = R2.dist t2 y -> R2.dist t1 z = R2.dist t2 z -> t1 = t2.
Proof.
intros x y z t1 t2 Hxy Hyz Hxz Hx Hy Hz.
Admitted.
Arguments GPS x y z t1 t2 _ _ _ _ _ _ : clear implicits.

Lemma diff_0_1 : ~R2.eq (0, 0) (0, 1).
Proof. intro Heq. inversion Heq. now apply R1_neq_R0. Qed.


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


(** ** Barycenter *)

(* Barycenter is the center of SEC for an equilateral triangle *)

Definition barycenter_3_pts (pt1 pt2 pt3:R2.t) := R2.mul (Rinv 3) (R2.add pt1 (R2.add pt2 pt3)).

Lemma barycenter_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
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
   Take for instance dist(x,y) = 1 <-> x <> y, and pt1, pt2 pt3 different.
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

Axiom middle_spec: forall pt1 pt2, is_middle pt1 pt2 (R2.middle pt1 pt2).
Axiom bary3_spec: forall pt1 pt2 pt3,
  is_barycenter_3_pts pt1 pt2 pt3 (barycenter_3_pts pt1 pt2 pt3).
Axiom middle_unique: forall x y a b, is_middle x y a -> is_middle x y b ->  R2.eq a b.
Axiom bary3_unique: forall x y z a b,
    is_barycenter_3_pts x y z a -> is_barycenter_3_pts x y z b ->  R2.eq a b.

Lemma middle_comm : forall ptx pty,
    R2.eq (R2.middle ptx pty) (R2.middle pty ptx).
Proof.
  intros ptx pty.
  unfold R2.middle.
  rewrite R2.add_comm.
  reflexivity.
Qed.

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


(** **  Circles and SEC  *)

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

Lemma three_points_same_circle : forall c1 c2 pt1 pt2 pt3,
  on_circle c1 pt1 = true -> on_circle c1 pt2 = true -> on_circle c1 pt3 = true ->
  on_circle c2 pt1 = true -> on_circle c2 pt2 = true -> on_circle c2 pt3 = true ->
  c1 = c2.
Proof.
intros [c1 r1] [c2 r2] pt1 pt2 pt3 Hc1_pt1 Hc1_pt2 Hc1_pt3 Hc2_pt1 Hc2_pt2 Hc2_pt3.
unfold on_circle in *; cbn in *; rewrite Rdec_bool_true_iff in *.
Check GPS.
Admitted.


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

(* TODO? *)
Axiom SEC_unicity: forall l c,
    enclosing_circle c l
    -> (radius c <= radius (SEC l))%R
    -> c = SEC l.

Lemma SEC_unicity2 : forall l c, enclosing_circle c l -> (radius c <= radius (SEC l))%R -> c = SEC l.
Proof.
intros l c Henclosing Hradius.
assert (Heq : radius c = radius (SEC l)).
{ apply Rle_antisym; trivial. now apply SEC_spec2. }
clear Hradius.
cut (center c = center (SEC l)).
+ intro Hcenter. destruct c, (SEC l); cbn in *; subst. reflexivity.
+ (* Idea?: If there are only two points on the SEC, they are a diameter.
            Otherwise, three points define a unique circle.
            Therefore, if they are not the same, we have points on one circle but not the other. *)
destruct c as [pt r]. cbn in *. subst. destruct (SEC l). simpl in *.
Abort.

Lemma SEC_singleton : forall pt, SEC (pt :: nil) = {| center := pt; radius := 0 |}.
Proof.
intro pt. symmetry. apply SEC_unicity.
- apply enclosing_singleton.
- simpl. rewrite radius_is_max_dist, max_dist_singleton. apply R2.dist_pos.
Qed.

(* OK even when the points are the same *)
Lemma SEC_dueton : forall pt1 pt2,
  SEC (pt1 :: pt2 :: nil) = {| center := R2.middle pt1 pt2; radius := /2 * R2.dist pt1 pt2 |}.
Proof. Admitted.
(*
Lemma diameter_spec1: forall c (pt1 pt2:R2.t),
    c = SEC (pt1::pt2::nil) ->
    R2.dist pt1 pt2 = (c.(radius) * 2)%R ->
    c.(center) = R2.middle pt1 pt2.
Proof.
  intros c pt1 pt2 H H0.
  assert (R2.dist pt1 c.(center) + R2.dist c.(center) pt2 >= R2.dist pt1 pt2)%R.
  { apply Rle_ge, R2.triang_ineq. }
  rewrite H0 in H1.
  destruct (R2.eq_dec pt1 pt2).
  ++ rewrite ?e in *.
     unfold R2.middle.
     rewrite R2.mul_distr_add.
     rewrite R2.add_morph.
     (assert (h_demi:(1 / 2 + 1 / 2 = 1)%R)).
     { rewrite <- double.
       field. }
     rewrite h_demi.
     rewrite R2.mul_1.
     rewrite R2_dist_defined_2 in H0.
     destruct (Rmult_integral (radius c) 2).
     ** symmetry;assumption.
     ** destruct (@SEC_reached (pt2 :: pt2 :: nil)) as [ x [h1 h2]].
        --- discriminate.
        --- simpl in h1.
            assert (pt2 = x).
            { tauto. }
            clear h1. subst.
            assert (R2.dist (center (SEC (x :: x :: nil))) x = 0%R).
            { unfold on_circle in h2.
              rewrite H2 in h2.
              apply Rdec_bool_true_iff in h2.
              rewrite R2.dist_sym.
              assumption. }
            apply R2.dist_defined.
            assumption.
     ** absurd (0%R = 2%R);auto.
        apply Rlt_not_eq.
        apply Rlt_R0_R2.
  ++ destruct (@SEC_reached_twice (pt1 :: pt2 :: nil)).
     ** auto.
     ** repeat constructor.
        --- intro Habs. inversion Habs.
            +++ symmetry in H2. contradiction.
            +++ inversion H2.
        --- intro Habs. inversion Habs.
     ** decompose [ex and ] H2; clear H2.
        assert (Hpt : x = pt1 /\ x0 = pt2 \/ x0 = pt1 /\ x = pt2).
        { inversion H3; inversion H4;
          repeat match goal with
          | H : In ?x nil  |- _ => inversion H
          | H : In ?x (?y :: nil) |- _ => inversion_clear H; auto
          end; now subst; elim H5.
         }
        assert (on_circle (SEC (pt1 :: pt2 :: nil)) pt1 = true).
        { decompose [and or] Hpt ; subst ; assumption. }
        assert (on_circle (SEC (pt1 :: pt2 :: nil)) pt2 = true).
        { decompose [and or] Hpt ; subst ; assumption. }
        clear dependent x.
        clear dependent x0.
        assert (h_middle: is_middle pt1 pt2 (center c)).
        { red.
          admit. }
        apply (@middle_unique pt1 pt2 (center c) (R2.middle pt1 pt2)).
        assumption.
        apply middle_spec.
Admitted.
*)

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

Lemma R2_dist_defined_2 : forall pt, R2.dist pt pt = 0.
Proof.
  intros pt.
  rewrite R2.dist_defined.
  reflexivity.
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

(* If the radius of SEC is not zero then the center is not part of it. *)
Lemma SEC_non_zero_radius_center : forall l,
    radius (SEC l)<> 0%R
    <-> on_circle (SEC l) (center (SEC l)) = false.
Proof.
  intros l.
  split;[ intros hrad | intro honcirc];unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
  - apply Rdec_bool_false_iff.
    auto.
  - rewrite ?Rdec_bool_false_iff in *.
    auto.
Qed.

Lemma SEC_zero_radius_center : forall l,
  on_circle (SEC l) (center (SEC l)) = true <-> radius (SEC l) = 0%R.
Proof.
  intros l.
  split;[ intros hrad | intro honcirc];unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
  - rewrite ?Rdec_bool_true_iff in *.
    auto.
  - apply Rdec_bool_true_iff.
    auto.
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
Lemma SEC_reached_twice : forall l, (2 <= length l)%nat -> NoDup l -> (* radius (SEC l) <> 0%R -> *)
  exists pt1 pt2, In pt1 l /\ In pt2 l /\ pt1 <> pt2
    /\ on_circle (SEC l) pt1 = true /\ on_circle (SEC l) pt2 = true.
Proof.
intros l Hl Hnodup.
(*assert (on_circle (SEC l) (center (SEC l)) = false).
{ now apply SEC_non_zero_radius_center. }*)
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
  pose (c := center (SEC l)).
  pose (r := radius (SEC l)).
  (* the farthest point of l from c (excluding pt1) *)
  pose (pt := farthest_from_in_except pt1 c c l).
  pose (d := R2.dist c pt). (* the room we have *)
  pose (r' := Rdiv (r + d) 2). (* the new radius *)
  pose (c' := R2.add c (R2.mul (r - r') (R2.add c (R2.opp pt)))). (* the new center *)
  assert (Hin : In pt l).
  { apply farthest_from_in_except_In. destruct l as [| e l].
    - cbn in Hl. omega.
    - inversion_clear Hnodup. cbn in H. exists e. intuition. }
  assert (Hmax : forall x, In x l -> x <> pt1 -> R2.dist c x <= d).
  { intros. unfold d, pt. now apply farthest_from_in_except_le. }
  assert (Hnew : enclosing_circle {| center := c'; radius := r' |} l).
  { admit. }
  (* The final proof *)
  apply (Rle_not_lt r' r).
  - unfold r. change r' with (radius {| center := c'; radius := r' |}).
    now apply SEC_spec2.
  - unfold r'. cut (d < r). lra.
    
Admitted.

Definition on_SEC l := List.filter (on_circle (SEC l)) l.

Instance on_SEC_compat : Proper (PermutationA Logic.eq ==> PermutationA Logic.eq) on_SEC.
Proof.
intros l1 l2 Hl. unfold on_SEC. rewrite Hl at 2.
rewrite filter_extensionality_compat; try reflexivity.
intros ? ? ?. subst. now rewrite Hl.
Qed.

Lemma on_SEC_In : forall pt l, In pt (on_SEC l) <-> In pt l /\ on_circle (SEC l) pt = true.
Proof. intros. unfold on_SEC. apply filter_In. Qed.

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

Lemma on_SEC_pair_is_diameter : forall pt1 pt2 l, on_SEC l = pt1 :: pt2 :: nil ->
  SEC l = {| center := R2.middle pt1 pt2; radius := /2 * R2.dist pt1 pt2 |}.
Proof.
Admitted.

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

Lemma on_SEC_idempotent : forall l, PermutationA R2.eq (on_SEC (on_SEC l)) (on_SEC l).
Proof. Admitted.

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
(*
intro l. unfold on_SEC.
assert ( Hperm := partition_Permutation (on_circle (SEC l)) l).
rewrite <- PermutationA_Leibniz in Hperm. rewrite <- Hperm at 1 3.
rewrite partition_filter in *. cbn in *. rewrite (PermutationA_app_comm _).
remember (filter (fun x : R2.t => negb (on_circle (SEC l) x)) l) as l1.
remember (filter (on_circle (SEC l)) l) as l2.
assert (HinSEC : forall pt, In pt l1 -> R2.dist (center (SEC l2)) pt <= radius (SEC l2)).
{ intros pt Hin. SearchAbout SEC.  }



Qed.
generalize (incl_refl l1). rewrite Heql1 at 2. clear Heql1. intro Hincl.
induction l1 as [| e l1].
- cbn. rewrite app_nil_r in Hperm. unfold on_SEC. subst. now rewrite filter_idempotent.
- cbn. destruct (on_circle (SEC l) e) eqn:He.
  + exfalso. assert (Hin : In e (e :: l1)) by now left.
    apply Hincl in Hin. rewrite filter_In in Hin. destruct Hin as [_ Hin].
    rewrite He in Hin. discriminate.
  + rewrite <- IHl1.
    * apply on_SEC_add_same.
      assert (Hin : In e l).
      { admit. }
      apply SEC_spec1 in Hin.
    * 
    * 

 remember (SEC l) as c.
Qed.
*)

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

Axiom triangle_barycenter_inside : forall pt1 pt2 pt3,
  pt1 <> pt2 -> on_circle (SEC (pt1 :: pt2 :: pt3 :: nil)) (barycenter_3_pts pt1 pt2 pt3) = false.

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
    rewrite Hperm. rewrite PermutationA_Leibniz in Hperm. rewrite (barycenter_compat Hperm).
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
rewrite <- R2.dist_defined. rewrite <- Hradius, <- SEC_zero_radius_center.
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
    rewrite (barycenter_compat Hperm) in H0. rewrite (classify_triangle_compat Hperm) in Htriangle.
    apply (equilateral_barycenter_not_eq _ Htriangle); trivial.
    intuition.
  + assert (Hperm : Permutation (ptx :: pty :: ptz :: nil) (ptz :: ptx :: pty :: nil)).
    { now etransitivity; repeat constructor. }
    rewrite (barycenter_compat Hperm) in H. rewrite (classify_triangle_compat Hperm) in Htriangle.
    apply (equilateral_barycenter_not_eq _ Htriangle); trivial.
    functional induction (classify_triangle ptz ptx pty) as [Heq1 Heq2 | | | |]; try discriminate.
    rewrite Rdec_bool_true_iff in *.
    intro. subst.
    rewrite R2_dist_defined_2 in *. symmetry in Heq1. now rewrite R2.dist_defined in Heq1.
- now apply equilateral_NoDupA.
Qed.
