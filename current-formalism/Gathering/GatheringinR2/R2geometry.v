Require Import Rbase R_sqrt.
Require Import Psatz.
Require Import RelationPairs.
Require Import Morphisms.
Require Import SetoidPermutation.
Import List Permutation.
(*  Rbasic_fun  *)
Require Import Pactole.Preliminary.
Require Import Pactole.Positions.


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
  Admitted.
  
  Lemma add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. solve_R. Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. solve_R. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. solve_R. Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. solve_R. Qed.
  
  Lemma mult_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. solve_R. Qed.
  
  Lemma add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. solve_R. Qed.
  
  Lemma plus_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
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

(* Barycenter is the center of SEC for an equilateral triangle *)
Definition barycenter (pt1 pt2 pt3:R2.t) := R2.mul (Rinv 3) (R2.add pt1 (R2.add pt2 pt3)).

Function opposite_of_max_side (pt1 pt2 pt3 : R2.t) :=
  let len12 := R2.dist pt1 pt2 in
  let len23 := R2.dist pt2 pt3 in
  let len13 := R2.dist pt1 pt3 in
  if Rle_bool len12 len23
  then if Rle_bool len23 len13 then pt2 else pt1
  else if Rle_bool len12 len13 then pt2 else pt3.


Lemma barycenter_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    barycenter pt1 pt2 pt3 =  barycenter pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' Hperm.
  rewrite <- PermutationA_Leibniz, (PermutationA_3 _) in Hperm.
  decompose [or and] Hperm; clear Hperm; subst;
  reflexivity || unfold barycenter; f_equal;
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

(** **  Circles and SEC  *)

Record circle := {
  center : R2.t;
  radius : R}.

Definition enclosing_circle (c : circle) l := List.Forall (fun x => R2.dist x (center c) <= (radius c)) l.
Definition on_circle (c : circle) x := Rdec_bool (R2.dist (center c) x) (radius c).
Locate Permutation.
Instance enclosing_circle_compat : forall c, Proper (@Permutation _ ==> iff) (enclosing_circle c).
Proof. intro. unfold enclosing_circle. apply Forall_Permutation_compat. intros ? ? ?. now subst. Qed.

(** We assume the existence of a primitive SEC computing the smallest enclosing circle,
    given by center and radius. *)
Parameter SEC : list R2.t -> circle.
(** Its definition does not depend on the representation of points. *)
Declare Instance SEC_compat : Proper (@Permutation _ ==> Logic.eq) SEC.
(** The SEC is an enclosing circle. *)
Axiom SEC_spec1 : forall l, enclosing_circle (SEC l) l.
(** The SEC is the smallest one. *)
Axiom SEC_spec2 : forall l c, enclosing_circle c l -> radius (SEC l) <= radius c.
