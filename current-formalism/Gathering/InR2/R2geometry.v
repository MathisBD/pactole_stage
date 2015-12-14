Require Import Rbase R_sqrt Rbasic_fun.
Require Import Psatz.
Require Import RelationPairs.
Require Import Morphisms.
Require Import SetoidPermutation.
Require Import Omega.
Import List Permutation.
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

Lemma pos_sqrt_eq : forall x y, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof. Admitted.

Lemma sqrt_sqrt_id : forall x, 0 <= x -> Rpow_def.pow (sqrt x) 2 = x.
Proof. Admitted.

Lemma mul_dist : forall k u v, 0 <= k -> R2.dist (k * u) (k * v) = k * R2.dist u v.
Proof.
intros k [? ?] [? ?] Hk. unfold R2.dist, R2def.dist. cbn.
apply pos_sqrt_eq.
- apply sqrt_pos.
- apply Rmult_le_pos; trivial. apply sqrt_pos.
- unfold Rsqr. ring_simplify. repeat rewrite sqrt_sqrt_id. 
  + cbn. field.
  + psatz R.
  + psatz R.
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

(** We assume the existence of a primitive SEC computing the smallest enclosing circle,
    given by center and radius. *)
Parameter SEC : list R2.t -> circle.
(** The SEC is an enclosing circle. *)
Axiom SEC_spec1 : forall l, enclosing_circle (SEC l) l.
(** The SEC is the smallest one. *)
Axiom SEC_spec2 : forall l c, enclosing_circle c l -> radius (SEC l) <= radius c.
(** Extra specification in the degenerate case. *)
Axiom SEC_nil : radius (SEC nil) = 0.
(** Its definition does not depend on the representation of points. *)
Declare Instance SEC_compat : Proper (@Permutation _ ==> Logic.eq) SEC.

Global Instance SEC_compat_bis : Proper (PermutationA Logic.eq ==> Logic.eq) SEC.
Proof. intros ? ? Heq. rewrite PermutationA_Leibniz in Heq. now rewrite Heq. Qed.

(* The last axiom is useful because of the following degeneracy fact. *)
Lemma enclosing_circle_nil : forall pt r, enclosing_circle {| center := pt; radius := r |} nil.
Proof. intros. unfold enclosing_circle. intros x Hin. elim Hin. Qed.

Definition center_eq c1 c2 := c1.(center) = c2.(center).
Definition radius_eq c1 c2 := c1.(radius) = c2.(radius).

(** Unicity proof of the radius of the SEC *)
Lemma SEC_radius_compat :
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

Lemma enclosing_singleton : forall x, enclosing_circle {| center := x; radius :=0 |} (x::nil).
Proof.
  intros x.
  red.
  intros x0 H.
  cbn.
  inversion H.
  - subst.
    destruct (R2.dist_defined x0 x0).
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
    on_circle (SEC l) (center (SEC l)) = true
    <-> radius (SEC l) = 0%R.
Proof.
  intros l.
  split;[ intros hrad | intro honcirc];unfold on_circle in *; rewrite ?R2_dist_defined_2 in *; auto.
  - rewrite ?Rdec_bool_true_iff in *.
    auto.
  - apply Rdec_bool_true_iff.
    auto.
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

Lemma on_SEC_add_same :
  forall pt l, R2.dist (center (SEC l)) pt <= radius (SEC l)
               -> (SEC (pt::l)) = SEC l .
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
    destruct hin;subst.
    + rewrite R2.dist_sym.
      assumption.
    + apply SEC_spec1.
      assumption.
Qed.

Lemma barycenter_3_pts_inside_SEC : forall pt1 pt2 pt3,
  R2.dist (barycenter_3_pts pt1 pt2 pt3) (center (SEC (pt1 :: pt2 :: pt3 :: nil))) <= radius (SEC (pt1 :: pt2 :: pt3 :: nil)).
Proof.
intros pt1 pt2 pt3. unfold barycenter_3_pts. do 2 rewrite R2.add_distr.
remember (center (SEC (pt1 :: pt2 :: pt3 :: nil))) as c.
apply Rle_trans with (R2.dist (/3 * pt1) (/3 * c) + R2.dist (/3 * pt2) (/3 * c) + R2.dist (/3 * pt3) (/3 * c)).
(* apply R2.triang_ineq. *)
Admitted.