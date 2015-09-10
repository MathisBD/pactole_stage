(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Positions.
Require Pactole.CommonFormalism.
Require Pactole.RigidFormalism.
Require Import Pactole.GatheringinR.SortingR.
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.Lexprod.


Import Permutation.
Set Implicit Arguments.


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


(** R² as a vector space over R. *)

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


Transparent R2.origin R2def.origin R2.eq_dec R2.eq R2def.eq R2.dist R2def.dist.

Ltac unfoldR2 := unfold R2.origin, R2def.origin, R2.eq_dec, R2.eq, R2def.eq, R2.dist, R2def.dist.

Tactic Notation "unfoldR2" "in" ident(H) :=
  unfold R2.origin, R2def.origin, R2.eq_dec, R2.eq, R2def.eq, R2.dist, R2def.dist in H.

Lemma R2mul_0 : forall u, R2.eq (R2.mul 0 u) R2.origin.
Proof. intros [x y]. compute. now do 2 rewrite Rmult_0_l. Qed.


(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] =>
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | |- context[Rdec 0 1] =>
        let Heq := fresh "Heq" in destruct (Rdec 0 1) as [Heq | Heq];
        [now symmetry in Heq; elim R1_neq_R0 | clear Heq]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ?x <> ?x |- _ => elim H; reflexivity
  end.

Ltac Rdec_full :=
  match goal with
    | |- context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Ltac Rdec_full_in H :=
  match type of H with
    | context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.
Tactic Notation "Rdec_full" "in" ident(H) := Rdec_full_in H.

Record circle := {
  center : R2.t;
  radius : R}.

Definition enclosing_circle (c : circle) l := List.Forall (fun x => R2.dist x (center c) <= (radius c)) l.
Definition on_circle (c : circle) x := Rdec_bool (R2.dist (center c) x) (radius c).

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


Function target_triangle (pt1 pt2 pt3 : R2.t) : R2.t :=
  let typ := classify_triangle pt1 pt2 pt3 in
  match typ with
  | Equilateral => barycenter pt1 pt2 pt3
  | Isosceles p => p
  | Scalene => opposite_of_max_side pt1 pt2 pt3
  end.


Ltac injection_absurd :=
  match goal with
  | H: FinFun.Injective ?f,
       H1: ?f ?a = ?x,
           H2: ?f ?b = ?x |- _ =>
    let h := fresh "habs" in
    assert (h:f a = f b) by (transitivity x;auto);
      apply H in h;discriminate
  | _ => try omega
  end.

Ltac autoinv :=
  repeat match goal with
         | H:Some _ = Some _ |- _ => inversion_clear H
         end.

(* Sans vouloir vous vexer... *)
Check Preliminary.PermutationA_3.

Lemma enum_permut_three : forall A (l l':list A) x1 x2 x3,
    Permutation l l'
    -> l' = (x1 :: x2 :: x3 :: nil)
    -> l = x1 :: x2 :: x3 :: nil
       \/ l = x1 :: x3 :: x2 :: nil
       \/ l = x2::x1::x3::nil
       \/ l = x2 :: x3 :: x1 :: nil
       \/ l = x3::x2::x1::nil
       \/  l = x3::x1::x2::nil.
Proof.
  intros A l l' x1 x2 x3 hpermut heql'.
  specialize (Permutation_nth_error_bis l l').
  intros H.
  destruct H as [H _].
  specialize (H hpermut).
  destruct H as [f [f_inject [f_bound f_permut]]].
  assert (h_lgth:length l = 3%nat).
  { rewrite (Permutation_length hpermut).
    rewrite heql'.
    reflexivity. }
  assert (exists a1 a2 a3, l = a1::a2::a3::nil). {
    repeat (destruct l;simpl in *;try discriminate).
    eauto. }
  destruct H as [a1 [a2 [a3 heql]]].
  rewrite h_lgth in f_bound.
  unfold FinFun.bFun in  f_bound.
  assert (h_ltf0:(f 0 < 3)%nat).
  { apply f_bound;auto. }
  assert (h_ltf1:(f 1 < 3)%nat).
  { apply f_bound;auto. }
  assert (h_ltf2:(f 2 < 3)%nat).
  { apply f_bound;auto. }
  generalize (f_permut 0%nat).
  generalize (f_permut 1%nat).
  generalize (f_permut 2%nat).
  intros hpermut2 hpermut1 hpermut0.
  subst l'; subst l;simpl in *.
  destruct (f O) eqn:heq0; try injection_absurd
  ; destruct (f (S O)) eqn:heq1; try injection_absurd
  ; destruct (f (S (S O))) eqn:heq2;try injection_absurd;simpl in *; autoinv; auto 7
  ;repeat (try destruct n;try injection_absurd;simpl in *; autoinv; auto 7
          ; try destruct n0;try injection_absurd;simpl in *; autoinv; auto 7
          ; try destruct n1;try injection_absurd;simpl in *; autoinv; auto 7).
Qed.

Ltac normalize_R2dist pt1' pt2' pt3' :=
  (repeat progress (rewrite ?Rdec_bool_false_iff
                    , ?Rdec_bool_true_iff , ?(R2.dist_sym pt2' pt1')
                    , ?(R2.dist_sym pt3' pt1'), ?(R2.dist_sym pt3' pt2') in *));
    try match goal with
        | H: ~( _ <= _) |- _ => apply Rnot_le_lt in H
        end.

Lemma barycenter_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    barycenter pt1 pt2 pt3 =  barycenter pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' hpermut.
  remember (pt1 :: pt2 :: pt3 :: nil) as l.
  remember (pt1' :: pt2' :: pt3' :: nil) as l'.
  specialize (@enum_permut_three _ _ _ pt1' pt2' pt3' hpermut Heql').
  intros h.
  decompose [or] h; clear h;
  match goal with
  | H1:l = _ , H2:l = _ |- _ => rewrite H1 in H2; inversion H2; clear H1 H2;subst
  end;clear hpermut;try reflexivity;unfold barycenter; f_equal;
  (* FIXME: find a better way to normalize the sum? field? *)
  repeat progress
         match goal with
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
         end
  ; reflexivity.
Qed.


Lemma classify_triangle_compat: forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    classify_triangle pt1 pt2 pt3 =  classify_triangle pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' hpermut.
  remember (pt1 :: pt2 :: pt3 :: nil) as l.
  remember (pt1' :: pt2' :: pt3' :: nil) as l'.
  specialize (@enum_permut_three _ _ _ pt1' pt2' pt3' hpermut Heql').
  intros h.
  decompose [or] h; clear h;
  match goal with
  | H1:l = _ , H2:l = _ |- _ => rewrite H1 in H2; inversion H2; clear H1 H2;subst
  end;clear hpermut;try reflexivity;
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
(* TODO *)
  intros pt1 pt2 pt3 pt1' pt2' pt3' scalene hpermut.
  generalize (classify_triangle_compat hpermut).
  intro scalene'.
  rewrite scalene in scalene'. symmetry in scalene'.
  functional inversion scalene.
  functional inversion scalene'.
  clear scalene' scalene.
  normalize_R2dist pt1 pt2 pt3.
  normalize_R2dist pt1' pt2' pt3'.
  remember (pt1 :: pt2 :: pt3 :: nil) as l.
  remember (pt1' :: pt2' :: pt3' :: nil) as l'.
  specialize (@enum_permut_three _ _ _ pt1' pt2' pt3' hpermut Heql').
  intros h.
  decompose [or] h; clear h;
  match goal with
  | H1:l = _ , H2:l = _ |- _ => rewrite H1 in H2; inversion H2; clear H1 H2;subst
  end ;clear hpermut;try reflexivity;
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

Lemma target_triangle_compat : forall pt1 pt2 pt3 pt1' pt2' pt3',
    Permutation (pt1 :: pt2 :: pt3 :: nil) (pt1' :: pt2' :: pt3' :: nil) ->
    target_triangle pt1 pt2 pt3 = target_triangle pt1' pt2' pt3'.
Proof.
  intros pt1 pt2 pt3 pt1' pt2' pt3' hpermut.
  generalize (classify_triangle_compat hpermut).
  intro h_classify.
  functional induction (target_triangle pt1 pt2 pt3)
  ;generalize h_classify; intro h_classify'
  ;symmetry in h_classify';rewrite e in h_classify';unfold target_triangle
  ;rewrite h_classify';auto.
  - apply barycenter_compat;auto.
  - apply opposite_of_max_side_compat;auto.
Qed.



(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to position.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR2.

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter nG: nat.
Hypothesis nG_pos : (3 <= nG)%nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.


(** The spectrum is a multiset of positions *)
Module Spect := MultisetSpectrum.Make(R2)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 2, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Common := CommonRealFormalism.Make(R2)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(R2)(N)(Spect)(Common).
Close Scope R_scope.
Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

Lemma map_sim_support : forall (sim : Sim.t) s,
  Permutation (Spect.support (Spect.map sim s)) (map sim (Spect.support s)).
Proof.
intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_support.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.empty.
Proof.
intros conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.multiset_empty in Heq.
assert (Hlgth:= Spect.Pos.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
unfold N.nB, N.nG in *.
cut (3 <= 0). omega.
rewrite Hlgth at 2. rewrite plus_0_r. apply nG_pos.
Qed.

(* FIXME: These three definitions: gathered_at, gather and WillGather
   should be shared by all our proofs about gathering (on Q, R, R2,
   for impossibility and possibility proofs). Shouldn't they be in a
   module? We could even add a generic notion of forbidden
   configurations.

 TODO: "position" should be renamed into "configuration".*)

(** [gathered_at pos pt] means that in configuration [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive gather (pt: R2.t) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> gather pt (execution_tail e) -> gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive willGather (pt : R2.t) (e : execution) : Prop :=
  | Now : gather pt e -> willGather pt e
  | Later : willGather pt (execution_tail e) -> willGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these positions as [forbidden]. *)
Definition forbidden (config : Pos.t) :=
  Nat.Even N.nG /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : R2.t, willGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R2.t, willGather pt (execute r d config).


(** **  Some results about R with respect to distance and similarities  **)

Open Scope R_scope.

(* A location is determined by distances to 3 points. *)
(*
Lemma dist_case : forall x y, R2.dist x y = x - y \/ R2.dist x y = y - x.
Proof.
unfold R.dist, Rdef.dist. intros x y. destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. lra.t
- apply Rabs_left in Hlt. lra.
Qed.

Lemma dist_locate : forall x y k, R.dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.
*)
Lemma GPS : forall x y z t1 t2, x <> y -> y <> z -> x <> z ->
  R2.dist t1 x = R2.dist t2 x -> R2.dist t1 y = R2.dist t2 y -> R2.dist t1 z = R2.dist t2 z -> t1 = t2.
Proof.
intros x y z t1 t2 Hxy Hyz Hxz Hx Hy Hz.
Admitted.
Arguments GPS x y z t1 t2 _ _ _ _ _ _ : clear implicits.

Lemma diff_0_1 : ~R2.eq (0, 0) (0, 1).
Proof. intro Heq. inversion Heq. now apply R1_neq_R0. Qed.

Lemma three_fixpoints_is_id : forall sim : Sim.t,
  (exists pt1 pt2 pt3 : R2.t, pt1 <> pt2 /\ pt1 <> pt3 /\ pt2 <> pt3
                           /\ sim pt1 = pt1 /\ sim pt2 = pt2 /\ sim pt3 = pt3) ->
  Sim.eq sim Sim.id.
Proof.
intros sim [pt1 [pt2 [pt3 [Hneq12 [Hneq23 [Hneq13 [Hpt1 [Hpt2 Hpt3]]]]]]]] x y Hxy.
assert (Hzoom : sim.(Sim.zoom) = 1).
{ apply (Rmult_eq_reg_r (R2.dist pt1 pt2)). rewrite <- sim.(Sim.dist_prop).
  - rewrite Hpt1, Hpt2. ring.
  - rewrite R2.dist_defined. assumption. }
rewrite Hxy. apply (GPS pt1 pt2 pt3); trivial.
- rewrite <- Hpt1 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
- rewrite <- Hpt2 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
- rewrite <- Hpt3 at 1. rewrite sim.(Sim.dist_prop). rewrite Hzoom. simpl. ring.
Qed.

(** Definition of rotations *)

Definition rotate_bij (θ : R) : Similarity.bijection R2.eq.
refine {|
  Similarity.section := fun r => (cos θ * fst r - sin θ * snd r, sin θ * fst r + cos θ * snd r);
  Similarity.retraction := fun r => (cos (-θ) * fst r - sin (-θ) * snd r, sin (-θ) * fst r + cos (-θ) * snd r) |}.
Proof.
unfold R2.eq, R2def.eq.
abstract (intros xy xy'; split; intro; subst; destruct xy as [x y] || destruct xy' as [x y]; simpl;
rewrite Rtrigo1.cos_neg, Rtrigo1.sin_neg; f_equal; ring_simplify ; do 2 rewrite <- Rfunctions.Rsqr_pow2;
rewrite <- (Rmult_1_l x) at 3 || rewrite <- (Rmult_1_l y) at 3; rewrite <- (Rtrigo1.sin2_cos2 θ); ring).
Defined.

Lemma arith : forall (θ : R) (x y : R2.t),
  (cos θ)² * (fst x)² - 2 * (cos θ)² * fst x * fst y + (cos θ)² * (snd x)² -
  2 * (cos θ)² * snd x * snd y + (cos θ)² * (fst y)² + (cos θ)² * (snd y)² +
  (fst x)² * (sin θ)² - 2 * fst x * (sin θ)² * fst y + (sin θ)² * (snd x)² -
  2 * (sin θ)² * snd x * snd y + (sin θ)² * (fst y)² + (sin θ)² * (snd y)² =
  (fst x)² - 2 * fst x * fst y + (snd x)² - 2 * snd x * snd y + (fst y)² + (snd y)².
Proof.
(* AACtactics should help with rewriting by sin2_cos2 here *)
Admitted.


Definition rotate (θ : R) : Sim.t.
refine {|
  Sim.sim_f := rotate_bij θ;
  Sim.zoom := 1;
  Sim.center := (0, 0) |}.
Proof.
+ simpl. unfoldR2. abstract(f_equal; field).
+ unfoldR2. intros. rewrite Rmult_1_l. f_equal. simpl.
repeat rewrite Rfunctions.Rsqr_pow2; ring_simplify; repeat rewrite <- Rfunctions.Rsqr_pow2.
apply arith.
Defined.

Lemma rotate_inverse : forall θ, Sim.eq ((rotate θ)⁻¹) (rotate (-θ)).
Proof. intros θ x y Hxy. now rewrite Hxy. Qed.

Lemma rotate_mul_comm : forall θ k u, R2.eq (rotate θ (R2.mul k u)) (R2.mul k (rotate θ u)).
Proof. intros θ k [x y]. unfoldR2. simpl. f_equal; field. Qed.

Lemma rotate_opp_comm : forall θ u, R2.eq (rotate θ (R2.opp u)) (R2.opp (rotate θ u)).
Proof. intros θ [? ?]. unfoldR2. simpl. f_equal; field. Qed.

Lemma rotate_add_distr : forall θ u v, R2.eq (rotate θ (R2.add u v)) (R2.add (rotate θ u) (rotate θ v)).
Proof. intros θ [? ?] [? ?]. unfoldR2. simpl. f_equal; field. Qed.

(** A similarity in R2 is described by its ratio, center and rotation angle. *)
Theorem similarity_in_R2 : forall sim : Sim.t, exists θ,
  forall x, sim x = R2.mul sim.(Sim.zoom) (rotate θ (R2.add x (R2.opp sim.(Sim.center)))).
Proof.
intro sim. assert (Hkpos : 0 < sim.(Sim.zoom)) by apply Sim.zoom_pos.
destruct sim as [f k c Hc Hk]. simpl in *. unfoldR2 in Hc.

Admitted.

Corollary inverse_similarity_in_R2 : forall (sim : Sim.t) θ,
  (forall x, sim x = sim.(Sim.zoom) * (rotate θ (x + (- sim.(Sim.center)))))%R2 ->
  (forall x, R2.eq ((sim ⁻¹) x) ((/sim.(Sim.zoom)) *
                                  (rotate (-θ) (x + (sim.(Sim.zoom) * rotate θ sim.(Sim.center)))))%R2).
Proof.
intros sim θ Hdirect x. cbn -[rotate].
rewrite <- sim.(Similarity.Inversion). rewrite Hdirect. clear Hdirect.
assert (Sim.zoom sim <> 0) by apply Sim.zoom_non_null.
setoid_rewrite <- rotate_mul_comm. rewrite R2.add_distr. rewrite R2.mult_morph.
replace (Sim.zoom sim * / Sim.zoom sim) with 1 by (now field). rewrite R2.mul_1.
repeat rewrite rotate_add_distr. rewrite <- rotate_inverse.
(* Does not work! Sniff...
match goal with |- context[(rotate θ) ((rotate θ ⁻¹) ?x)] => idtac "found";
change ((rotate θ) ((rotate θ ⁻¹) x)) with (Sim.compose (rotate θ) (rotate θ ⁻¹) x) end *)
change ((rotate θ) ((rotate θ ⁻¹) x)) with (Sim.compose (rotate θ) (rotate θ ⁻¹) x).
change ((rotate θ) ((rotate θ ⁻¹) (Sim.zoom sim *  (rotate θ) (Sim.center sim))%R2))
  with (Sim.compose (rotate θ) (rotate θ ⁻¹) (Sim.zoom sim * (rotate θ) (Sim.center sim))%R2).
rewrite Sim.compose_inverse_r.
unfoldR2. destruct x as [x1 x2], sim as [f k [c1 c2] ? ?]; simpl in *. f_equal; field.
Qed.

Lemma sim_Minjective : forall (sim : Sim.t), MMultiset.Preliminary.injective R2.eq R2.eq sim.
Proof. apply Sim.injective. Qed.

Hint Immediate sim_Minjective.

Instance forbidden_compat : Proper (Pos.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [pt1 [pt2 [Hneq Hpt]]]]; split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

(* cf algo in 1D, should be in the multiset library *)
Parameter Smax : Spect.t -> Spect.t.
Declare Instance Smax_compat : Proper (Spect.eq ==> Spect.eq) Smax.
Axiom Smax_morph : forall f s, Spect.eq (Smax (Spect.map f s)) (Spect.map f (Smax s)).
Axiom Smax_empty : forall s, Spect.eq (Smax s) Spect.empty <-> Spect.eq s Spect.empty.

(* Safe to use only when SEC is well-defined, ie when robots are not gathered. *)
Function target (s : Spect.t) : R2.t :=
  let l := Spect.support s in
  let sec := List.filter (on_circle (SEC l)) l in
  match sec with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* gathered *)
    | pt1 :: pt2 :: nil => R2.middle pt1 pt2
    | pt1 :: pt2 :: pt3 :: nil => (* triangle cases *)
      target_triangle pt1 pt2 pt3
    | _ => (* general case *) center (SEC l)
  end.



Instance target_compat : Proper (Spect.eq ==> Logic.eq) target.
Proof.
intros s1 s2 Hs. unfold target.
assert (Hperm : Permutation (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1))
                            (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))).
{ rewrite <- PermutationA_Leibniz. etransitivity.
  - apply (filter_PermutationA_compat _); refine _. now rewrite Hs.
  - rewrite filter_extensionality_compat; try reflexivity.
    intros x y Hxy. subst. f_equal. f_equiv. rewrite <- PermutationA_Leibniz. now rewrite Hs. }
destruct (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
+ apply Permutation_nil in Hperm. now rewrite Hperm.
+ apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
+ apply Permutation_length_2_inv in Hperm.
  destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial.
  unfold R2.middle. now rewrite R2.add_comm.
+ assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) =3%nat) by now rewrite <- Hperm.
  destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
    as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
  apply target_triangle_compat;assumption.
+ assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) = 4 + length l)%nat
    by now rewrite <- Hperm.
  destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
    as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
  f_equal. f_equiv. rewrite <- PermutationA_Leibniz. now rewrite Hs.
Qed.

Definition SECT (s : Spect.t) : list R2.t :=
  let l := Spect.support s in
  target s :: List.filter (on_circle (SEC l)) l.

Instance SECT_compat : Proper (Spect.eq ==> @Permutation _) SECT.
Proof.
intros s1 s2 Hs. unfold SECT. rewrite Hs at 1. constructor.
etransitivity.
- rewrite <- PermutationA_Leibniz. apply (filter_PermutationA_compat _); refine _. rewrite Hs. reflexivity.
- rewrite filter_extensionality_compat; try reflexivity.
  intros ? ? ?. subst. f_equal. f_equiv. rewrite <- PermutationA_Leibniz. now rewrite Hs.
Qed.

Definition SECT_cardinal s :=
  Spect.cardinal (Spect.filter (fun x => if List.in_dec R2.eq_dec x (SECT s) then true else false) s).

Instance SECT_cardinal_compat : Proper (Spect.eq ==> Logic.eq) SECT_cardinal.
Proof.
intros s1 s2 Hs. unfold SECT_cardinal. f_equiv. rewrite Hs.
apply Spect.filter_extensionality_compat.
- intros x y Hxy. now rewrite Hxy.
- intro x. destruct (in_dec R2.eq_dec x (SECT s1)), (in_dec R2.eq_dec x (SECT s2));
  trivial; rewrite Hs in *; contradiction.
Qed.

Definition is_clean (s : Spect.t) : bool :=
  if inclA_bool _ R2.eq_dec (Spect.support s) (SECT s) then true else false.

Instance is_clean_compat : Proper (Spect.eq ==> Logic.eq) is_clean.
Proof.
intros ? ? Heq. unfold is_clean.
destruct (inclA_bool _ R2.eq_dec (Spect.support x) (SECT x)) eqn:Hx,
         (inclA_bool _ R2.eq_dec (Spect.support y) (SECT y)) eqn:Hy;
  trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff in *.
+ elim Hy. intros e Hin. rewrite <- Heq in Hin.
  apply SECT_compat in Heq. rewrite <- PermutationA_Leibniz in Heq.
  rewrite <- Heq. now apply Hx.
+ elim Hx. intros e Hin. rewrite Heq in Hin.
  apply SECT_compat in Heq. rewrite <- PermutationA_Leibniz in Heq.
  rewrite Heq. now apply Hy.
Qed.

Definition gatherR2_pgm (s : Spect.t) : R2.t :=
  match Spect.support (Smax s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* majority *)
    | _ :: _ :: _ =>
      if is_clean s then target s (* reduce *)
      else if mem R2.eq_dec (0, 0) (SECT s) then (0, 0) else target s (* clean *)
  end.

Instance gatherR2_pgm_compat : Proper (Spect.eq ==> R2.eq) gatherR2_pgm.
Proof.
intros s1 s2 Hs. unfold gatherR2_pgm.
assert (Hsize : length (Spect.support (Smax s1)) = length (Spect.support (Smax s2))).
{ f_equiv. rewrite <- PermutationA_Leibniz. now do 2 f_equiv. }
destruct (Spect.support (Smax s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support (Smax s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ apply Smax_compat, Spect.support_compat in Hs. rewrite Hs1, Hs2 in Hs.
  rewrite PermutationA_Leibniz in Hs. apply Permutation_length_1_inv in Hs. now inversion Hs.
+ rewrite Hs. destruct (is_clean s2).
  - now f_equiv.
  - destruct (mem R2.eq_dec (0, 0) (SECT s1)) eqn:Hin,
             (mem R2.eq_dec (0, 0) (SECT s2)) eqn:Hin';
    rewrite ?mem_true_iff, ?mem_false_iff, ?InA_Leibniz in *;
    try (reflexivity || (rewrite Hs in Hin; contradiction)). now f_equiv.
Qed.

Definition gatherR2 : robogram := {| pgm := gatherR2_pgm |}.

(** **  Decreasing measure ensuring termination  **)

(** Global measure: lexicgraphic order on the index of the type of config + some specific measure:
    ]  Gathered: no need
   0]  Majority tower: # robots not on majority tower
   1]  Non-isosceles triangle and c = SEC ∪ DEST: # robots not on DEST
   2]  Non-isosceles triangle and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   1'] Isosceles triangle not equilateral and c = SEC ∪ DEST: # robots not on DEST
   2'] Isosceles triangle not equilateral and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   3]  Equilateral triangle and c = SEC ∪ DEST: # robots not on DEST
   4]  Equilateral triangle and c <> SEC ∪ DEST: # robots not on SEC ∪ DEST
   5]  General case ($|\SEC| \geq 4$) and c = SEC ∪ DEST: # robots not on DEST
   6]  General case ($|\SEC| \geq 4$) and c <> SECT$: # robots not on SEC ∪ DEST
*)

Close Scope R_scope.

Definition measure_reduce (s : Spect.t) := N.nG - s[target s].
Definition measure_clean (s : Spect.t) := N.nG - SECT_cardinal s.

Definition measure (s : Spect.t) : nat * nat :=
  match Spect.support (Smax s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => (0, measure_reduce s) (* majority *)
    | _ :: _ :: _ =>
      let l := Spect.support s in
      let sec := List.filter (on_circle (SEC l)) l in
      match sec with
        | nil | _ :: nil => (0, 0) (* impossible cases *)
        | pt1 :: pt2 :: pt3 :: nil =>
          match classify_triangle pt1 pt2 pt3 with (* triangle cases *)
            | Equilateral => if is_clean s then (3, measure_reduce s) else (4, measure_clean s)
            | Isosceles vertex => if is_clean s then (1, measure_reduce s) else (2, measure_clean s)
            | Scalene => if is_clean s then (1, measure_reduce s) else (2, measure_clean s)
          end
        | _ => (* general case *) if is_clean s then (5, measure_reduce s) else (6, measure_clean s)
      end
  end.

Instance measure_reduce_compat : Proper (Spect.eq ==> Logic.eq) measure_reduce.
Proof. intros ? ? Heq. unfold measure_reduce. now rewrite Heq. Qed.

Instance measure_clean_compat : Proper (Spect.eq ==> Logic.eq) measure_clean.
Proof. intros ? ? Heq. unfold measure_clean. now rewrite Heq. Qed.

Instance measure_compat : Proper (Spect.eq ==> Logic.eq) measure.
Proof.
intros s1 s2 Hs. unfold measure.
assert (Hsize : length (Spect.support (Smax s1)) = length (Spect.support (Smax s2))).
{ f_equiv. rewrite <- PermutationA_Leibniz. now do 2 f_equiv. }
destruct (Spect.support (Smax s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support (Smax s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ f_equal. now rewrite Hs.
+ clear -Hs.
  assert (Hperm : Permutation (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1))
                              (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))).
  { rewrite <- PermutationA_Leibniz. etransitivity.
    - apply (filter_PermutationA_compat _); refine _. now rewrite Hs.
    - rewrite filter_extensionality_compat; try reflexivity.
      intros x y Hxy. subst. f_equal. f_equiv. rewrite <- PermutationA_Leibniz. now rewrite Hs. }
  destruct (filter (on_circle (SEC (Spect.support s1))) (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
  - apply Permutation_nil in Hperm. now rewrite Hperm.
  - apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
  - apply Permutation_length_2_inv in Hperm.
    destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial;
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) =3%nat) by now rewrite <- Hperm.
    destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
      as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite (classify_triangle_compat Hperm).
    destruct (classify_triangle b1 b2 b3); rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2)) = 4 + length l)%nat
      by now rewrite <- Hperm.
    destruct (filter (on_circle (SEC (Spect.support s2))) (Spect.support s2))
      as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
Qed.

Require Pactole.GatheringinR.Algorithm.

Definition lt_config x y := lexprod lt lt (measure (!! x)) (measure (!! y)).

Lemma wf_lt_conf: well_founded lt_config.
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply wf_lexprod;apply lt_wf.
Qed.

Instance lt_conf_compat: Proper (Pos.eq ==> Pos.eq ==> iff) lt_config.
Proof.
  intros pos1 pos1' heq1 pos2 pos2' heq2.
  unfold lt_config.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Definition map_triangle_type f t :=
  match t with
  | Isosceles p => Isosceles (f p)
  | _ => t
  end.

Definition sim_circle (sim:Sim.t) c :=
  {| center := sim c.(center) ; radius := sim.(Sim.zoom) * (c.(radius)) |}.

Lemma classify_triangle_morph :
  forall (sim : Sim.t) pt1 pt2 pt3, classify_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = map_triangle_type sim (classify_triangle pt1 pt2 pt3).
Proof.
  intros sim pt1 pt2 pt3.
  unfold classify_triangle at 1.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *; try apply Sim.zoom_non_null.
  functional induction (classify_triangle pt1 pt2 pt3);
  repeat rewrite ?e, ?e0, ?e1, ?(sim.(Sim.dist_prop)), ?Rdec_bool_mult_l; try reflexivity;
  try apply Sim.zoom_non_null.
Qed.

Lemma on_circle_morph :
  forall (sim : Sim.t) pt c, on_circle (sim_circle sim c) (sim pt) = on_circle c pt.
Proof.
  intros sim pt c.
  unfold on_circle at 1.
  unfold sim_circle.
  simpl.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *;try apply Sim.zoom_non_null.
  reflexivity.
Qed.

Lemma enclosing_circle_morph :
  forall (sim : Sim.t) c l, enclosing_circle (sim_circle sim c) (List.map sim l) <-> enclosing_circle c l.
Proof.
  intros sim c l.
  unfold enclosing_circle.
  unfold sim_circle.
  simpl.
  setoid_rewrite Forall_forall.
  setoid_rewrite in_map_iff.
  split;intro h.
  - intros x h'.
    specialize (h (sim x)).
    setoid_rewrite (sim.(Sim.dist_prop)) in h.
    apply Rmult_le_reg_l in h;auto.
    + apply Sim.zoom_pos.
    + eauto.
  - intros x H.
    destruct H as [x' [hsim hIn]].
    subst.
    rewrite (sim.(Sim.dist_prop)).
    eapply Rmult_le_compat_l in h;eauto.
    apply Rlt_le, Sim.zoom_pos.
Qed.

(* TODO? *)
Axiom SEC_unicity: forall l c,
    enclosing_circle c l
    -> (radius c <= radius (SEC l))%R
    -> c = SEC l.

(* TODO *)
Axiom SEC_morph : forall (sim:Sim.t) l, SEC (List.map sim l) = sim_circle sim (SEC l).

Lemma barycenter_morph: forall (sim : Sim.t) pt1 pt2 pt3,
  barycenter (sim pt1) (sim pt2) (sim pt3) = sim (barycenter pt1 pt2 pt3).
Proof.
  intros sim pt1 pt2 pt3.
  unfold barycenter.
Admitted.

Lemma opposite_of_max_side_morph : forall (sim : Sim.t) pt1 pt2 pt3,
  opposite_of_max_side (sim pt1) (sim pt2) (sim pt3) = sim (opposite_of_max_side pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold opposite_of_max_side.
repeat rewrite (sim.(Sim.dist_prop)).
assert (Hpos : (0 < Sim.zoom sim)%R) by apply Sim.zoom_pos.
repeat rewrite Rle_bool_mult_l; trivial.
repeat match goal with
  | |- context[Rle_bool ?x ?y] => destruct (Rle_bool x y)
end; reflexivity.
Qed.

Lemma target_triangle_morph:
  forall (sim : Sim.t) pt1 pt2 pt3, target_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = sim (target_triangle pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold target_triangle.
rewrite classify_triangle_morph.
destruct (classify_triangle pt1 pt2 pt3);simpl;auto.
- apply barycenter_morph.
- apply opposite_of_max_side_morph.
Qed.

Lemma target_morph : forall (sim : Sim.t) s, target (Spect.map sim s) = sim (target s).
Proof.
intros sim s. unfold target.
assert (Hperm : Permutation (List.map sim (filter (on_circle (SEC (Spect.support s))) (Spect.support s)))
                  (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (Spect.support (Spect.map sim s)))).
{ assert (Heq : filter (on_circle (SEC (Spect.support s))) (Spect.support s)
              = filter (fun x => on_circle (sim_circle sim (SEC (Spect.support s))) (sim x)) (Spect.support s)).
  { apply filter_extensionality_compat; trivial. repeat intro. subst. now rewrite on_circle_morph. }
  rewrite Heq. rewrite <- filter_map.
  rewrite <- PermutationA_Leibniz. rewrite <- Spect.map_injective_support; trivial.
  - rewrite filter_extensionality_compat; try reflexivity.
    repeat intro. subst. f_equal. symmetry. rewrite <- SEC_morph.
    apply SEC_compat. apply map_sim_support.
  - intros ? ? H. now rewrite H.
  - apply Sim.injective. }
rewrite <- PermutationA_Leibniz in Hperm.
assert (Hlen := PermutationA_length _ Hperm).
destruct ((filter (on_circle (SEC (Spect.support s))) (Spect.support s))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hn,
         (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (Spect.support (Spect.map sim s)))
         as [| pt1' [| pt2' [| pt3' [| ? ?]]]]; simpl in *; try (omega || reflexivity); clear Hlen.
+ admit. (* we need the hypothesis that there are robots *)
+ now rewrite (PermutationA_1 _) in Hperm.
+ rewrite (PermutationA_2 _) in Hperm.
  destruct Hperm as [[H1 H2] | [H1 H2]]; subst; admit. (* sim is a morphism for R2.add and R2.mul *)
+ rewrite PermutationA_Leibniz in Hperm. rewrite <- (target_triangle_compat Hperm). apply target_triangle_morph.
+ change (sim (center (SEC (Spect.support s)))) with (center (sim_circle sim (SEC (Spect.support s)))).
  f_equal. rewrite <- SEC_morph. f_equiv. apply map_sim_support.
Admitted.

Corollary SECT_morph : forall (sim : Sim.t) s, Permutation (SECT (Spect.map sim s)) (map sim (SECT s)).
Proof.
intros sim s. unfold SECT.
rewrite target_morph. simpl. constructor.
transitivity (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (map sim (Spect.support s))).
+ rewrite <- PermutationA_Leibniz. apply (filter_PermutationA_compat _).
  - repeat intro. now subst.
  - rewrite PermutationA_Leibniz. apply map_sim_support.
+ rewrite filter_map.
  cut (map sim (filter (fun x => on_circle (SEC (Spect.support (Spect.map sim s))) (sim x)) (Spect.support s))
       = (map sim (filter (on_circle (SEC (Spect.support s))) (Spect.support s)))).
  - intro Heq. now rewrite Heq.
  - f_equal. apply filter_extensionality_compat; trivial.
    repeat intro. subst. now rewrite map_sim_support, SEC_morph, on_circle_morph.
Qed.

Lemma is_clean_morph : forall (sim : Sim.t) s, is_clean (Spect.map sim s) = is_clean s.
Proof.
intros sim s. unfold is_clean.
destruct (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support (Spect.map sim s)) (SECT (Spect.map sim s))) eqn:Hx,
         (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support s) (SECT s)) eqn:Hy;
trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff, ?inclA_Leibniz in *.
- elim Hy. intros x Hin. apply (in_map sim) in Hin. rewrite <- map_sim_support in Hin.
  apply Hx in Hin. rewrite SECT_morph, in_map_iff in Hin.
  destruct Hin as [x' [Heq ?]]. apply Sim.injective in Heq. now rewrite <- Heq.
- elim Hx. intros x Hin. rewrite SECT_morph. rewrite map_sim_support in Hin.
  rewrite in_map_iff in *. destruct Hin as [x' [? Hin]]. subst. exists x'. repeat split. now apply Hy.
Qed.

Theorem round_simplify : forall da conf,
  Pos.eq (round gatherR2 da conf)
         (fun id => match da.(step) id with
                      | None => conf id
                      | Some f =>
                          let s := !! conf in
                          match Spect.support (Smax s) with
                            | nil => conf id (* only happen with no robots *)
                            | pt :: nil => pt (* majority stack *)
                            | _ => if is_clean s then target s else
                                   if mem R2.eq_dec (conf id) (SECT s) then conf id else target s
                          end
                    end).
Proof.
intros da conf id. hnf. unfold round.
destruct (step da id) as [f |] eqn:Hstep; trivial.
destruct id as [g | b]; try now eapply Fin.case0; exact b.
remember (conf (Good g)) as pt. remember (f pt) as sim.
assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. }
simpl pgm. unfold gatherR2_pgm.
assert (Hperm : Permutation (map sim (Spect.support (Smax (!! conf))))
                            (Spect.support (Smax (!! (Pos.map sim conf)))))
  by (now rewrite <- map_sim_support, <- PermutationA_Leibniz, <- Smax_morph, Spect.from_config_map).
assert (Hlen := Permutation_length Hperm).
destruct (Spect.support (Smax (!! conf))) as [| pt1 [| pt2 l]] eqn:Hmax,
         (Spect.support (Smax (!! (Pos.map sim conf)))) as [| pt1' [| pt2' l']];
simpl in Hlen; discriminate || clear Hlen.
* rewrite Spect.support_nil, Smax_empty in Hmax. elim (spect_non_nil _ Hmax).
* simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'. now apply Sim.compose_inverse_l.
* rewrite <- Spect.from_config_map, is_clean_morph; trivial.
  destruct (is_clean (!! conf)).
  + rewrite <- Spect.from_config_map, target_morph; trivial. now apply Sim.compose_inverse_l.
  + rewrite <- (Sim.center_prop sim). rewrite Heqsim at 3. rewrite (step_center da _ _ Hstep).
    assert (Hperm' : PermutationA eq (SECT (!! (Pos.map sim conf))) (map sim (SECT (!! conf)))).
    { rewrite PermutationA_Leibniz, <- SECT_morph. f_equiv. now rewrite Spect.from_config_map. }
    rewrite Hperm'. rewrite (mem_injective_map _); trivial; try (now apply Sim.injective); [].
    destruct (mem R2.eq_dec pt (SECT (!! conf))).
    - rewrite <- (Sim.center_prop sim), Heqsim, (step_center _ _ _ Hstep). now apply Sim.compose_inverse_l.
    - simpl. rewrite <- sim.(Similarity.Inversion), <- target_morph. f_equiv. now apply Spect.from_config_map.
Qed.

End GatheringinR2.
