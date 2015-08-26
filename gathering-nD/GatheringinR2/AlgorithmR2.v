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
Require Import Omega.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Positions.
Require Pactole.CommonFormalism.
Require Pactole.RigidFormalism.
Require Import Pactole.GatheringinR.SortingR.
Require Import Pactole.MultisetSpectrum.


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

Ltac Rdec_aux H :=
  match type of H with
    | context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot. We
    call a [configuration] a function from robots to position. An
    [execution] is an infinite (coinductive) stream of [configuration]s. A
    [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR2.

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter nG: nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.


(** The spectrum is a multiset of positions *)
Module Spect := MultisetSpectrum.Make(R2)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Common := CommonRealFormalism.Make(R2)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(R2)(N)(Spect)(Common).
Close Scope R_scope.
Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

(** [gathered_at pos pt] means that in configuration [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

Require Import Streams.
(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
Definition gather (pt: R2.t) (e : execution) : Prop :=
  Stream.forever (Stream.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition willGather (pt : R2.t) (e : execution) : Prop := Stream.eventually (gather pt) e.

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
  Sim.center := (0,0) |}.
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


End GatheringinR2.


(** The proofs of soundness and termination uses a decreasing measure
    given below according to 6 different kinds of configuration:
    0) All robots are gathered
    1) There is a mjority tower (ie a tower containing strictly more robots that any ohter tower)
    2) There are three aligned towers
    3) There are two critical points and other non-critical ones + center of circle.
        -> not present on the algorithm
    4) There are three critical points and no other points except on the center of the circle
    5) All robots are on the encosing circle (or its center) (exactly 3 critical), but some towers are non critical
    6) General case: some robots are not on the enclosing circle.


Robogram:

\begin{enumerate}
\item \label{algo:majo} If there is a unique location with highest
  multiplicity, the destination is that location,
\item If there are three aligned towers, then go to the middle one,
\item\label{algo:notsecmaj}Otherwise, if not on \secmaj nor at its
  center nor of highest multiplicity, then the center of \secmaj is
  the destination,
\item\label{algo:allsecmajnoncrit}Otherwise, if all towers are on
  \secmaj or at its center and if at a non-critical location, the
  destination is the center of \secmaj,\marginote{fusion 2 et 3
    possible mais plus compliqué à montrer (non max hors SEC peut
    devenir max)}
\item\label{algo:allsecmajcrit}Otherwise, if all towers are at
  critical locations, go to the center of \secmaj.
\item Otherwise, the destination is the origin (do not
  move).
\end{enumerate}

Global measure: lexicgraphic order on the index of the type of config + some specific measure:
  0) done
  1) 
  2) 
  3) 
  4) 
  5) 
  6) 


*)