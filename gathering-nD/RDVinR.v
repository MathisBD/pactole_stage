Require Import Bool.
Require Import Arith.Div2.
Require Import Omega.
Require Import Rbase Rbasic_fun.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import FMultisetFacts FMultisetMap.
Require Import Preliminary.
Require Import Robots.
Require Import Positions.
Require Import ConvergentFormalismRd.
Require Import SortingR.
Require MultisetSpectrum.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.


Set Implicit Arguments.
Close Scope R_scope.


(** R as a vector space over itself. *)

Module Rdef : MetricSpaceDef with Definition t := R
                             with Definition eq := @Logic.eq R
                             with Definition eq_dec := Rdec
                             with Definition origin := 0%R
                             with Definition dist := fun x y => Rabs (x - y)
                             with Definition add := Rplus
                             with Definition mul := Rmult
                             with Definition opp := Ropp.
  
  Definition t := R.
  Definition origin := 0%R.
  Definition eq := @Logic.eq R.
  Definition dist x y := Rabs (x - y).
  
  Definition add := Rplus.
  Definition mul := Rmult.
  Definition opp := Ropp.
  
  Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Instance opp_compat : Proper (eq ==> eq) opp.
  Proof. unfold eq. repeat intro. now subst. Qed.
  
  Definition eq_equiv := @eq_equivalence R.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := Rdec.
  
  Lemma dist_defined : forall x y : t, dist x y = 0%R <-> eq x y.
  Proof.
  intros x y. unfold eq, dist. split; intro Heq.
  + apply Rminus_diag_uniq. destruct (Rcase_abs (x - y)) as [Hcase | Hcase].
    - apply Rlt_not_eq in Hcase. apply Rabs_no_R0 in Hcase. contradiction.
    - rewrite <- Heq. symmetry. now apply Rabs_pos_eq, Rge_le.
  + rewrite (Rminus_diag_eq _ _ Heq). apply Rabs_R0.
  Qed.

  Lemma dist_sym : forall y x : t, dist x y = dist y x.
  Proof. intros. unfold dist. apply Rabs_minus_sym. Qed.
  
  Lemma triang_ineq : forall x y z : t, (dist x z <= dist x y + dist y z)%R.
  Proof.
  intros. unfold dist. replace (x - z)%R with (x - y + (y - z))%R by lra. apply Rabs_triang.
  Qed.
  
  Lemma plus_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof. unfold eq, add. intros. lra. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof. unfold eq, add, origin. intros. lra. Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof. unfold eq, add, opp, origin. intros. lra. Qed.
  
  Lemma mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Proof. unfold eq, mul. intros. lra. Qed.
  
  Lemma add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  Lemma plus_distr : forall a b u, eq (mul (a + b) u) (add (mul a u) (mul b u)).
  Proof. unfold eq, add, mul. intros. lra. Qed.
  
  (* The multiplicative identity is missing *)
End Rdef.


Module R := MakeMetricSpace(Rdef).

(** Small dedicated decision tactic for reals handling 1<>0 and r=r *)
Ltac Rdec := repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] =>
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
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


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot. We
    call a [configuration] a function from robots to position. An
    [execution] is an infinite (coinductive) stream of [configuration]s. A
    [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR.

(** **  Framework of the impossibility proof: a finite set with at leasts two elements  **)
Section HypRobots.
Variable nG : nat.
Hypothesis size_G : nG >= 2.


Definition g1' : Fin.t nG.
destruct nG eqn:HnG. abstract (omega).
apply (@Fin.F1 n).
Defined.

Definition g2' : Fin.t nG.
destruct nG as [| [| n]] eqn:HnG; try (abstract (omega)).
apply (Fin.FS Fin.F1).
Defined.

End HypRobots.

Require Import Coq.Program.Equality.
Lemma g1'_g2' : forall nG size_nG , @g1' nG size_nG <> @g2' nG size_nG.
Proof.
  dependent destruction nG;intros.
  - exfalso;omega.
  - dependent destruction nG.
    + exfalso;omega.
    + simpl.
      intro abs.
      inversion abs.
Qed.

Parameter nG: nat.
Axiom size_G : nG >= 2.

Corollary half_size_pos : div2 nG > 0.
Proof. apply Exp_prop.div2_not_R0. apply size_G. Qed.


Module N : Size with Definition nG := nG.
  Definition nG := nG.
  Definition nB := 0.
End N.


(** The spectrum is a multiset of positions *)
Module Spec := MultisetSpectrum.Make(R)(N).

Module Export Formalism := ConvergentFormalism(R)(N)(Spec).
Close Scope R_scope.

(** [gathered_at pos pt] means that in position [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather (pt: R) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive WillGather (pt : R) (e : execution) : Prop :=
  | Now : Gather pt e -> WillGather pt e
  | Later : WillGather pt (execution_tail e) -> WillGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these positions as [forbidden]. *)
Definition forbidden (config : Pos.t) :=
  Nat.Even N.nG /\ let m := Spec.from_config(config) in
  exists p1 p2, ~p1 = p2 /\ Spec.multiplicity p1 m = N.nG / 2 /\ Spec.multiplicity p2 m = N.nG / 2.

Instance forbidden_invariant : Proper (Pos.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [pt1 [pt2 [Hneq Hpt]]]]; split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

(** [solGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed. *)
Definition solGathering (r : robogram) (d : demon) :=
  forall pos, ~forbidden pos -> exists pt : R, WillGather pt (execute r d pos).

Definition g1 : Names.G := @g1' nG size_G.

Definition g2 : Names.G := @g2' nG size_G.

Lemma g1_g2 : g1 <> g2.
Proof. apply g1'_g2'. Qed.

Open Scope R_scope.

(* A location is determined by distances to 2 points. *)
Lemma dist_case : forall x y, R.dist x y = x - y \/ R.dist x y = y - x.
Proof.
unfold R.dist, Rdef.dist. intros x y. destruct (Rle_lt_dec 0 (x - y)) as [Hle | Hlt].
- apply Rabs_pos_eq in Hle. lra.
- apply Rabs_left in Hlt. lra.
Qed.

Lemma dist_locate : forall x y k, R.dist x y = k -> x = y + k \/ x = y - k.
Proof. intros x y k ?. subst. assert (Hcase := dist_case x y). lra. Qed.

Lemma GPS : forall x y z1 z2, x <> y -> R.dist z1 x = R.dist z2 x -> R.dist z1 y = R.dist z2 y -> z1 = z2.
Proof.
intros x y z1 z2 Hneq Hx Hy.
assert (Hcase1 := dist_case z1 x). assert (Hcase2 := dist_case z2 x).
assert (Hcase3 := dist_case z1 y). assert (Hcase4 := dist_case z2 y).
lra.
Qed.
Arguments GPS x y z1 z2 _ _ _ : clear implicits.

(* Not true when the metric space has dimension 0, we need at least 2 different points. *)
Lemma sim_ratio_pos : forall sim, (0 <= sim.(ratio))%R.
Proof.
intros [f k c Hc Hk]. simpl. clear c Hc. specialize (Hk R1 R0).
assert (H1 : R.dist 1 0 = 1). { unfold R.dist, Rdef.dist. rewrite Rminus_0_r. apply Rabs_pos_eq. lra. }
rewrite H1, Rmult_1_r in Hk. subst. apply R.dist_pos.
Qed.

(* A similarity in R is described by its ratio and its center. *)
Theorem similarity_in_R : forall sim,
  (forall x, sim.(f) x = sim.(ratio) * (x - sim.(center)) + sim.(center)) \/
  (forall x, sim.(f) x = - sim.(ratio) * (x - sim.(center)) + sim.(center)).
Proof.
intro sim. assert (Hkpos : 0 <= sim.(ratio)) by apply sim_ratio_pos.
destruct sim as [f k c Hc Hk]. simpl in *. destruct (Rdec k 0) as [Hk0 | Hk0].
* (* if the ratio is 0, the similarity is a constant function. *)
  left. intro x. subst k. rewrite Rmult_0_l, Rplus_0_l.
  rewrite <- R.dist_defined. rewrite <- Hc, Hk. ring.
* assert (Hc1 : f (c + 1) = c + k \/ f (c + 1) = c - k).
  { specialize (Hk (c + 1) c). rewrite Hc in Hk.
    assert (H1 : R.dist (c + 1) c = 1). { replace 1 with (c+1 - c) at 2 by ring. apply Rabs_pos_eq. lra. }
    rewrite H1 in Hk. destruct (dist_case (f (c + 1)) c) as [Heq | Heq]; rewrite Heq in Hk; lra. }
  destruct Hc1 as [Hc1 | Hc1].
  + left. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (k * (x - c) + c - c) with (k * (x - c)) by ring.
      now rewrite Rabs_mult, (Rabs_pos_eq k Hkpos).
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (k * (x - c) + c - (c + k)) with (k * (x - (c + 1))) by ring.
      now rewrite Rabs_mult, (Rabs_pos_eq k Hkpos).
  + right. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) + c - c) with (- k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) + c - (c - k)) with (- k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
Qed.

(* Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 99, format "'⟦' k ','  t '⟧'"). *)

Corollary spec_nil : forall conf, ~Spec.eq (Spec.from_config conf) Spec.empty.
Proof.
intros conf Heq.
SearchAbout Spec.empty.
Admitted.


Definition Stack_at x pos :=
  exists n, Spec.multiplicity x (Spec.from_config pos) = n
  /\ forall y, x <> y -> (Spec.multiplicity y (Spec.from_config pos) < n)%nat.

Instance Stack_at_compat : Proper (Logic.eq ==> Pos.eq ==> iff) Stack_at.
Proof. intros ? ? ? ? ? Hpos. subst. unfold Stack_at. now setoid_rewrite Hpos. Qed.


Ltac Rdec_aux H :=
  match type of H with
    | context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.


Instance map_ExtEq_compat A B : Proper ((eq ==> eq) ==> @Permutation A ==> @Permutation B) (@map A B).
Proof.
intros f g Hfg l. induction l; intros l' Hl.
- apply Permutation_nil in Hl. subst l'. reflexivity.
- assert (Hin : InA eq a l'). { rewrite <- PermutationA_Leibniz in Hl. rewrite <- Hl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l'' Hl']. rewrite PermutationA_Leibniz in Hl'.
  rewrite Hl'. simpl. rewrite (Hfg _ _ (reflexivity a)). constructor.
  apply IHl. apply Permutation_cons_inv with a. now transitivity l'.
Qed.


Open Scope R_scope.

Definition is_extremal r (s : Spec.t) :=
  if Rdec r (List.hd r (sort (Spec.support s))) then true else
  if Rdec r (List.last (sort (Spec.support s)) r) then true else false.

(*
Theorem is_extremal_correct : forall r (s : spectrum),
  List.In r s -> (is_extremal r s = true <-> extremal r s).
Proof.
unfold is_extremal,extremal. intros r s Hin.
repeat Rdec_full; split; intro H; try (reflexivity || discriminate H);
try solve [reflexivity | discriminate H | right; now intros [] | left; now intros []].
+ clear H. rewrite Heq. exists (List.last (sort s) r). right.
  rewrite range_split. split;
  rewrite List.Forall_forall; apply sort_min || apply sort_max.
+ clear H. exists (List.hd r (sort s)). left. rewrite Heq.
  rewrite range_split. split;
  rewrite List.Forall_forall; apply sort_min || apply sort_max.
+ exfalso. destruct H as [b [Hb | Hb]].
  - elim (Rlt_irrefl r). apply Rlt_le_trans with (List.last (sort s) r).
      revert Hneq0. generalize (sort_max s r r Hin). apply Rle_neq_lt.
      apply range_split in Hb. destruct Hb as [_ Hb]. rewrite List.Forall_forall in Hb.
      apply Hb. rewrite (Permuted_sort s) at 2. apply last_In.
      rewrite (Permuted_sort s) in Hin. destruct (sort s).
      inversion Hin. discriminate.
  - elim (Rlt_irrefl r). apply Rle_lt_trans with (List.hd r (sort s)).
      apply range_split in Hb. destruct Hb as [Hb _]. rewrite List.Forall_forall in Hb.
      apply Hb. rewrite (Permuted_sort s) at 2.
      rewrite (Permuted_sort s) in Hin. destruct (sort s).
      inversion Hin. now left.
      assert (Hneq' : List.hd r (sort s) <> r). { intro. apply Hneq. now symmetry. }
      revert Hneq'. generalize (sort_min s r r Hin). apply Rle_neq_lt.
Qed.
*)

Instance is_extremal_compat : Proper (eq ==> Spec.eq ==> eq) is_extremal.
Proof.
intros x y ? s s' Hs. subst y. unfold is_extremal.
destruct (Rdec x (hd x (sort (Spec.support s)))), (Rdec x (hd x (sort (Spec.support s'))));
try rewrite Hs in *; contradiction || trivial.
destruct (Rdec x (last (sort (Spec.support s)) x)), (Rdec x (last (sort (Spec.support s')) x));
try rewrite Hs in *; contradiction || reflexivity.
Qed.

Coercion is_true : bool >-> Sortclass.

Definition monotonic {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  Proper (RA ==> RB) f \/ Proper (RA --> RB) f.
Locate Rle.
Lemma similarity_increasing : forall k t, k >= 0 -> Proper (Rleb ==> Rleb) (fun x => k * (x - t)).
Proof. repeat intro. hnf in *. rewrite Rleb_spec in *. apply Rmult_le_compat_l; lra. Qed.

Lemma similarity_decreasing : forall k t, k <= 0 -> Proper (Rleb --> Rleb) (fun x => k * (x - t)).
Proof.
repeat intro. hnf in *. unfold flip in *. rewrite Rleb_spec in *. apply Ropp_le_cancel.
replace (- (k * (y - t))) with ((- k) * (y - t)) by ring.
replace (- (k * (x - t))) with ((- k) * (x - t)) by ring.
apply Rmult_le_compat_l; lra.
Qed.

Corollary similarity_monotonic : forall k t, monotonic Rleb Rleb (fun x => k * (x - t)).
Proof.
intros k t. destruct (Rle_lt_dec 0 k) as [Hlt | Hle].
+ left. apply similarity_increasing. lra.
+ right. apply similarity_decreasing. lra.
Qed.

Lemma similarity_injective : forall k t, k <> 0 -> injective eq eq (fun x => k * (x - t)).
Proof. intros k t Hk x y. now rewrite local_invert. Qed.


Lemma is_extremal_map_monotonic_invariant : forall f, monotonic Rleb Rleb f -> injective eq eq f ->
  forall x l, is_extremal (f x) (Spec.map f l) = is_extremal x l.
Proof.
intros f Hfmon Hfinj x l. unfold is_extremal.
assert (Hf : Proper (R.eq ==> R.eq) f). { unfold R.eq, Rdef.eq. repeat intro. now subst. }
destruct Hfmon as [Hfinc | Hfdec].
+ repeat Rdec_full; trivial;rewrite Spec.map_support, (sort_map_increasing Hfinc) in *; trivial.
  - rewrite map_hd in Heq. apply Hfinj in Heq. contradiction.
  - rewrite map_last in Heq. apply Hfinj in Heq. contradiction.
  - elim Hneq. rewrite map_hd. now f_equal.
  - elim Hneq0. rewrite map_last. now f_equal.
+ repeat Rdec_full; trivial;rewrite Spec.map_support, (sort_map_decreasing Hfdec) in *; trivial.
  - rewrite hd_rev_last, map_last in Heq. apply Hfinj in Heq. contradiction.
  - rewrite last_rev_hd, map_hd in Heq. apply Hfinj in Heq. contradiction.
  - elim Hneq0. rewrite last_rev_hd, map_hd. now f_equal.
  - elim Hneq. rewrite hd_rev_last, map_last. now f_equal.
Qed.

Corollary is_extremal_similarity_invariant : forall k t pos r, k <> 0 ->
  is_extremal (k * (r - t)) (nominal_spectrum (⟦k, t⟧ pos)) = is_extremal r (nominal_spectrum pos).
Proof.
intros k t pos r Hk. rewrite nominal_spectrum_similarity.
now rewrite (is_extremal_map_monotonic_invariant (similarity_monotonic k t) (similarity_injective Hk)).
Qed.

Definition extreme_center (s : spectrum) :=
  (List.hd 0 (sort s) + List.last (sort s) 0) / 2.
(* When there is no robot (s is empty), the center is 0. *)

Instance extreme_center_perm_invariant : Proper (@Permutation R ==> eq) extreme_center.
Proof. intros s s' Hs. unfold extreme_center. now rewrite Hs. Qed.

Lemma extreme_center_map_similarity_invariant : forall k t, k <> 0 ->
  forall l, l <> nil -> extreme_center (map (fun x => k * (x - t)) l) = k * (extreme_center l - t).
Proof.
intros k t Hk l Hl. destruct (similarity_monotonic k t) as [Hinc | Hdec].
+ unfold extreme_center. rewrite (sort_map_increasing Hinc). generalize 0.
  assert (Hperm := Permuted_sort l). destruct (sort l) as [| x l']; intro r.
    symmetry in Hperm. apply Permutation_nil in Hperm. contradiction.
    clear l Hl Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    revert r. induction l; intros r Hl.
      now elim Hl.
      simpl. destruct l.
        simpl. field.
        rewrite <- IHl. reflexivity. discriminate. discriminate.
+ unfold extreme_center. rewrite (sort_map_decreasing Hdec).
  rewrite last_rev_hd, hd_rev_last. generalize 0.
  assert (Hperm := Permuted_sort l). destruct (sort l) as [| x l']; intro r.
    symmetry in Hperm. apply Permutation_nil in Hperm. contradiction.
    clear l Hl Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    revert r. induction l; intros r Hl.
      now elim Hl.
      simpl. destruct l.
        simpl. field.
        rewrite <- IHl. reflexivity. discriminate. discriminate.
Qed.

Lemma extreme_center_similarity_invariant : forall k t pos, k <> 0 ->
  extreme_center (nominal_spectrum (⟦k, t⟧ pos)) = k * (extreme_center (nominal_spectrum pos) - t).
Proof.
intros k t pos Hk. rewrite nominal_spectrum_similarity, extreme_center_map_similarity_invariant; trivial.
assert (Hin : In (locate  pos (Good _ g1)) (nominal_spectrum pos)) by apply In_spectrum.
intro Habs. rewrite Habs in Hin. inversion Hin.
Qed.

(** The robogram works as follows:
    1) if there is a majority stack, everyone goes there;
    2) if there are three stacks, everyone goes on the middle one;
    3) otherwise, robots located at non extremal locations go to the middle of the extremal locations.
    The last case will necessarily end into one of the first two, ensuring termination.
**)
Definition robogram (s : spectrum) : location :=
  match majority_stack s with
    | NoResult => 0 (* there is no robot anyway in this case *)
    | Valid p n => p
    | Invalid n => if beq_nat (length (M.support (multiset s))) 3
                   then List.nth 1 (sort (M.support (multiset s))) 0 else
                   if is_extremal 0 s then 0 else extreme_center s end.

Print Assumptions robogram.

(** The robogram is invariant by permutation of spectra. *)
Instance robogram_invariant : Proper (@Permutation R ==> eq) robogram.
Proof.
unfold robogram. intros s s' Hperm. rewrite Hperm.
destruct (majority_stack s'); trivial. now repeat rewrite Hperm.
Qed.
Print Assumptions robogram_invariant.


Lemma nominal_spectrum_alls : forall pt,
  nominal_spectrum (@lift_gp nG (fun _ => pt)) = alls pt nG.
Proof.
intro. unfold nominal_spectrum. simpl. rewrite app_nil_r.
induction nG. reflexivity. simpl. now rewrite <- IHn.
Qed.

Lemma nominal_spectrum_alls_two : forall pt1 pt2 (f : G nG -> bool),
  Permutation (nominal_spectrum (@lift_gp nG (fun x => if f x then pt1 else pt2)))
              (alls pt1 (length (filter f (Gnames nG))) ++ alls pt2 (nG - length (filter f (Gnames nG)))).
Proof.
intros pt1 pt2 f. destruct (Rdec pt1 pt2) as [Heq | Hneq].
+ assert (length (filter f (Gnames nG)) <= nG)%nat.
  { unfold Gnames. rewrite filter_length, fin_map_length. omega. } subst. rewrite alls_app.
  replace ((length (filter f (Gnames nG)) + (nG - length (filter f (Gnames nG)))))%nat with nG by omega.
  assert (Hpos : ExtEq (fun x : G nG => if f x then pt2 else pt2) (fun _ => pt2)). { intro g. now destruct (f g). }
  rewrite Hpos. rewrite nominal_spectrum_alls. reflexivity.
+ unfold lift_gp. rewrite (nominal_spectrum_combineG f (fun _ => pt1) (fun _ => pt2) (Zero_fun R)).
  rewrite app_nil_r, partition_filter. apply Permutation_app; rewrite map_cst_alls.
  - reflexivity.
  - assert (length (filter (fun x => negb (f x)) (Gnames nG)) <= nG)%nat.
    { unfold Gnames. rewrite filter_length, fin_map_length. omega. }
    assert (length (Gnames nG) = nG). { unfold Gnames. apply fin_map_length. } 
    replace (length (filter (fun x : G nG => negb (f x)) (Gnames nG)))
      with (nG - (length (Gnames nG) - length (filter (fun x : G nG => negb (f x)) (Gnames nG))))%nat by omega.
    rewrite <- filter_length. reflexivity.
Qed.

Lemma forbidden_similarity_invariant : forall pos k t, forbidden ((⟦k, t⟧) pos) -> forbidden pos.
Proof.
intros [gp bp] k t [p1 [p2 [Hneq Hperm]]]. destruct (Rdec k 0).
+ subst. assert (Heq : PosEq (lift_gp (fun _ => 0)) (⟦0, t⟧ {| gp := gp; bp := bp |})).
  { split; simpl. intro. now rewrite Rmult_0_l. intro. now apply Fin.case0. }
  rewrite <- Heq in Hperm. clear Heq. rewrite nominal_spectrum_alls in Hperm.
  symmetry in Hperm.
  assert (p1 = 0).
  { apply Permutation_alls in Hperm. destruct nG eqn:HG.
      cut (0 >= 2)%nat. omega. rewrite <- HG at 1. now apply size_G.
      destruct n as [| n]; simpl in Hperm.
        discriminate Hperm.
        now inversion Hperm. }
  assert (p2 = 0).
  { rewrite Permutation_app_comm in Hperm. apply Permutation_alls in Hperm. destruct nG eqn:HG.
      cut (0 >= 2)%nat. omega. rewrite <- HG at 1. now apply size_G.
      destruct n as [| n]; simpl in Hperm.
        discriminate Hperm.
        now inversion Hperm. }
  subst p2. contradiction.
+ exists (p1 / k + t). exists (p2 / k + t). split.
  clear -Hneq n. intro Habs. apply Hneq. apply Rdiv_reg with k. assumption.
  apply Rplus_eq_reg_l with t. now setoid_rewrite Rplus_comm.
  clear Hneq. rewrite <- (@similarity_inverse _ _ k t); trivial. unfold similarity at 1.
  replace (p1 / k + t) with (/k * (p1 - - k * t)) by now field.
  change (/k * (p1 - - k * t)) with ((fun x => /k * (x - - k * t)) p1). rewrite <- map_alls.
  replace (p2 / k + t) with (/k * (p2 - - k * t)) by now field.
  change (/k * (p2 - - k * t)) with ((fun x => /k * (x - - k * t)) p2). rewrite <- map_alls.
  rewrite nominal_spectrum_map. rewrite <- map_app. now apply Permutation_map.
Qed.

Corollary forbidden_similarity_iff : forall k t pos, k <> 0 -> (forbidden (⟦k, t⟧ pos) <-> forbidden pos).
Proof.
intros k t pos Hk. split.
+ apply forbidden_similarity_invariant.
+ rewrite <- (similarity_inverse t pos Hk) at 1. apply forbidden_similarity_invariant.
Qed.

Definition equiv_by (f : R -> R) r r' :=
  match r, r' with
    | NoResult, NoResult => True
    | Valid y m, Valid x n => y = f x /\ m = n
    | Invalid m, Invalid n => m = n
    | _, _ => False
  end.

Lemma majority_stack_inj_compat_aux : forall f l x n r r',
  injective eq eq f -> equiv_by f r r' ->
  (List.fold_left (fun acc xn => f_majority (fst xn) (snd xn) acc)
                  (map (fun xn => (f (fst xn), snd xn)) l) r = Valid (f x) n
  <-> List.fold_left (fun acc xn => f_majority (fst xn) (snd xn) acc) l r' = Valid x n).
Proof.
intros f l x n r r' Hf. revert r r'. induction l; intros r r' Hr; simpl.
+ split; intro; (subst r; destruct r') || (subst r'; destruct r); simpl in Hr; try now elim Hr.
    destruct Hr as [Hr1 Hr2]. apply Hf in Hr1. now subst.
    destruct Hr. now subst.
+ apply IHl. destruct a as [y m], r, r'; simpl; simpl in Hr; try now elim Hr.
    destruct Hr. subst. now destruct (nat_compare m n1).
    subst. now destruct (nat_compare m n1).
Qed.

Instance PermutationA_compat A eqA (HeqA : @Equivalence A eqA) :
  Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (PermutationA eqA).
Proof. intros l1 l2 Hl12 l3 l4 Hl34. now rewrite Hl12, Hl34. Qed.

Lemma majority_stack_inj_map_Valid_compat : forall f l x n, injective eq eq f ->
  (majority_stack (map f l) = Valid (f x) n <-> majority_stack l = Valid x n).
Proof.
intros f l x n Hf. do 2 rewrite majority_stack_Valid_spec. split; intros [Hn Hle]; split.
+ clear Hle. revert n Hn. induction l; simpl; intros n Hn.
    now rewrite multiset_nil, M.empty_spec in *.
    destruct (Rdec a x) as [| Hneq].
      subst a. rewrite multiset_cons, M.add_spec in *. destruct n. omega.
      rewrite plus_comm in *; simpl in *. f_equal. apply eq_add_S in Hn. now apply IHl.
      assert (f a <> f x) by auto.
      rewrite multiset_cons, M.add_spec' in *; trivial. now apply IHl.
+ clear Hn. intros y Hxy. assert (Hn : f x <> f y) by auto. apply Hle in Hn. revert Hn. clear Hle Hxy.
  revert n y. induction l; simpl; intros n y Hin.
    now rewrite multiset_nil, M.empty_spec in *.
    rewrite multiset_cons in *. destruct (Rdec a y).
      subst a. rewrite M.add_spec in *. destruct n. omega.
      rewrite plus_comm in *; simpl in *. apply lt_n_S. apply lt_S_n in Hin. now apply IHl.
      assert (f a <> f y) by auto. rewrite M.add_spec' in *; trivial. now apply IHl.
+ clear Hle. revert n Hn. induction l; simpl; intros n Hn.
    now rewrite multiset_nil, M.empty_spec in *.
    destruct (Rdec a x) as [| Hneq].
      subst a. rewrite multiset_cons, M.add_spec in *. destruct n. omega.
      rewrite plus_comm in *; simpl in *. f_equal. apply eq_add_S in Hn. now apply IHl.
      assert (f a <> f x) by auto.
      rewrite multiset_cons, M.add_spec' in *; trivial. now apply IHl.
+ clear Hn. intros y Hxy. destruct (in_dec Rdec y (map f l)) as [Hin | Hin].
  - rewrite in_map_iff in Hin. destruct Hin as [z [Hyz Hin]]. subst y.
    assert (Hxz : x <> z). { intro. subst z. now apply Hxy. }
    apply Hle in Hxz. clear Hle Hxy Hin. revert n z Hxz. induction l; intros n z Hin.
      now rewrite multiset_nil, M.empty_spec in *.
      simpl. rewrite multiset_cons in *. destruct (Rdec a z).
        subst a. rewrite M.add_spec in *. destruct n. omega.
        rewrite plus_comm in *; simpl in *. apply lt_n_S. apply lt_S_n in Hin. now apply IHl.
        assert (f a <> f z) by auto. rewrite M.add_spec' in *; trivial. now apply IHl.
  - destruct n.
      specialize (Hle _ (succ_neq x)). omega.
      rewrite <- multiset_In in Hin. omega.
Qed.

Lemma majority_stack_Valid_similarity : forall k t pos x n, k <> 0 ->
  (majority_stack (nominal_spectrum ((⟦k, t⟧) pos)) = Valid (k * (x - t)) n
  <-> majority_stack (nominal_spectrum pos) = Valid x n).
Proof.
intros k t pos x n Hk. rewrite nominal_spectrum_similarity.
assert (Hf := fun x y => proj1 (@local_invert k t x y Hk)).
now rewrite (majority_stack_inj_map_Valid_compat _ _ _ Hf).
Qed.

Lemma majority_stack_Invalid_similarity : forall k t pos n, k <> 0 ->
  (majority_stack (nominal_spectrum ((⟦k, t⟧) pos)) = Invalid n
  <-> majority_stack (nominal_spectrum pos) = Invalid n).
Proof.
intros k t pos n Hk. rewrite nominal_spectrum_similarity. generalize (nominal_spectrum pos). clear pos.
intro s. do 2 rewrite majority_stack_Invalid_spec. split; intros [Hn [x [y [Hx [Hy [Hxy Hle]]]]]].
* split. assumption. exists (/k * x + t). exists (/k * y + t). repeat split.
  + clear y Hxy Hy Hle. revert n Hn Hx. induction s; simpl; intros n Hn Hx.
      now rewrite multiset_nil, M.empty_spec in *.
      rewrite multiset_cons in *. destruct (Rdec (k * (a - t)) x) as [Heq | Hneq].
      - subst x. assert (/k * (k * (a - t)) + t = a) by now field. rewrite H in *.
        rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        f_equal. apply eq_add_S in Hx. destruct n.
          assert (Hin : ~In (k * (a - t)) (map (fun x : R => k * (x - t)) s)). { rewrite <- multiset_In. omega. }
          rewrite in_map_iff in Hin. destruct (in_dec Rdec a s) as [| Hnin].
            elim Hin. exists a. now split.
            rewrite <- multiset_In in Hnin. omega.
          apply IHs. omega. assumption.
      - assert (a <> /k * x + t). { intro. subst a. apply Hneq. clear -Hk. unfold M.elt in x. now field. }
        rewrite M.add_spec' in *; trivial. now apply IHs.
  + clear x Hxy Hx Hle. revert n Hn Hy. induction s; simpl; intros n Hn Hy.
      now rewrite multiset_nil, M.empty_spec in *.
      rewrite multiset_cons in *. destruct (Rdec (k * (a - t)) y) as [Heq | Hneq].
      - subst y. assert (/k * (k * (a - t)) + t = a) by now field. rewrite H in *.
        rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        f_equal. apply eq_add_S in Hy. destruct n.
          assert (Hin : ~In (k * (a - t)) (map (fun x : R => k * (x - t)) s)). { rewrite <- multiset_In. omega. }
          rewrite in_map_iff in Hin. destruct (in_dec Rdec a s) as [| Hnin].
            elim Hin. exists a. now split.
            rewrite <- multiset_In in Hnin. omega.
          apply IHs. omega. assumption.
      - assert (a <> /k * y + t). { intro. subst a. apply Hneq. clear -Hk. unfold M.elt in y. now field. }
        rewrite M.add_spec' in *; trivial. now apply IHs.
  + rewrite <- (local_invert t _ _ Hk). intro Heq. field_simplify in Heq; auto. apply Hxy.
    assert (x / 1 = x) by field. rewrite <- H, Heq. now assert (y / 1 = y) by field.
  + clear x y Hx Hy Hxy. intro z. specialize (Hle (k * (z - t))).
    revert n Hn Hle. induction s; simpl; intros n Hn Hle.
      rewrite multiset_nil, M.empty_spec. omega.
      rewrite multiset_cons in *. destruct (Rdec a z).
      - subst z. rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        apply le_n_S. apply le_S_n in Hle. destruct n.
          assert (Hin : ~In (k * (a - t)) (map (fun x : R => k * (x - t)) s)). { rewrite <- multiset_In. omega. }
          rewrite in_map_iff in Hin. destruct (in_dec Rdec a s) as [| Hnin].
            elim Hin. exists a. now split.
            rewrite <- multiset_In in Hnin. omega.
          apply IHs. omega. assumption.
      - assert (k * (a - t) <> k * (z - t)) by now rewrite local_invert.
        rewrite M.add_spec' in *; trivial. now apply IHs.
* split. assumption. exists (k * (x - t)). exists (k * (y - t)). repeat split.
  + clear y Hxy Hy Hle. revert n Hn Hx. induction s; simpl; intros n Hn Hx.
      now rewrite multiset_nil, M.empty_spec in *.
      rewrite multiset_cons in *. destruct (Rdec a x) as [Heq | Hneq].
      - subst x. rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        f_equal. apply eq_add_S in Hx. destruct n.
          assert (Hnin : ~In a s). { rewrite <- multiset_In. omega. }
          assert (Hin : ~In (k * (a -t)) (map (fun x : R => k * (x - t)) s)).
          { rewrite in_map_iff. intros [x [Heq Hin]]. apply Hnin.
            rewrite local_invert in Heq; trivial. now subst a. }
          rewrite <- multiset_In in Hin. omega.
          apply IHs. omega. assumption.
      - assert (k * (a - t) <> k * (x - t)) by now rewrite local_invert.
        rewrite M.add_spec' in *; trivial. now apply IHs.
  + clear x Hxy Hx Hle. revert n Hn Hy. induction s; simpl; intros n Hn Hy.
      now rewrite multiset_nil, M.empty_spec in *.
      rewrite multiset_cons in *. destruct (Rdec a y) as [Heq | Hneq].
      - subst y. rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        f_equal. apply eq_add_S in Hy. destruct n.
          assert (Hnin : ~In a s). { rewrite <- multiset_In. omega. }
          assert (Hin : ~In (k * (a -t)) (map (fun x : R => k * (x - t)) s)).
          { rewrite in_map_iff. intros [x [Heq Hin]]. apply Hnin.
            rewrite local_invert in Heq; trivial. now subst a. }
          rewrite <- multiset_In in Hin. omega.
          apply IHs. omega. assumption.
      - assert (k * (a - t) <> k * (y - t)) by now rewrite local_invert.
        rewrite M.add_spec' in *; trivial. now apply IHs.
  + now rewrite (local_invert t _ _ Hk).
  + clear x y Hx Hy Hxy. intro z. specialize (Hle (/k * z + t)).
    revert n Hn Hle. induction s; simpl; intros n Hn Hle.
      rewrite multiset_nil, M.empty_spec. omega.
      rewrite multiset_cons in *. destruct (Rdec (k * (a - t)) z) as [| Hneq].
      - subst z. assert (/ k * (k * (a - t)) + t = a) by now field. rewrite H in *.
        rewrite M.add_spec in *. destruct n. omega. rewrite plus_comm in *. simpl in *.
        apply le_n_S. apply le_S_n in Hle. destruct n.
          assert (Hnin : ~In a s). { rewrite <- multiset_In. omega. }
          assert (Hin : ~In (k * (a -t)) (map (fun x : R => k * (x - t)) s)).
          { rewrite in_map_iff. intros [x [Heq Hin]]. apply Hnin.
            rewrite local_invert in Heq; trivial. now subst a. }
          rewrite <- multiset_In in Hin. omega.
          apply IHs. omega. assumption.
      - assert (a <> /k * z + t).
        { intro Habs. rewrite <- (local_invert t _ _ Hk) in Habs. apply Hneq. rewrite Habs. now field. }
        rewrite M.add_spec' in *; trivial. now apply IHs.
Qed.

Theorem robogram_homothecy_invariant : forall k t pos, k <> 0 ->
  robogram (nominal_spectrum (⟦k, t⟧ pos)) = k * (robogram (nominal_spectrum (⟦1, t⟧ pos))).
Proof.
intros k t pos Hk. unfold robogram.
destruct (majority_stack (nominal_spectrum  (⟦k, t⟧ pos))) eqn:Hmaj.
* rewrite majority_stack_NoResult_spec in Hmaj. elim (nominal_spectrum_nil _ Hmaj).
* assert (Hl : l = k * ((/k * l + t) - t)) by now field.
  rewrite Hl, majority_stack_Valid_similarity in Hmaj; trivial. clear Hl.
  destruct (majority_stack (nominal_spectrum  (⟦1, t⟧ pos))) eqn:Hmaj1.
  - rewrite majority_stack_NoResult_spec in Hmaj1. elim (nominal_spectrum_nil _ Hmaj1).
  - replace l0 with (1 * (l0 + t - t)) in Hmaj1 by ring. rewrite majority_stack_Valid_similarity in Hmaj1.
    rewrite Hmaj1 in Hmaj. inversion Hmaj. subst n0. clear Hmaj1 Hmaj.
    setoid_rewrite Rplus_comm in H0. apply Rplus_eq_reg_l in H0. subst l0. now field. apply R1_neq_R0.
  - rewrite majority_stack_Invalid_similarity in Hmaj1; try exact R1_neq_R0.
    rewrite Hmaj1 in Hmaj. discriminate Hmaj.
* rewrite majority_stack_Invalid_similarity in Hmaj; trivial.
  rewrite <- (@majority_stack_Invalid_similarity 1) in Hmaj; try exact R1_neq_R0. rewrite Hmaj.
  repeat rewrite nominal_spectrum_similarity.
  repeat rewrite multiset_map; try apply similarity_injective; try (apply R1_neq_R0 || assumption).
  assert (Hlen : length (M.support (M.map (fun x : R => k * (x - t)) (multiset (nominal_spectrum pos))))
               = length (M.support (M.map (fun x : R => 1 * (x - t)) (multiset (nominal_spectrum pos))))).
  { repeat rewrite M.map_support, map_length;
    reflexivity || (now repeat intro; subst) || now apply similarity_injective; try apply R1_neq_R0. }
  setoid_rewrite Hlen at 1.
  destruct (beq_nat (length (M.support (M.map (fun x : R => 1 * (x - t)) (multiset (nominal_spectrum pos))))) 3)
  eqn:H3.
  assert (div2 3 = 1%nat) by reflexivity.
  + assert (Proper (eq ==> eq) (fun x : R => 1 * (x - t))) by now repeat intro; subst.
    assert (Proper (eq ==> eq) (fun x : R => k * (x - t))) by now repeat intro; subst.
    assert (injective eq eq (fun x : R => 1 * (x - t))) by (apply similarity_injective; apply R1_neq_R0).
    assert (injective eq eq (fun x : R => k * (x - t))) by now apply similarity_injective.
    repeat rewrite M.map_support; trivial.
    rewrite (@sort_map_increasing (fun x => 1 * (x - t))); try now apply similarity_increasing; lra.
    replace 0 with (1 * (t - t)) by ring. rewrite (map_nth (fun x => 1 * (x - t))). ring_simplify.
    symmetry in H3. apply beq_nat_eq in H3. rewrite <- Hlen in H3. rewrite <- H, <- H3.
    rewrite M.map_support; trivial. rewrite (Permutation_length (Permuted_sort _)).
    destruct (Rlt_le_dec k 0).
    - rewrite (@sort_map_decreasing (fun x => k * (x - t))); try now apply similarity_decreasing; lra.
      rewrite rev_length, odd_middle.
        rewrite map_length. replace (1 * (t - t)) with (k * (t - t)) by ring.
        rewrite (map_nth (fun x => k * (x - t))). now rewrite Rmult_minus_distr_l.
        rewrite map_length, <- (Permutation_length (Permuted_sort _)).
        rewrite M.map_support, map_length in H3; trivial. unfold M.elt in H3. rewrite H3. now exists 1%nat.
    - rewrite (@sort_map_increasing (fun x => k * (x - t))); try now apply similarity_increasing; lra.
      rewrite map_length. replace (1 * (t - t)) with (k * (t - t)) by ring.
      rewrite (map_nth (fun x => k * (x - t))). now rewrite Rmult_minus_distr_l.
  + do 2 rewrite <- nominal_spectrum_similarity.
  assert (H0 : forall k, k * (t - t) = 0) by (intro; ring). rewrite <- (H0 k) at 1. rewrite <- (H0 1) at 2.
  repeat rewrite is_extremal_similarity_invariant; exact R1_neq_R0 || trivial.
  destruct (is_extremal t (nominal_spectrum pos)). ring.
  repeat rewrite extreme_center_similarity_invariant; exact R1_neq_R0 || trivial. ring.
Qed.
Print Assumptions robogram_homothecy_invariant.

(** **  General simplification lemmas for [round robogram da _] and [nominal_spectrum (round robogram da _)] **)

Lemma round_simplify : forall (da : demonic_action nG 0) pos,
  ExtEq (round robogram da (gp pos))
        (fun g => if Rdec (frame da g) 0 then gp pos g else
                  match majority_stack (nominal_spectrum pos) with
                    | NoResult => 0
                    | Valid pt n => pt
                    | Invalid n => if beq_nat (length (M.support (multiset (nominal_spectrum pos)))) 3
                                   then List.nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0
                                   else if is_extremal (gp pos g) (nominal_spectrum pos) then gp pos g
                                        else extreme_center (nominal_spectrum pos)
                  end).
Proof.
intros da pos g. unfold round. destruct (Rdec (frame da g) 0) as [| Hframe]. reflexivity.
rewrite (spectrum_ok da). rewrite robogram_homothecy_invariant; trivial. field_simplify; trivial. clear Hframe.
unfold robogram.
rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
destruct (majority_stack (nominal_spectrum pos)) eqn:Hmaj.
+ rewrite majority_stack_NoResult_spec in Hmaj. elim (nominal_spectrum_nil _ Hmaj).
+ rewrite <- majority_stack_Valid_similarity in Hmaj; try exact R1_neq_R0. rewrite Hmaj. field.
+ rewrite <- majority_stack_Invalid_similarity in Hmaj; try exact R1_neq_R0. rewrite Hmaj.
  rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
  assert (Hinj : injective eq eq (fun x => 1 * (x - gp pos g))) by (apply similarity_injective; lra).
  assert (Proper (eq ==> eq) (fun x => 1 * (x - gp pos g))) by now repeat intro; subst.
  rewrite nominal_spectrum_similarity, multiset_map, M.map_support, map_length; trivial.
  assert (H0 : 1 * (gp pos g - gp pos g) = 0) by ring.
  unfold M.elt.
  destruct (beq_nat (@length R (M.support (multiset (nominal_spectrum pos)))) 3) eqn:H3.
  - rewrite nominal_spectrum_similarity, multiset_map, M.map_support; trivial.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
    rewrite sort_map_increasing; try now apply similarity_increasing; lra.
    rewrite <- H0 at 1. rewrite (map_nth (fun x => 1 * (x - gp pos g))). field_simplify.
    rewrite (nth_indep _ _ 0). reflexivity. rewrite beq_nat_true_iff in H3.
    rewrite <- Permuted_sort. unfold M.elt in H3. rewrite H3. omega.
  - rewrite <- H0 at 1. rewrite is_extremal_similarity_invariant; try exact R1_neq_R0.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
    destruct (is_extremal (gp pos g) (nominal_spectrum pos)). field.
    rewrite extreme_center_similarity_invariant; try exact R1_neq_R0. field_simplify.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. now rewrite <- lift_gp_equiv.
Qed.
Print Assumptions round_simplify.

(* Definitions of two subsets of robots: active and idle ones. *)
Definition idle nG (da : demonic_action nG 0) := filter (fun x => Rdec_bool (frame da x) 0) (Gnames nG).
Definition active nG (da : demonic_action nG 0) := filter (fun x => negb (Rdec_bool (frame da x) 0)) (Gnames nG).

(* General result to put in ConvergentFormalism *)
Lemma move_active : forall r conf da g, round r da (gp conf) g <> gp conf g -> In g (active da).
Proof.
intros r conf da g Hmove. unfold active. rewrite filter_In. split.
+ unfold Gnames. change g with (id g). apply In_fin_map.
+ unfold round in Hmove. unfold Rdec_bool. destruct (Rdec (frame da g) 0).
  - now elim Hmove.
  - reflexivity.
Qed.

Theorem nominal_spectrum_simplify : forall (da : demonic_action nG 0) pos,
  Permutation (nominal_spectrum pos) (map (gp pos) (idle da) ++ map (gp pos) (active da)).
Proof.
intros da pos.
rewrite (lift_gp_equiv pos), <- (if_ExtEq (fun g => Rdec_bool (frame da g) 0) (gp pos)) at 1.
unfold lift_gp. rewrite (nominal_spectrum_combineG (fun g => Rdec_bool (frame da g) 0)).
rewrite partition_filter, app_nil_r. reflexivity.
Qed.

Theorem nominal_spectrum_round_simplify : forall (da : demonic_action nG 0) pos,
  Permutation
    (nominal_spectrum (lift_gp (round robogram da (gp pos))))
    (* robots that are not activated this turn *)
    (map (gp pos) (idle da)
    (* robots that are activated this turn *)
    ++ map (fun g => match majority_stack (nominal_spectrum pos) with
                       | NoResult => 0
                       | Valid pt n => pt
                       | Invalid n => if beq_nat (length (M.support (multiset (nominal_spectrum pos)))) 3
                                      then List.nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0
                                      else if is_extremal (gp pos g) (nominal_spectrum pos) then gp pos g
                                           else extreme_center (nominal_spectrum pos)
                     end)
           (active da)).
Proof.
intros da pos. rewrite round_simplify. unfold lift_gp. rewrite (if_Rdec_ExtEq 0 (frame da)).
rewrite nominal_spectrum_combineG. simpl. rewrite app_nil_r, partition_filter. reflexivity.
Qed.

(** ** Simplification of the global position in the three cases of the robogram **)

(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Stack_at_grow :  forall pt pos (da : demonic_action nG 0),
  Stack_at pt pos -> (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
                     >= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros pt pos da Hstack.
(* we first simplify the lhs *)
rewrite <- majority_stack_spec in Hstack. destruct Hstack as [m Hstack].
rewrite nominal_spectrum_round_simplify, Hstack. rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec. rewrite <- (map_length (gp pos)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.
Print Assumptions Stack_at_grow.

(* This proof follows the exact same structure.
   It is simpler because among robots that are activated, none goes to pt' <> pt *)
Theorem Stack_at_wither : forall pt pt' pos (da : demonic_action nG 0), pt <> pt' ->
  Stack_at pt pos -> (M.multiplicity pt' (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
                     <= M.multiplicity pt' (multiset (nominal_spectrum pos)))%nat.
Proof.
intros pt pt' pos da Hdiff Hstack.
(* we first simplify the lhs *)
rewrite <- majority_stack_spec in Hstack. destruct Hstack as [m Hstack].
rewrite nominal_spectrum_round_simplify, Hstack. repeat rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* No activated robot goes to pt' as pt' <> pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full. now symmetry in Heq. omega.
Qed.

(** As a consequence, whenever there is a majority stack, it remains forever so. **)
Theorem Stack_at_forever : forall pt pos (da : demonic_action nG 0),
  Stack_at pt pos -> Stack_at pt (lift_gp (round robogram da (gp pos))).
Proof.
intros pt pos da Hstack. assert (Hs := Hstack). destruct Hs as [n [? Hpos]].
eexists. split. reflexivity. intros pt' Hdiff.
eapply le_lt_trans. apply Stack_at_wither with pt; trivial.
eapply lt_le_trans. apply Hpos. assumption.
subst n. apply Stack_at_grow. assumption.
Qed.


(*Existing Instance range_compat.*)
Existing Instance nominal_spectrum_compat.
Existing Instance lift_gp_compat.


(** If we have three stacks, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  ExtEq (round robogram da (gp pos))
        (fun g => if Rdec (frame da g) 0 then gp pos g
                  else nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0).
Proof.
intros da pos n Hmaj H3.
rewrite round_simplify; trivial. intro g. Rdec_full. reflexivity.
rewrite Hmaj, H3. rewrite <- beq_nat_refl.
apply nth_indep. unfold M.elt in H3. rewrite <- (Permutation_length (Permuted_sort _)), H3. omega.
Qed.

Lemma nominal_spectrum_3_stacks : forall pos,
    (length (M.support (multiset (nominal_spectrum pos))) >= 3%nat)%nat <->
    exists pt1 pt2 pt3 l, exists n1 n2 n3,
        pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3 /\
        (0 < n1)%nat /\ (0 < n2)%nat /\ (0 < n3)%nat /\
        Permutation (nominal_spectrum pos) (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3++l).
Proof.
intro pos. split; intro H.
- assert (Hl : exists pt1 pt2 pt3 l, M.support (multiset (nominal_spectrum pos)) =  pt1 :: pt2 :: pt3 :: l).
  { destruct (M.support (multiset (nominal_spectrum pos))) as [| a [| b [| c [| d l]]]]; inversion H; try (exfalso;omega).
    - exists a. exists b. exists c. exists nil. reflexivity.
    - exists a. exists b. exists c. exists (d::l). reflexivity. } clear H.
  destruct Hl as [pt1 [pt2 [pt3 [ l Hl]]]]. exists pt1. exists pt2. exists pt3.
  exists (remove Rdec pt3 (remove Rdec pt2 (remove Rdec pt1 (nominal_spectrum pos)))).
  exists (M.multiplicity pt1 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt2 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt3 (multiset (nominal_spectrum pos))).
  assert (Hdup := M.support_NoDupA (multiset (nominal_spectrum pos))).
  rewrite Hl in Hdup. inversion_clear Hdup. inversion_clear H0. clear H2.
  assert (H12 : pt1 <> pt2). { intro Habs. apply H. now left. }
  assert (H13 : pt1 <> pt3). { intro Habs. apply H. now right; left. }
  assert (H23 : pt2 <> pt3). { intro Habs. apply H1. now left. }
  clear H H1. repeat split; trivial.
  + change (M.In pt1 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now left.
  + change (M.In pt2 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now right; left.
  + change (M.In pt3 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now do 2 right; left.
  + do 3 rewrite multiset_spec. etransitivity. apply (remove_count_occ_restore Rdec pt1).
    apply Permutation_app. reflexivity. etransitivity. apply (remove_count_occ_restore Rdec pt2).
    apply Permutation_app. now rewrite count_occ_remove_out.
    etransitivity.  apply (remove_count_occ_restore Rdec pt3).
    apply Permutation_app. rewrite count_occ_remove_out;auto.
    now rewrite count_occ_remove_out.
    reflexivity.

- destruct H as [pt1 [pt2 [pt3 [l [n1 [n2 [n3 [H12 [H23 [H13 [Hn1 [Hn2 [Hn3 Hperm]]]]]]]]]]]]].
  rewrite Hperm. do 3 rewrite multiset_app. repeat rewrite multiset_alls.
  do 3 rewrite M.add_union_singleton.
  unfold ge.

  assert (In pt1 (M.support (M.add pt1 n1 (M.add pt2 n2 (M.add pt3 n3 (multiset l)))))).
  { rewrite <- InA_Leibniz.
    rewrite M.support_spec.
    unfold M.In.
    rewrite M.add_spec.
    omega. }
  assert (In pt2 (M.support (M.add pt1 n1 (M.add pt2 n2 (M.add pt3 n3 (multiset l)))))).
  { rewrite <- InA_Leibniz.
    rewrite M.support_spec.
    unfold M.In.
    rewrite M.add_spec';auto.
    unfold M.In.
    rewrite M.add_spec;auto.
    omega. }
  assert (In pt3 (M.support (M.add pt1 n1 (M.add pt2 n2 (M.add pt3 n3 (multiset l)))))).
  { rewrite <- InA_Leibniz.
    rewrite M.support_spec.
    unfold M.In.
    rewrite M.add_spec';auto.
    unfold M.In.
    rewrite M.add_spec';auto.
    unfold M.In.
    rewrite M.add_spec;auto.
    omega. }
  remember (M.support (M.add pt1 n1 (M.add pt2 n2 (M.add pt3 n3 (multiset l))))) as lst.
  clear -H H0 H1 H12 H23 H13.
  rewrite <- InA_Leibniz in *.
  apply (PermutationA_split _) in H.
  destruct H.
  rewrite H in *.
  simpl.
  apply le_n_S.
  rewrite -> InA_Leibniz in *.
  simpl in H0, H1.
  destruct H0, H1; try contradiction.
  rewrite <- InA_Leibniz in *.
  apply (PermutationA_split _) in H0.
  destruct H0.
  rewrite H0 in *.
  simpl.
  apply le_n_S.
  rewrite -> InA_Leibniz in *.
  simpl in H1.
  destruct H1; try contradiction.
  rewrite <- InA_Leibniz in *.
  apply (PermutationA_split _) in H1.
  destruct H1.
  rewrite H1 in *.
  simpl.
  apply le_n_S.
  auto with arith.
Qed.

Lemma nominal_spectrum_3_stacks_nil : forall pos, length (M.support (multiset (nominal_spectrum pos))) = 3%nat <->
  exists pt1 pt2 pt3, exists n1 n2 n3, pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3 /\
    (0 < n1)%nat /\ (0 < n2)%nat /\ (0 < n3)%nat /\
    Permutation (nominal_spectrum pos) (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3).
Proof.
intro pos. split; intro H.
+ assert (Hl : exists pt1 pt2 pt3, M.support (multiset (nominal_spectrum pos)) =  pt1 :: pt2 :: pt3 :: nil).
  { destruct (M.support (multiset (nominal_spectrum pos))) as [| a [| b [| c [| d l]]]]; inversion H.
    exists a. exists b. exists c. reflexivity. } clear H.
  destruct Hl as [pt1 [pt2 [pt3 Hl]]]. exists pt1. exists pt2. exists pt3.
  exists (M.multiplicity pt1 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt2 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt3 (multiset (nominal_spectrum pos))).
  assert (Hdup := M.support_NoDupA (multiset (nominal_spectrum pos))).
  rewrite Hl in Hdup. inversion_clear Hdup. inversion_clear H0. clear H2.
  assert (H12 : pt1 <> pt2). { intro Habs. apply H. now left. }
  assert (H13 : pt1 <> pt3). { intro Habs. apply H. now right; left. }
  assert (H23 : pt2 <> pt3). { intro Habs. apply H1. now left. }
  clear H H1. repeat split; trivial.
  - change (M.In pt1 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now left.
  - change (M.In pt2 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now right; left.
  - change (M.In pt3 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now do 2 right; left.
  - do 3 rewrite multiset_spec. etransitivity. apply (remove_count_occ_restore Rdec pt1).
    apply Permutation_app. reflexivity. etransitivity. apply (remove_count_occ_restore Rdec pt2).
    apply Permutation_app. now rewrite count_occ_remove_out.
    assert (Hin : forall x, In x (nominal_spectrum pos) -> x = pt1 \/ x = pt2 \/ x = pt3).
    { intros x Hin. cut (In x (M.support (multiset (nominal_spectrum pos)))).
        rewrite Hl. intros [| [| [|]]]; intuition.  now apply multiset_support. }
    assert (Hrem : forall x, In x (remove Rdec pt2 (remove Rdec pt1 (nominal_spectrum pos))) -> x = pt3).
    { intros x H'. rewrite (remove_in_iff _ _) in H'. destruct H' as [H' ?].
      rewrite (remove_in_iff _ _) in H'. destruct H' as [H' ?]. apply Hin in H'. intuition. }
    rewrite alls_carac in Hrem. rewrite Hrem. f_equiv.
    clear Hrem Hl. induction (nominal_spectrum pos).
      reflexivity.
      simpl. repeat Rdec_full; try subst a.
        contradiction.
        apply IHs. intros x Hx. apply Hin. now right.
        simpl. Rdec_full. contradiction. simpl. f_equal. apply IHs. intros x Hx. apply Hin. now right.
        simpl. Rdec_full.
          subst a. apply IHs. intros x Hx. apply Hin. now right.
          exfalso. assert (Ha : In a (a :: s)) by now left. apply Hin in Ha. destruct Ha as [ | [|]]; auto.
+ destruct H as [pt1 [pt2 [pt3 [n1 [n2 [n3 [H12 [H23 [H13 [Hn1 [Hn2 [Hn3 Hperm]]]]]]]]]]]].
  rewrite Hperm. do 2 rewrite multiset_app. do 3 rewrite multiset_alls.
  do 2 rewrite M.add_union_singleton. rewrite M.support_add; trivial. unfold Rdecidable.eq_dec.
  destruct (InA_dec Rdec pt1 (M.support (M.add pt2 n2 (M.singleton pt3 n3)))) as [Hin | Hin].
  - rewrite M.support_add in Hin; trivial. unfold Rdecidable.eq_dec in Hin.
    destruct (InA_dec (eqA:=eq) Rdec pt2 (M.support (M.singleton pt3 n3))) as [Hin2 | Hin2].
      rewrite M.support_singleton in Hin; try omega. inversion_clear Hin. contradiction. now inversion H.
      inversion_clear Hin. contradiction. rewrite M.support_singleton in H; try omega.
      inversion_clear H. contradiction. now inversion H0.
  - simpl. f_equal. clear Hin. rewrite M.support_add; trivial. unfold Rdecidable.eq_dec.
    destruct (InA_dec Rdec pt2 (M.support (M.singleton pt3 n3))) as [Hin | Hin].
      rewrite M.support_singleton in Hin; try omega. inversion_clear Hin. contradiction. now inversion H.
      simpl. f_equal. rewrite M.support_singleton; simpl; omega.
Qed.


Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Corollary nominal_spectrum_Three : forall pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  exists pt1 pt2 pt3, exists m, pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3 /\ (0 < m <= n)%nat /\
    Permutation (nominal_spectrum pos) (alls pt1 n ++ alls pt2 n ++ alls pt3 m).
Proof.
intros pos n Hmaj H3. rewrite nominal_spectrum_3_stacks_nil in H3.
destruct H3 as [pt1 [pt2 [pt3 [n1 [n2 [n3 [H12 [H23 [H13 [Hn1 [Hn2 [Hn3 Hperm]]]]]]]]]]]].
rewrite Hperm in Hmaj. rewrite majority_stack_Invalid_spec in Hmaj.
destruct Hmaj as [Hn [x [y [Hx [Hy [Hxy Hother]]]]]].
assert (Heqx : x = pt1 \/ x = pt2 \/ x = pt3).
{ rewrite <- Hx in Hn. change (M.In x (multiset (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3))) in Hn.
  rewrite <- M.support_spec, InA_Leibniz, multiset_support in Hn.
  do 2 rewrite in_app_iff in Hn. now destruct Hn as [Hn | [Hn | Hn]]; apply alls_In in Hn; auto. }
assert (Heqy : y = pt1 \/ y = pt2 \/ y = pt3).
{ rewrite <- Hy in Hn. change (M.In y (multiset (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3))) in Hn.
  rewrite <- M.support_spec, InA_Leibniz, multiset_support in Hn.
  do 2 rewrite in_app_iff in Hn. now destruct Hn as [Hn | [Hn | Hn]]; apply alls_In in Hn; auto. }
(* We consider the 6 possible permutations. *)
destruct Heqx as [ | [ | ]]; destruct Heqy as [ | [ | ]]; subst x y; try now elim Hxy.
+ (* x = pt1 & y = pt2 *)
  exists pt1. exists pt2. exists pt3. exists n3. specialize (Hother pt3).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. do 2 Rdec_full; try now symmetry in Heq; contradiction. simpl. intro Hother.
  now repeat split.
+ (* x = pt1 & y = pt3 *)
  exists pt1. exists pt3. exists pt2. exists n2. specialize (Hother pt2).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. apply Permutation_app. reflexivity. apply Permutation_app_comm.
+ (* x = pt2 & y = pt1 *)
  exists pt1. exists pt2. exists pt3. exists n3. specialize (Hother pt3).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. do 2 Rdec_full; try now symmetry in Heq; contradiction. simpl. intro Hother.
  now repeat split.
+ (* x = pt2 & y = pt3 *)
  exists pt2. exists pt3. exists pt1. exists n1. specialize (Hother pt1).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec. repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. now rewrite Permutation_app_comm, app_assoc.
+ (* x = pt3 & y = pt1 *)
  exists pt1. exists pt3. exists pt2. exists n2. specialize (Hother pt2).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. apply Permutation_app. reflexivity. apply Permutation_app_comm.
+ (* x = pt3 & y = pt2 *)
  exists pt2. exists pt3. exists pt1. exists n1. specialize (Hother pt1).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec. repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. now rewrite Permutation_app_comm, app_assoc.
Qed.

Theorem Three_grow : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  let pt := nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0 in
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
   >= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros da pos n Hmaj H3. hnf.
pose (pt := nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0%R). fold pt.
(* We simplify the lhs *)
rewrite nominal_spectrum_round_simplify, Hmaj, H3, <- beq_nat_refl.
rewrite multiset_app, M.union_spec.
(* We split the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec. unfold pt.
Rdec. rewrite <- (map_length (gp pos)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.

Theorem Three_wither : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  forall pt, pt <> nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0 ->
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
   <= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros da pos n Hmaj H3 pt Hdiff.
(* we first simplify the lhs *)
rewrite nominal_spectrum_round_simplify, Hmaj, H3, <- beq_nat_refl.
rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* No activated robot goes to pt' as pt' <> pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full. contradiction. omega.
Qed.

(** If we do not have a majority stack and have more than three stacks,
    then all activated robots except the ones on the extreme positions [x] and [t] go to [(x + t) / 2]. **)
(*
Lemma Generic_min : forall l n x t,
  majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> forall d, hd d (sort l) = x.
Proof.
intros l n x t Hmaj Hrange Hx Ht d. destruct (sort l) eqn:Hl.
+ rewrite Permuted_sort, Hl in Hmaj. rewrite majority_stack_nil in Hmaj. discriminate Hmaj.
+ apply Rle_antisym.
  - rewrite <- Hl. now apply sort_min.
  - rewrite range_split in Hrange. destruct Hrange as [Hrange _]. rewrite Forall_forall in Hrange.
    apply Hrange. apply (Permutation_in _ (symmetry (Permuted_sort _))). rewrite Hl. now left.
Qed.

Lemma Generic_max : forall l n x t,
  majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> forall d, last (sort l) d = t.
Proof.
intros l n x t Hmaj Hrange Hx Ht d. destruct (sort l) eqn:Hl.
+ rewrite Permuted_sort, Hl in Hmaj. rewrite majority_stack_nil in Hmaj. discriminate Hmaj.
+ apply Rle_antisym.
  - rewrite range_split, Forall_forall, Forall_forall in Hrange.
    destruct Hrange as [_ Hrange]. apply Hrange. apply (Permutation_in _ (symmetry (Permuted_sort _))).
    rewrite Hl. apply last_In. discriminate.
  - rewrite <- Hl. now apply sort_max.
Qed.
*)
Lemma round_simplify_Generic : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
  let l_min := hd 0%R (sort (nominal_spectrum conf)) in
  let l_max := last (sort (nominal_spectrum conf)) 0%R in
  ExtEq (round robogram da (gp conf))
        (fun g => if Rdec (frame da g) 0 then gp conf g else
                  if Rdec (gp conf g) l_min then l_min else
                  if Rdec (gp conf g) l_max then l_max else (l_min + l_max) / 2).
Proof.
intros da conf n Hmaj Hlen.
red. intro g. rewrite round_simplify; trivial. Rdec_full. reflexivity.
rewrite Hmaj. rewrite <- beq_nat_false_iff in Hlen. rewrite Hlen.
assert (Hnil : sort (nominal_spectrum conf) <> nil).
{ intro Habs. apply (nominal_spectrum_nil conf). apply Permutation_nil.
  rewrite <- Habs. symmetry. apply Permuted_sort. }
unfold is_extremal. rewrite (hd_invariant _ 0), (last_invariant _ 0); trivial.
now repeat Rdec_full.
Qed.

(** If we have no majority stack (hence more than one stack), then the extreme locations are different. **)
Lemma min_max_diff :
  forall l n, majority_stack l = Invalid n -> hd 0 (sort l) <> last (sort l) 0.
Proof.
intros l n Hl Heq.
assert (Hin : forall x, In x l -> x = hd 0 (sort l)).
{ intros x Hin. apply Rle_antisym.
  - rewrite Heq. now apply sort_max.
  - now apply sort_min. }
assert (Hlen : (2 <= length l)%nat) by apply (majority_stack_Invalid_length Hl).
rewrite alls_carac in Hin. rewrite Hin in Hl.
rewrite majority_stack_alls in Hl. discriminate. omega.
Qed.


Theorem Generic_grow : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
  (M.multiplicity (extreme_center (nominal_spectrum conf)) (multiset (nominal_spectrum conf))
   <= M.multiplicity (extreme_center (nominal_spectrum conf))
      (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf))))))%nat.
Proof.
intros da conf n Hmaj Hlen.
(* We simplify the rhs *)
rewrite <- beq_nat_false_iff in Hlen.
rewrite nominal_spectrum_round_simplify, Hmaj, Hlen, multiset_app, M.union_spec.
pose (pt := extreme_center (nominal_spectrum conf)). fold pt.
(* Same thing for the lhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both configurations so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp conf g) (nominal_spectrum conf)) (gp conf))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec. rewrite <- (map_length (gp conf)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.

Theorem Generic_wither : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
  forall pt, pt <> extreme_center (nominal_spectrum conf) ->
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
   <= M.multiplicity pt (multiset (nominal_spectrum conf)))%nat.
Proof.
intros da pos n Hmaj Hlen pt Hdiff.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in Hlen.
rewrite nominal_spectrum_round_simplify, Hmaj, Hlen, multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp pos g) (nominal_spectrum pos)) (gp pos))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
apply plus_le_compat. reflexivity.
(* Among those that are activated, at least zero can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full. contradiction. omega.
Qed.

Theorem Generic_min_same : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
    hd 0%R (sort (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
    = hd 0%R (sort (nominal_spectrum conf)).
Proof.
Admitted.

Theorem Generic_max_same : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
    last (sort (nominal_spectrum (lift_gp (round robogram da (gp conf))))) 0%R
    = last (sort (nominal_spectrum conf)) 0%R.
Proof.
Admitted.

Corollary Generic_extreme_center_same : forall da conf n, 
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
    extreme_center (nominal_spectrum (lift_gp (round robogram da (gp conf))))
    = extreme_center (nominal_spectrum conf).
Proof.
intros da conf n Hmaj Hlen. unfold extreme_center.
now rewrite (Generic_min_same _ _ Hmaj Hlen), (Generic_max_same _ _ Hmaj Hlen).
Qed.

Theorem Generic_min_mult_same : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
  M.multiplicity
    (hd 0%R (sort (nominal_spectrum conf)))
    (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
  = M.multiplicity
    (hd 0%R (sort (nominal_spectrum conf)))
    (multiset (nominal_spectrum conf)).
Proof.
intros da conf n Hmaj Hlen.
remember (hd 0%R (sort (nominal_spectrum conf))) as pt.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in Hlen.
rewrite nominal_spectrum_round_simplify, Hmaj, Hlen, multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
f_equal.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp conf g) (nominal_spectrum conf)) (gp conf))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
f_equal.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full.
+ exfalso. subst. unfold extreme_center in Heq. assert (Hdiff := min_max_diff Hmaj). lra.
+ rewrite multiset_spec.
  cut (~ count_occ Rdec
    (map (gp conf)
       (filter (fun g => negb (is_extremal (gp conf g) (nominal_spectrum conf))) (active da)))
       pt > 0)%nat. omega.
  rewrite <- count_occ_In. intro Hin. rewrite in_map_iff in Hin. destruct Hin as [g [Heq Hin]].
  rewrite filter_In in Hin. destruct Hin as [_ Hin]. revert Hin.  unfold is_extremal.
  rewrite negb_true_iff. repeat Rdec_full; try discriminate. subst. elim Hneq0.
  rewrite Heq at 1. apply hd_invariant. apply sort_nil.
Qed.

Theorem Generic_max_mult_same : forall (da : demonic_action nG 0) conf n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) <> 3%nat ->
  M.multiplicity
    (last (sort (nominal_spectrum conf)) 0%R)
    (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
  = M.multiplicity
    (last (sort (nominal_spectrum conf)) 0%R)
    (multiset (nominal_spectrum conf)).
Proof.
intros da conf n Hmaj Hlen.
remember (last (sort (nominal_spectrum conf)) 0%R) as pt.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in Hlen.
rewrite nominal_spectrum_round_simplify, Hmaj, Hlen, multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
f_equal.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp conf g) (nominal_spectrum conf)) (gp conf))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
f_equal.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full.
+ exfalso. subst. unfold extreme_center in Heq. assert (Hdiff := min_max_diff Hmaj). lra.
+ rewrite multiset_spec.
  cut (~ count_occ Rdec
    (map (gp conf)
       (filter (fun g => negb (is_extremal (gp conf g) (nominal_spectrum conf))) (active da)))
       pt > 0)%nat. omega.
  rewrite <- count_occ_In. intro Hin. rewrite in_map_iff in Hin. destruct Hin as [g [Heq Hin]].
  rewrite filter_In in Hin. destruct Hin as [_ Hin]. revert Hin.  unfold is_extremal.
  rewrite negb_true_iff. repeat Rdec_full; try discriminate. subst. elim Hneq1.
  rewrite Heq at 1. apply last_invariant. apply sort_nil.
Qed.


Theorem Stack_at_meeting : forall pos pt (d : demon nG 0) k,
  kFair k d -> Stack_at pt pos -> WillGather pt (execute robogram d (gp pos)).
Proof.
Admitted.

Theorem gathered_at_forever : forall pt gp (da : demonic_action nG 0),
  gathered_at pt gp -> gathered_at pt (round robogram da gp).
Proof.
intros pt gp [] Hgather. unfold round. simpl.
intro g. destruct (Rdec (frame g) 0). now apply Hgather.
rewrite Hgather. rewrite <- Rplus_0_r. f_equal. rewrite <- (Rmult_0_r (/ frame g)). f_equal.
unfold similarity. simpl. rewrite (spectrum_exteq g _ (lift_gp (fun _ => 0))). unfold robogram.
assert (spectrum_of g (lift_gp (fun _ => 0)) = alls 0 nG) as Heq.
{ apply Permutation_alls.
  transitivity (nominal_spectrum (lift_gp (fun _ : G nG => 0))).
    now apply spectrum_ok.
    now rewrite nominal_spectrum_alls. }
rewrite Heq. unfold majority_stack.
rewrite multiset_alls, M.fold_singleton; simpl; try omega.
  reflexivity.
  generalize size_G. omega.
  now repeat intro; subst.
  split; (now intros []) || intro x; simpl.
    rewrite Hgather, Rminus_diag_eq. now rewrite Rmult_0_r.
    reflexivity.
    now apply Fin.case0.
Qed.

Lemma Permutation_eq_pair_equiv : forall l1 l2, Permutation l1 l2 <-> PermutationA M.eq_pair l1 l2.
Proof.
assert (HeqA : (eq ==> eq ==> iff)%signature Logic.eq M.eq_pair).
{ intros [? ?] ? ? [? ?] ? ?. subst. now split; intro H; inversion H; reflexivity || hnf in *; simpl in *; subst. }
intros l1 l2. rewrite <- PermutationA_Leibniz. now apply (PermutationA_eq_compat HeqA).
Qed.

Lemma forbidden_elements_perm : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2 /\ Permutation (M.elements (multiset (nominal_spectrum pos)))
                                                              ((pt1, div2 nG) :: (pt2, div2 nG) :: nil).
Proof.
intro pos. split; intros [pt1 [pt2 [Hneq Hpos]]]; exists pt1; exists pt2; split; trivial.
+ rewrite Permutation_eq_pair_equiv, Hpos, multiset_app, multiset_alls, multiset_alls, M.add_union_singleton.
  apply (NoDupA_equivlistA_PermutationA _).
  - apply (NoDupA_strengthen _ (M.elements_NoDupA _)).
  - apply NoDupA_2. intros [Habs _]. apply Hneq. apply Habs.
  - intros [x n]. rewrite M.elements_add. simpl. split; intro H.
      destruct H as [[? [? H]] | [_ H]].
        subst. rewrite M.singleton_spec. Rdec_full. contradiction. rewrite plus_0_r. now left.
        right. rewrite M.elements_spec in H. destruct H as [H Hn]. simpl in H. rewrite M.singleton_spec in H.
        revert H. Rdec_full; intro H. subst. now left. simpl in Hn. omega.
      rewrite M.singleton_spec. inversion_clear H.
        left. destruct H0. hnf in *; simpl in *. subst. repeat split.
          Rdec_full. contradiction. symmetry. now apply plus_0_r.
          now apply half_size_pos.
        right. inversion_clear H0.
          split.
            destruct H as [H _]. hnf in H. simpl in H. subst. now auto.
            rewrite M.elements_singleton. now left. now apply half_size_pos.
          inversion H.
+ assert (Hin : forall xn, InA M.eq_pair xn (M.elements (multiset (nominal_spectrum pos)))
                           <-> (fst xn = pt1 \/ fst xn = pt2) /\ snd xn = div2 nG).
  { intros [x n]. rewrite Permutation_eq_pair_equiv in Hpos. rewrite Hpos.
    split; intro H.
    + inversion H.
      - destruct H1. hnf in *; simpl in *. subst. auto.
      - inversion H1.
          destruct H4. hnf in *; simpl in *. subst. auto.
          inversion H4.
    + simpl in H. destruct H as [[? | ? ] ?]; subst.
        now left.
        now right; left. }
  (* If (x, n) belongs to elements l, then Permutation l alls x n ++ l' for some l' not containg x.
     Let do this twice to remove all elements of elements l. *)
  assert (Hmul1 : M.multiplicity pt1 (multiset (nominal_spectrum pos)) = div2 nG).
  { apply proj1 with (div2 nG > 0)%nat. rewrite <- (M.elements_spec (pt1, div2 nG)).
    rewrite Hin. now split; try left. }
  assert (Hmul2 : M.multiplicity pt2 (multiset (nominal_spectrum pos)) = div2 nG).
  { apply proj1 with (div2 nG > 0)%nat. rewrite <- (M.elements_spec (pt2, div2 nG)).
    rewrite Hin. now split; try right. }
  apply multiset_Permutation in Hmul1. destruct Hmul1 as [l [Hl Hperm]].
  rewrite Hperm. apply Permutation_app. reflexivity.
  rewrite Hperm, multiset_app, M.union_spec, multiset_alls, M.singleton_spec in Hmul2.
  revert Hmul2. Rdec_full. symmetry in Heq. contradiction. clear Hneq0. simpl. intro Hmul2.
  apply multiset_Permutation in Hmul2. destruct Hmul2 as [l' [Hl' Hperm']].
  rewrite <- app_nil_r, Hperm'. apply Permutation_app. reflexivity.
  (* Now we must prove that there is no other element in the spectrum because there is none in its multiset. *)
  destruct l'. reflexivity. exfalso. cut (e = pt1 \/ e = pt2).
  - intros [? | ?]; subst e.
      apply Hl. rewrite Hperm'. apply in_app_iff. now right; left.
      apply Hl'. now left.
  - apply proj1 with (M.multiplicity e (multiset l) = div2 nG).
    rewrite <- (Hin (e, M.multiplicity e (multiset l))). rewrite Hperm.
    rewrite multiset_app, multiset_alls, M.elements_union. simpl. unfold M.In.
    rewrite M.singleton_spec. Rdec_full.
      elim Hl. subst e. rewrite Hperm'. rewrite in_app_iff. now right; left.
      split.
        right. rewrite Hperm', multiset_app, multiset_alls, multiset_cons, M.union_spec, M.add_spec. simpl. omega.
        reflexivity.
Qed.

Corollary forbidden_elements : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2
                    /\ M.elements (multiset (nominal_spectrum pos)) = (pt1, div2 nG) :: (pt2, div2 nG) :: nil.
Proof.
intro pos. rewrite forbidden_elements_perm. split; intros [pt1 [pt2 [Hdiff H]]].
+ symmetry in H. apply Permutation_length_2_inv in H. destruct H as [H | H].
  - exists pt1. exists pt2. auto.
  - exists pt2. exists pt1. auto.
+ exists pt1. exists pt2. rewrite H. auto.
Qed.

Corollary forbidden_multiplicity : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2
              /\ M.multiplicity pt1 (multiset (nominal_spectrum pos)) = div2 nG
              /\ M.multiplicity pt2 (multiset (nominal_spectrum pos)) = div2 nG
              /\ forall pt, pt <> pt1 -> pt <> pt2 -> M.multiplicity pt (multiset (nominal_spectrum pos)) = 0%nat.
Proof.
intro pos. split; intros [pt1 [pt2 [Hdiff H]]].
+ exists pt1. exists pt2. repeat split.
  - assumption.
  - apply proj1 with (div2 nG > 0)%nat. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. Rdec. Rdec_full. contradiction. split.
      now apply plus_0_r.
      now apply half_size_pos.
  - apply proj1 with (div2 nG > 0)%nat. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. Rdec. Rdec_full. symmetry in Heq. contradiction. split.
      reflexivity.
      now apply half_size_pos.
  - intros pt Hdiff1 Hdiff2. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. now do 2 Rdec_full.
+ rewrite forbidden_elements_perm. exists pt1. exists pt2. split; trivial.
  apply Permutation_eq_pair_equiv. apply (NoDupA_equivlistA_PermutationA _).
  - apply (NoDupA_strengthen _ (M.elements_NoDupA _)).
  - apply NoDupA_2. intros [Habs _]. apply Hdiff. apply Habs.
  - intros [x n]. destruct H as [Hin1 [Hin2 Hin]]. destruct (Rdec x pt1).
      subst. rewrite M.elements_spec. simpl. rewrite Hin1. split; intro H.
        now left.
        inversion_clear H.
          destruct H0 as [_ H]. hnf in H; simpl in H. subst n. split. reflexivity. now apply half_size_pos.
          inversion_clear H0. destruct H as [Habs _]. elim Hdiff. now apply Habs. now inversion H.
      destruct (Rdec x pt2).
        subst. rewrite M.elements_spec. simpl. rewrite Hin2. split; intro H.
          now right; left.
          inversion_clear H.
            destruct H0 as [Habs _]. elim Hdiff. symmetry. now apply Habs.
            inversion_clear H0.
              destruct H as [_ H]. hnf in H; simpl in H. subst n. split. reflexivity. now apply half_size_pos.
              now inversion H.
        split; intro H.
          rewrite M.elements_spec in H. rewrite Hin in H; try assumption. simpl in H. omega.
          inversion_clear H.
            destruct H0 as [H _]. hnf in H; simpl in H. contradiction.
            inversion_clear H0.
              destruct H as [H _]. hnf in H; simpl in H. contradiction.
              now inversion H.
Qed.

Lemma forbidden_even : forall pos, forbidden pos -> NPeano.Even nG.
Proof.
intros pos [pt1 [pt2 [Hdiff Hperm]]]. exists (div2 nG).
rewrite <- plus_0_r at 1. rewrite <- (nominal_spectrum_length pos).
rewrite Hperm, app_length, alls_length, alls_length. omega.
Qed.

Lemma Stack_at_forbidden : forall pt pos, Stack_at pt pos -> ~forbidden pos.
Proof.
intros pt pos [n [Hstack Hother]] [pt1 [pt2 [Hdiff Habs]]]. revert Hstack Hother.
setoid_rewrite Habs.
setoid_rewrite multiset_app. setoid_rewrite M.union_spec.
setoid_rewrite multiset_alls. setoid_rewrite M.singleton_spec.
do 2 Rdec_full; try subst pt.
- contradiction.
- rewrite plus_0_r. intro. subst. intro H. specialize (H pt2 Hdiff). revert H. Rdec. intro. omega.
- simpl. intro. subst. intro H. specialize (H pt1 Hneq). revert H. Rdec. intro. omega.
- simpl. intro. subst. intro H. specialize (H pt1 Hneq). revert H. Rdec. intro. omega.
Qed.

(* Other proof for never_forbidden *)

Hypothesis same_destination : forall da pos g1 g2, In g1 (@active nG da) -> In g2 (active da) ->
  round robogram da pos.(gp) g1 = round robogram da pos.(gp) g2.

Lemma no_active_same_conf :
  forall da conf, @active nG da = nil -> PosEq (lift_gp (round robogram da conf.(gp))) conf.
Proof.
intros da conf Hactive. rewrite (lift_gp_equiv conf) at 2. apply lift_gp_compat.
rewrite round_simplify. intro r.
destruct (Rdec (frame da r) 0) as [Heq | Heq]; trivial.
assert (Hin : In r (active da)).
{ unfold active. rewrite filter_In. split.
  - unfold Gnames. change r with (id r). apply In_fin_map.
  - destruct (Rdec_bool (frame da r) 0) eqn:Habs; trivial.
    rewrite Rdec_bool_true_iff in Habs. contradiction. }
rewrite Hactive in Hin. elim Hin.
Qed.

(* TODO *)
Lemma nominal_spectrum_3_stacks_beaucoup_mieux:
  forall pos,
    (length (M.support (multiset (nominal_spectrum pos))) >= 3)%nat ->
    exists (pt1 pt2 pt3 : R) l,
      pt1 <> pt2 /\
      pt2 <> pt3 /\
      pt1 <> pt3 /\
      Permutation (nominal_spectrum pos) (pt1::pt2::pt3::l).
Proof.
  intros pos H.
  rewrite (nominal_spectrum_3_stacks pos) in H.
  decompose [ex and] H; clear H.
  destruct x3; [exfalso; omega|].
  destruct x4; [exfalso; omega|].
  destruct x5; [exfalso; omega|].
  simpl in H7.
  exists x, x0 , x1 , (alls x x3 ++ alls x0 x4 ++ alls x1 x5 ++ x2);repeat split;auto.
  rewrite H7.
  rewrite <- Permutation_middle.
  apply perm_skip, perm_skip.
  transitivity ((alls x x3 ++ x1 :: alls x0 x4 ++ alls x1 x5 ++ x2)).
  - apply Permutation_app_head.
    symmetry.
    apply Permutation_middle.
  - symmetry.
    apply Permutation_middle.
Qed.


Corollary nominal_spectrum_3_stacks_beaucoup_mieux_mieux:
  forall pos pt3,
    (length (M.support (multiset (nominal_spectrum pos))) >= 3)%nat ->
    M.In pt3 (multiset (nominal_spectrum pos)) ->
    exists (pt1 pt2 : R) l,
        pt1 <> pt2 /\
        pt2 <> pt3 /\
        pt1 <> pt3 /\
      Permutation (nominal_spectrum pos) (pt1::pt2::l).
Proof.
  intros pos pt3 H H0.
  decompose [and ex] (nominal_spectrum_3_stacks_beaucoup_mieux _ H).
  destruct (Rdec x pt3), (Rdec x0 pt3), (Rdec x1 pt3); subst;Rdec;eauto 10.
  - exists x0, x1,(pt3::x2);repeat split;auto.
    rewrite H5.
    clear -H5.
    change (Permutation ((pt3 :: x0 :: x1::nil) ++ x2) ((x0 :: x1 :: pt3 ::nil) ++ x2)).
    apply Permutation_app;try reflexivity.
    etransitivity.
    + eapply perm_swap.
    + eapply perm_skip.
      eapply perm_swap.
  - exists x, x1,(pt3::x2);repeat split;auto.
    rewrite H5.
    eapply perm_skip.
    eapply perm_swap.
Qed.

Lemma increase_move :
  forall r conf da pt,
    (M.multiplicity pt (multiset (nominal_spectrum conf))
     < M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round r da (gp conf))))))%nat ->
    exists g, round r da (gp conf) g = pt /\ round r da (gp conf) g <> (gp conf) g.
Proof.
  intros r conf da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (Rdec_bool ((round r da (gp conf) x))  pt)
                             (negb (Rdec_bool ((gp conf) x) pt)))) (Gnames nG)) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [g [Hin Heq_bool]].
    exists g.
    rewrite andb_true_iff, negb_true_iff, Rdec_bool_true_iff, Rdec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall g, round r da (gp conf) g <> pt \/ gp conf g = pt).
    { intro g. specialize (Hex g). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- Rdec_bool_false_iff, <- Rdec_bool_true_iff. apply Hex, In_Gnames. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt. SearchAbout M.filter.
Admitted.

Lemma not_forbidden_Invalid_length : forall pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  ~forbidden pos -> (length (M.support (multiset (nominal_spectrum pos))) >= 3)%nat.
Proof.
Admitted.

(* Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog p1.
   |\before(p2)| >= |\after(p2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2. *)
Theorem never_forbidden : forall (da : demonic_action nG 0) pos,
  ~forbidden pos -> ~forbidden (lift_gp (round robogram da pos.(gp))).
Proof.
intros da conf Hok.
(* Three cases for the robogram *)
destruct (majority_stack (nominal_spectrum conf)) eqn:Hs.
{ (* Absurd case: no robot *)
  rewrite majority_stack_NoResult_spec in Hs. elim (nominal_spectrum_nil _ Hs). }
{ (* 1) There is a majority tower *)
  apply Stack_at_forbidden with l. apply Stack_at_forever. rewrite <- majority_stack_spec. now exists n. }
(* A robot has moved otherwise we have the same configuration before nad it is forbidden. *)
assert (Hnil := no_active_same_conf da conf).
destruct (active da) eqn:Hneq.
* now rewrite Hnil.
* intro Habs.
  assert (Heven:=forbidden_even Habs). rewrite <- NPeano.even_spec in Heven.
  (* since we suppose (forbidden (round robogram)) there must be a robot that moves *)
  assert (Hex : List.existsb (fun g => negb (Rdec_bool (conf.(gp) g) (round robogram da conf.(gp) g))) (active da)).
  { rewrite existsb_forallb. unfold is_true. rewrite negb_true_iff. apply not_true_is_false.
    rewrite forallb_forall. setoid_rewrite Rdec_bool_true_iff. intro Hall.
    assert (Hconf : PosEq (lift_gp (round robogram da conf.(gp))) conf).
    { rewrite (lift_gp_equiv conf) at 2. apply lift_gp_compat.
      intro r. destruct (Rdec (frame da r) 0) as [Heq | Heq].
      + rewrite round_simplify, Heq. Rdec. reflexivity.
      + symmetry. apply Hall. unfold active. change r with (id r). rewrite filter_In. split.
        - unfold Gnames. apply In_fin_map.
        - now rewrite negb_true_iff, Rdec_bool_false_iff. }
    apply Hok. rewrite <- Hconf. assumption. }
  unfold is_true in Hex. rewrite existsb_exists in Hex. destruct Hex as [rmove [Hin Hrmove]].
  rewrite negb_true_iff, Rdec_bool_false_iff in Hrmove.
  (* the robot moves to one of the two locations in round robogram conf.(gp) *)
  destruct Habs as [p1 [p2 [Hdiff Hperm]]].
  assert (exists pt pt', ((pt = p1 /\ pt'=p2) \/ (pt = p2  /\ pt'=p1)) /\ round robogram da (gp conf) rmove = pt).
  { admit. }
  destruct H as [pt [pt' [h_pt h_rmove_pt]]].
  assert (Hdiff2:pt<>pt').
  { decompose [and or] h_pt;auto. }
  assert (h:forall g, In g (active da) -> round robogram da (gp conf) g = pt).
  { intros g0 h.
    rewrite <- h_rmove_pt.
    apply same_destination;auto. }
  assert (((div2 nG)%nat <= M.multiplicity pt' (multiset (nominal_spectrum conf)))%nat).
    { transitivity (M.multiplicity pt' (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))%nat).
      - rewrite Hperm.
        rewrite multiset_app.
        rewrite M.union_spec.
        rewrite multiset_alls, multiset_alls.
        rewrite M.singleton_spec, M.singleton_spec.
        do 2 Rdec_full.
        + subst.
          contradiction.
        + omega.
        + subst.
          omega.
        + decompose [and or] h_pt; contradiction.
      - 
        generalize (@increase_move robogram conf da pt').
        intro H1.
        cut (~(M.multiplicity pt' (multiset (nominal_spectrum conf))
             < M.multiplicity pt' (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf))))))%nat).
        + omega.
        + rewrite H1. intros (r ,(abs2, abs3)).
          apply Hdiff2.
          rewrite <- abs2.
          symmetry.
          apply h.
          subst. eapply move_active; eauto. }
    assert (Hlt : forall p, p<>pt'
                            -> (M.multiplicity p (multiset (nominal_spectrum conf)) < div2 nG)%nat).
    {
      assert (h_dedicace_lionel:M.In pt' (multiset (nominal_spectrum conf))).
      { unfold M.In.
        eapply lt_le_trans; try eassumption.
        apply half_size_pos.
      }
      assert (Hle := not_forbidden_Invalid_length Hs Hok).
      decompose [ex and] (@nominal_spectrum_3_stacks_beaucoup_mieux_mieux _ pt' Hle h_dedicace_lionel).
      rename x1 into lr'.
      setoid_rewrite H4.
      intros p h_diff.
      assert (Hpt' : M.multiplicity pt' (multiset lr') = M.multiplicity pt' (multiset (nominal_spectrum conf))).
      { rewrite H4, multiset_cons, multiset_cons, M.add_spec', M.add_spec'; auto. }
      destruct (@multiset_Permutation pt' lr' _ eq_refl) as [lr [Hlr1 Hlr2]].
      rewrite Hpt' in Hlr2. rewrite Hlr2 in H4.
      assert (Hlen := nominal_spectrum_length conf).
      rewrite H4 in Hlen. simpl in Hlen. rewrite app_length, alls_length in Hlen.
      rewrite (NPeano.Nat.div2_odd nG) in Hlen at 2. rewrite <- NPeano.Nat.negb_even, Heven in Hlen.
      simpl in Hlen.
      assert (length lr <= div2 nG -2)%nat by omega.
      rewrite multiset_cons, multiset_cons, Hlr2, multiset_app, multiset_alls.
      apply le_lt_trans with (length lr + 1)%nat; try omega.
      destruct (Rdec p x), (Rdec p x0);repeat subst.
      + now elim H1.
      + rewrite M.add_spec, M.add_spec';auto.
        rewrite M.union_spec, M.singleton_spec. Rdec_full; try contradiction.
        simpl. apply plus_le_compat_r. rewrite <- cardinal_multiset. apply M.cardinal_lower.
      + rewrite M.add_spec', M.add_spec;auto.
        rewrite M.union_spec, M.singleton_spec. Rdec_full; try contradiction.
        simpl. apply plus_le_compat_r. rewrite <- cardinal_multiset. apply M.cardinal_lower.
      + rewrite M.add_spec', M.add_spec';auto.
        rewrite M.union_spec, M.singleton_spec. Rdec_full; try contradiction.
        simpl. rewrite <- cardinal_multiset. etransitivity; apply M.cardinal_lower || omega.
    }
    rewrite majority_stack_Invalid_spec in Hs.
    decompose [and ex] Hs.
    assert (n = div2 nG).
    { apply le_antisym.
      + destruct (multiset_Permutation _ H2) as [lr' [Hlrx Hlr']].
        rewrite Hlr', multiset_app, multiset_alls, M.union_spec, M.singleton_spec in H1.
        destruct (Rdecidable.eq_dec x0 x) as [? | _]; try now elim H3.
        destruct (multiset_Permutation _ H1) as [lr [Hlrx0 Hlr]].
        assert (Hlen := nominal_spectrum_length conf).
        rewrite Hlr', app_length, Hlr, alls_length, app_length, alls_length in Hlen.
        rewrite (NPeano.Nat.div2_odd nG) in Hlen. rewrite <- NPeano.Nat.negb_even, Heven in Hlen.
        simpl in Hlen. omega.
      + etransitivity; eauto. }
    rewrite H4 in *. apply (lt_irrefl (div2 nG)).
    destruct (Rdec x pt').
    + subst. rewrite <- H1 at 1. apply Hlt. auto.
    + rewrite <- H2 at 1. now apply Hlt.
Qed.

Close Scope R_scope.


Section WfLexicographic_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive lexprod : A*B -> A*B -> Prop :=
  | left_lex :
      forall (x x':A) (y y':B), leA x x' -> lexprod (x, y) (x', y')
  | right_lex :
      forall (x:A) (y y':B), leB y y' -> lexprod (x, y) (x, y').

  Notation LexProd := (lexprod leA leB).

  Lemma acc_A_B_lexprod :
    forall x:A,
      Acc leA x ->
      (forall x0:A, clos_trans A leA x0 x -> well_founded leB) ->
      forall y:B, Acc leB y -> @Acc (A*B) lexprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    cut (leA x2 x); intros.
    apply IHAcc; auto with sets.
    intros.
    eapply H2.
    apply t_trans with x2; auto with sets.
    eassumption.

    red in H2.
    eapply H2.
    eauto with sets.

    injection H1.
    destruct 2.
    injection H3.
    destruct 2; auto with sets.

    rewrite <- H1.
    injection H3; intros _ Hx1.
    subst x1.
    apply IHAcc0.
    inversion H1.
    inversion H3.
    subst.
    assumption.
  Defined.

  Theorem wf_lexprod :
    well_founded leA ->
    well_founded leB -> well_founded lexprod.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a.
    apply acc_A_B_lexprod; auto with sets; intros.
  Defined.


End WfLexicographic_Product.


Function conf_to_NxN (conf: position nG 0) :=
  let s := nominal_spectrum conf in
  let ms := multiset s in
  match majority_stack s with
  | NoResult => (0,0)
  | Valid p n => (1,nG-n)
  | Invalid _ =>
    if beq_nat (length (M.support ms)) 3
    then (2,nG - (M.multiplicity (nth 1 (sort (M.support ms)) 0%R)) ms)
    else (3,
          nG -
          (M.multiplicity (extreme_center s) ms
           + M.multiplicity (hd 0%R (sort s)) ms
           + M.multiplicity (last (sort s) 0%R) ms))
  end.

Require Import Inverse_Image.

Let lt_conf x y := lexprod lt lt (conf_to_NxN x) (conf_to_NxN y).

Lemma wf_lt_conf: well_founded lt_conf.
Proof.
  unfold lt_conf.
  apply wf_inverse_image.
  apply wf_lexprod;apply lt_wf.
Qed.

Instance conf_to_NxN_compat: Proper (@PosEq nG 0 ==> eq*eq) conf_to_NxN.
Proof.
  intros pos1 pos2 heq.
  unfold conf_to_NxN at 2.
  functional induction (conf_to_NxN pos1).
  - rewrite <- heq.
    rewrite e.
    reflexivity.
  - rewrite <- heq.
    rewrite e.
    reflexivity.
  - rewrite <- heq, e, <- heq, e0 , <- heq.
    reflexivity.
  - rewrite <- heq, e, <- heq, e0 , <- heq.
    reflexivity.
Qed.

Instance lexprod_compat: Proper (eq*eq ==> eq*eq ==> iff) (lexprod lt lt).
Proof.
  intros (a,b) (a',b') (heqa , heqb) (c,d) (c',d') (heqc , heqd) .
  hnf in *|-.
  simpl in *|-.
  subst.
  reflexivity.
Qed.

Instance lt_conf_compat: Proper (@PosEq nG 0 ==> @PosEq nG 0 ==> iff) lt_conf.
Proof.
  intros pos1 pos1' heq1 pos2 pos2' heq2.
  unfold lt_conf.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Lemma conf_to_NxN_NoResult_spec : forall conf, majority_stack (nominal_spectrum conf) = NoResult->
  conf_to_NxN conf = (0, 0).
Proof.
intros conf Heq. unfold conf_to_NxN. rewrite Heq. reflexivity.
Qed.

Lemma conf_to_NxN_Valid_spec :
  forall conf l n,
    majority_stack (nominal_spectrum conf) = Valid l n ->
    conf_to_NxN conf = (1,(nG - n)).
Proof.
  intros conf l n H.
  unfold conf_to_NxN.
  rewrite H.
  reflexivity.
Qed.

Lemma conf_to_NxN_Three_spec :
  forall conf n,
    majority_stack (nominal_spectrum conf) = Invalid n ->
    (length (M.support (multiset (nominal_spectrum conf)))) = 3 ->
    conf_to_NxN conf = (2, nG - M.multiplicity (nth 1 (sort (M.support (multiset (nominal_spectrum conf)))) 0%R)
                                               (multiset (nominal_spectrum conf))).
Proof.
  intros conf n H H'.
  unfold conf_to_NxN.
  rewrite H, H'.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma conf_to_NxN_Generic_spec :
  forall conf n,
    majority_stack (nominal_spectrum conf) = Invalid n ->
    (length (M.support (multiset (nominal_spectrum conf)))) <> 3 ->
    conf_to_NxN conf = (3,
     nG -
     (M.multiplicity (extreme_center (nominal_spectrum conf)) (multiset (nominal_spectrum conf)) +
      M.multiplicity (hd 0%R (sort (nominal_spectrum conf))) (multiset (nominal_spectrum conf)) +
      M.multiplicity (last (sort (nominal_spectrum conf)) 0%R) (multiset (nominal_spectrum conf)))).
Proof.
  intros conf n H H'.
  unfold conf_to_NxN.
  rewrite <- beq_nat_false_iff in H'.
  rewrite H,H'.
  reflexivity.
Qed.

Lemma multiplicity_le_nG : forall pt conf,
  M.multiplicity pt (multiset (nominal_spectrum conf)) <= nG.
Proof.
intros pt conf. etransitivity.
- apply M.cardinal_lower.
- rewrite cardinal_multiset, nominal_spectrum_length. omega.
Qed.

(* When we only have three towers, the new configuration does not create new positions. *)
Lemma support_round_Three_incl : forall conf da n,
  majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) = 3 ->
  incl (M.support (multiset (nominal_spectrum (lift_gp (@round nG 0 robogram da conf.(gp))))))
       (M.support (multiset (nominal_spectrum conf))).
Proof.
Admitted.

Corollary support_decrease : forall conf da n, majority_stack (nominal_spectrum conf) = Invalid n ->
  length (M.support (multiset (nominal_spectrum conf))) = 3 ->
  length (M.support (multiset (nominal_spectrum (lift_gp (@round nG 0 robogram da conf.(gp)))))) <= 3.
Proof.
intros conf da n Hmaj Hlen. rewrite <- Hlen.
generalize (support_round_Three_incl _ da Hmaj Hlen).
rewrite <- inclA_Leibniz. apply (NoDupA_inclA_length _). apply M.support_NoDupA.
Qed.

Lemma foo : forall (da : demonic_action nG 0) conf,
  ~forbidden conf ->
  (exists gmove, (round robogram da (gp conf) gmove) <> (gp conf) gmove) ->
  lt_conf (lift_gp (round robogram da (gp conf))) conf.
Proof.
  intros da conf Hvalid [gmove Hg].
  assert (Hframe : frame da gmove <> 0%R).
  { apply move_active in Hg. unfold active, Rdec_bool in Hg. rewrite filter_In in Hg.
    destruct Hg as [_ Hg]. destruct (Rdec (frame da gmove) 0); trivial. discriminate Hg. }
  destruct (majority_stack (nominal_spectrum conf)) eqn:Hmaj.
  - apply majority_stack_NoResult_spec in Hmaj.
    assert (h:=nominal_spectrum_length conf).
    rewrite Hmaj in h.
    simpl in h.
    assert (h':=size_G);omega.
  - destruct (Rdec (frame da gmove) 0) eqn:heq; try contradiction.
    assert (exists n',
               majority_stack (nominal_spectrum (lift_gp (round robogram da (gp conf))))
               = Valid l n'
               /\ n' > n).
    { admit. }
    decompose [ex and] H.
    red.
    rewrite (conf_to_NxN_Valid_spec _ H1).
    rewrite (conf_to_NxN_Valid_spec _ Hmaj).
    apply right_lex.
    assert (nG >= x).
    { admit. }
    omega.
  - destruct (eq_nat_dec (length (M.support (multiset (nominal_spectrum conf)))) 3) as [Hlen | Hlen].
    + (* Three towers case *)
      red.
      rewrite (conf_to_NxN_Three_spec _ Hmaj Hlen).
      destruct (majority_stack (nominal_spectrum (lift_gp (round robogram da conf.(gp))))) eqn:Hround.
      * rewrite (conf_to_NxN_NoResult_spec _ Hround). apply left_lex. omega.
      * rewrite (conf_to_NxN_Valid_spec _ Hround). apply left_lex. omega.
      * assert (Hlen' : length (M.support (multiset (nominal_spectrum (lift_gp (round robogram da conf.(gp)))))) = 3).
        { apply le_antisym.
          + apply (support_decrease _ _ Hmaj Hlen).
          + apply (not_forbidden_Invalid_length Hround). now apply never_forbidden. }
        rewrite (conf_to_NxN_Three_spec _ Hround Hlen'). apply right_lex.
        rewrite <- Hlen in Hlen'.
        assert (Hperm : Permutation
                 (M.support (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf))))))
                 (M.support (multiset (nominal_spectrum conf)))).
        { rewrite <- PermutationA_Leibniz. apply (NoDupA_inclA_length_PermutationA _).
          - apply M.support_NoDupA.
          - apply M.support_NoDupA.
          - rewrite inclA_Leibniz. eapply support_round_Three_incl; eassumption.
          - assumption. }
        rewrite Hperm.
        assert (Hup := multiplicity_le_nG (nth 1 (sort (M.support (multiset (nominal_spectrum conf)))) 0%R) 
                                          (lift_gp (round robogram da (gp conf)))).
        cut (M.multiplicity
                (nth 1 (sort (M.support (multiset (nominal_spectrum conf)))) 0%R)
                (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
              >
              M.multiplicity
                (nth 1 (sort (M.support (multiset (nominal_spectrum conf)))) 0%R)
                (multiset (nominal_spectrum conf))). omega.
        unfold gt. rewrite increase_move.
        exists gmove.
        assert (Heqg : round robogram da (gp conf) gmove =
                       nth 1 (sort (M.support (multiset (nominal_spectrum conf)))) 0%R).
        { erewrite round_simplify_Three; try eassumption.
          destruct (Rdec (frame da gmove) 0) as [Habs | _]; trivial.
          apply move_active in Hg. unfold active in Hg. rewrite filter_In, Habs in Hg.
          exfalso. elim Hg. intros _. unfold Rdec_bool. Rdec. discriminate. }
         split; trivial. rewrite <- Heqg. auto.
    + (* Generic case *)
      red. rewrite (conf_to_NxN_Generic_spec _ Hmaj Hlen).
      destruct (majority_stack (nominal_spectrum (lift_gp (round robogram da conf.(gp))))) eqn:Hmaj'.
      * rewrite (conf_to_NxN_NoResult_spec _ Hmaj'). apply left_lex. omega.
      * rewrite (conf_to_NxN_Valid_spec _ Hmaj'). apply left_lex. omega.
      * { destruct (eq_nat_dec (length (M.support (multiset
                     (nominal_spectrum (lift_gp (round robogram da (gp conf))))))) 3) as [Hlen' | Hlen'].
          + rewrite (conf_to_NxN_Three_spec _ Hmaj' Hlen'). apply left_lex. omega.
          + rewrite (conf_to_NxN_Generic_spec _ Hmaj' Hlen'). apply right_lex.
            rewrite (Generic_min_same _ _ Hmaj Hlen), (Generic_max_same _ _ Hmaj Hlen).
            rewrite (Generic_min_mult_same _ _ Hmaj Hlen), (Generic_max_mult_same _ _ Hmaj Hlen).
            rewrite (Generic_extreme_center_same _ _ Hmaj Hlen).
            assert (M.multiplicity (extreme_center (nominal_spectrum conf))
                      (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))
                    + M.multiplicity (hd 0%R (sort (nominal_spectrum conf)))
                        (multiset (nominal_spectrum conf))
                    + M.multiplicity (last (sort (nominal_spectrum conf)) 0%R)
                        (multiset (nominal_spectrum conf))
                    <= nG).
            { admit. }
            cut (M.multiplicity (extreme_center (nominal_spectrum conf))
                     (multiset (nominal_spectrum conf))
                 < M.multiplicity (extreme_center (nominal_spectrum conf))
                   (multiset (nominal_spectrum (lift_gp (round robogram da (gp conf)))))).
            omega.
            rewrite increase_move. exists gmove.
            assert (Heq : round robogram da (gp conf) gmove = extreme_center (nominal_spectrum conf)).
            { admit. }
            split; trivial. rewrite <- Heq. auto. }
Qed.

(*
Lemma gathered_at_PosEq : forall gp pt, gathered_at pt gp -> ExtEq gp (fun _ => pt).
Proof. intros gp pt Hgather. intro n. apply Hgather. Qed.
*)

Lemma gathered_at_Gather : forall pt (d : demon Four Zero) gp, gathered_at gp pt ->
  Gather pt (execute robogram d gp).
Proof.
intro pt. cofix gather. intros d gp Hgather. constructor. apply Hgather.
rewrite execute_tail. apply gather. now apply gathered_at_forever.
Qed.

Theorem stack_gathered_at : forall (da : demonic_action Four Zero) gp pt n, ~forbidden (lift_gp gp) ->
  majority_stack (nominal_spectrum (lift_gp gp)) = Valid pt n ->
  gathered_at (round robogram da gp) pt.
Proof.
intros da gp pt n Hok Hstack g. unfold round.
pose (s := spectrum_of da g ((⟦frame da g, gp g⟧) {| gp := gp; bp := locate_byz da |})). fold s.
destruct (Rdec (frame da g) 0).
  now elim (active da g). (* Stalling case *)
  unfold robogram.
  assert (Hfor : is_forbidden s = false).
  { unfold s. rewrite spectrum_ok. rewrite is_forbidden_false. intro Habs. apply Hok.
    revert Habs. setoid_rewrite lift_gp_equiv at 2. simpl. apply forbidden_similarity_invariant. }
  rewrite Hfor. clear Hfor.
  assert (Hperm : Permutation s (nominal_spectrum (⟦frame da g, gp g⟧ {| gp := gp; bp := locate_byz da |})))
  by apply da.(spectrum_ok).
  rewrite <- is_forbidden_false in Hok. rewrite Hperm. setoid_rewrite lift_gp_equiv at 2.
  simpl. rewrite <- (majority_stack_Valid_similarity (gp g) _ _ _ (active da g)) in Hstack.
  rewrite Hstack. now field.
Qed.

Corollary stack_sol : forall k (d : demon Four Zero), kFair k d ->
  forall gp : Four -> R, ~forbidden (lift_gp gp) ->
  Stack (lift_gp gp) ->
  exists pt, WillGather pt (execute robogram d gp).
Proof.
intros k [da d] Hfair gp Hok Hstack.
assert (Hs := Hstack). rewrite <- majority_stack_spec in Hs. destruct Hs as [pt [n Hpt]].
exists pt. constructor 2. constructor 1.
rewrite execute_tail. cofix gathered. constructor. clear gathered. simpl. now apply stack_gathered_at with n.
(* back to coinduction *)
apply gathered. (* ill-formed recursive definition: we cannot use stack_gathered *)
Admitted.

Theorem meeting4 :
  forall d : demon Four Zero, forall k, kFair k d -> solGathering robogram d.
Proof.
intros d k Hfair gp Hok.
destruct (majority_stack (nominal_spectrum (lift_gp gp))) as [| r n | n] eqn:Hdup.
  (* there is no robot *)
  rewrite majority_stack_NoResult_spec in Hdup. rewrite nominal_spectrum4 in Hdup. discriminate Hdup.
  (* there is a stack *)
  apply (stack_sol Hfair Hok). rewrite <- majority_stack_spec. now exists r; exists n.
  (* there is not stack, it will be created at the next step *)
  inversion_clear Hfair as [_ Htfair].
  destruct (stack_sol Htfair (@never_forbidden (demon_head d) _ Hok)) as [pt Hpt].
    apply Will_stack. assumption. rewrite <- majority_stack_spec.
    intros [x [m Habs]]. rewrite Hdup in Habs. discriminate Habs.
    exists pt. constructor 2. rewrite execute_tail. exact Hpt.
Qed.
Print Assumptions meeting4.

