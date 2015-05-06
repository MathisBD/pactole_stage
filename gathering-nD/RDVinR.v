Require Import Bool.
Require Import Arith.Div2.
Require Import Omega.
Require Import Rbase Rbasic_fun.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import MMultisetFacts MMultisetMap.
Require Import Pactole.Preliminary.
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


Module N : Size with Definition nG := nG with Definition nB := 0.
  Definition nG := nG.
  Definition nB := 0.
End N.


(** The spectrum is a multiset of positions *)
Module Spec := MultisetSpectrum.Make(R)(N).

Notation "s [ pt ]" := (Spec.multiplicity pt s) (at level 1, format "s [ pt ]").
Notation "!!" := Spec.from_config.

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
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

Instance forbidden_invariant : Proper (Pos.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [pt1 [pt2 [Hneq Hpt]]]]; split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

Lemma forbidden_even : forall pos, forbidden pos -> Nat.Even nG.
Proof. now intros pos [? _]. Qed.

Lemma forbidden_support_length : forall config, forbidden config ->
  length (Spec.support (Spec.from_config config)) = 2.
Proof.
intros conf [Heven [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]].
rewrite <- (@Spec.cardinal_total_sub_eq (Spec.add pt2 (Nat.div2 N.nG) (Spec.singleton pt1 (Nat.div2 N.nG)))
                                        (Spec.from_config conf)).
+ rewrite Spec.support_add; try now apply half_size_pos.
  destruct (Spec.In_dec pt2 (Spec.singleton pt1 (Nat.div2 N.nG))) as [Hin | Hin].
  - exfalso. rewrite Spec.In_singleton in Hin.
    destruct Hin. elim Hdiff. rewrite H.
    reflexivity.
  - rewrite Spec.support_singleton; trivial. apply half_size_pos.
+ intro pt. destruct (Rdec pt pt2), (Rdec pt pt1); subst.
  - now elim Hdiff.
  - rewrite Spec.add_spec, Spec.singleton_spec.
    unfold R.eq_dec, Rdef.eq_dec in *.
    do 2 Rdec_full; contradiction || omega.
  - rewrite Spec.add_other, Spec.singleton_spec.
      now unfold R.eq_dec, Rdef.eq_dec in *; Rdec_full; contradiction || omega.
      now unfold R.eq, Rdef.eq; auto.
  - rewrite Spec.add_other, Spec.singleton_spec.
      now unfold R.eq_dec, Rdef.eq_dec in *; Rdec_full; contradiction || omega.
      now unfold R.eq, Rdef.eq; auto.
+ rewrite Spec.cardinal_add, Spec.cardinal_singleton, Spec.cardinal_from_config.
  unfold N.nB.
  replace (Nat.div2 N.nG + Nat.div2 N.nG) with (2 * Nat.div2 N.nG) by lia.
  rewrite <- Nat.double_twice, plus_0_r. symmetry. apply even_double. now rewrite Even.even_equiv.
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

Transparent R.origin.
Transparent Rdef.origin.

(* A similarity in R is described by its ratio and its center. *)
Theorem similarity_in_R_case : forall sim,
  (forall x, sim.(f) x = sim.(ratio) * (x - sim.(center))) \/
  (forall x, sim.(f) x = - sim.(ratio) * (x - sim.(center))).
Proof.
intro sim. assert (Hkpos : 0 <= sim.(ratio)) by apply sim_ratio_pos.
destruct sim as [f k c Hc Hk]. simpl in *. unfold R.origin, Rdef.origin in Hc.
destruct (Rdec k 0) as [Hk0 | Hk0].
* (* if the ratio is 0, the similarity is a constant function. *)
  left. intro x. subst k. rewrite Rmult_0_l.
  rewrite <- R.dist_defined. rewrite <- Hc, Hk at 1. ring.
* assert (Hc1 : f (c + 1) = k \/ f (c + 1) = - k).
  { specialize (Hk (c + 1) c). rewrite Hc in Hk.
    assert (H1 : R.dist (c + 1) c = 1). { replace 1 with (c+1 - c) at 2 by ring. apply Rabs_pos_eq. lra. }
    rewrite H1 in Hk. destruct (dist_case (f (c + 1)) 0) as [Heq | Heq]; rewrite Heq in Hk; lra. }
  destruct Hc1 as [Hc1 | Hc1].
  + left. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - 0) with (k * (x - c)) by ring.
      now rewrite Rabs_mult, (Rabs_pos_eq k Hkpos).
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (k * (x - c) - k) with (k * (x - (c + 1))) by ring.
      now rewrite Rabs_mult, (Rabs_pos_eq k Hkpos).
  + right. intro x. apply (GPS (f c) (f (c + 1))).
    - lra.
    - rewrite Hk, Hc. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - 0) with (- k * (x - c)) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
    - rewrite Hk, Hc1. unfold R.dist, Rdef.dist.
      replace (- k * (x - c) - - k) with (- k * (x - (c + 1))) by ring.
      rewrite Rabs_mult, (Rabs_left (- k)); lra.
Qed.

Corollary similarity_in_R : forall sim, exists k, (k = sim.(ratio) \/ k = - sim.(ratio))
  /\ forall x, sim.(f) x = k * (x - sim.(center)).
Proof. intro sim. destruct (similarity_in_R_case sim); eauto. Qed.

Corollary inverse_similarity_in_R : forall (sim : similarity) k, k <> 0 -> 
  (forall x, sim x = k * (x - sim.(center))) -> forall x, (sim ⁻¹) x = x / k + sim.(center).
Proof. intros sim k Hk Hdirect x. rewrite <- sim.(Inversion), Hdirect. hnf. now field. Qed.

(* Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 99, format "'⟦' k ','  t '⟧'"). *)
Close Scope R_scope.

(** Some simplifications due to having no byzantine robots *)

(** [lift_function f g] lifts two renaming functions, one for good and
    one for bad robots, into a renaming function for any robot. *)
Definition lift_pos (f : Names.G -> R) : (Names.ident -> R) :=
  fun id => match id with
              | Good g => f g
              | Byz b => Fin.case0 (fun _ => R) b
            end.

(* It would be great to have it as a coercion between G → R and Pos.t,
   but I do not know how to make it work. *)

Instance lift_pos_compat : Proper ((eq ==> eq) ==> Pos.eq) lift_pos.
Proof. intros f g Hfg id. hnf. unfold lift_pos. destruct id; try reflexivity. now apply Hfg. Qed.

(** As there is no byzantine robots, a position is caracterized by the locations of good robots only. *)
Lemma lift_pos_equiv : forall pos : Pos.t, Pos.eq pos (lift_pos (fun g => pos (Good g))).
Proof. unfold lift_pos. intros pos [g | b]; hnf. reflexivity. now apply Fin.case0. Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Corollary spec_nil : forall conf, ~Spec.eq (Spec.from_config conf) Spec.empty.
Proof.
intros conf Heq.
unfold Spec.from_config in Heq.
rewrite Spec.multiset_empty in Heq.
assert (Hlgth:= Spec.Pos.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
unfold N.nG in *.
assert (hnG:=size_G).
omega.
Qed.

(* Renommer en Major_stack_at? *)
Definition Stack_at x pos :=
  forall y, x <> y -> ((!! pos)[y] < (!! pos)[x]).

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

Open Scope R_scope.

Coercion is_true : bool >-> Sortclass.

Definition monotonic {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  Proper (RA ==> RB) f \/ Proper (RA --> RB) f.

Lemma similarity_increasing : forall k t, 0 <= k -> Proper (Rleb ==> Rleb) (fun x => k * (x - t)).
Proof. repeat intro. hnf in *. rewrite Rleb_spec in *. apply Rmult_le_compat_l; lra. Qed.

Lemma similarity_decreasing : forall k t, k <= 0 -> Proper (Rleb --> Rleb) (fun x => k * (x - t)).
Proof.
repeat intro. hnf in *. unfold flip in *. rewrite Rleb_spec in *. apply Ropp_le_cancel.
replace (- (k * (y - t))) with ((- k) * (y - t)) by ring.
replace (- (k * (x - t))) with ((- k) * (x - t)) by ring.
apply Rmult_le_compat_l; lra.
Qed.

Corollary similarity_monotonic : forall sim, monotonic Rleb Rleb sim.(f).
Proof.
intro sim. destruct (similarity_in_R_case sim) as [Hinc | Hdec].
+ left. intros x y Hxy. do 2 rewrite Hinc. apply similarity_increasing; trivial. apply sim_ratio_pos.
+ right. intros x y Hxy. do 2 rewrite Hdec. apply similarity_decreasing; trivial.
  assert (Hratio := sim_ratio_pos sim). lra.
Qed.

Lemma similarity_injective : forall sim, sim.(ratio) <> 0 -> injective eq eq sim.
Proof.
intros sim Hk x y. destruct (similarity_in_R sim) as [k [Hk' Hsim]]; setoid_rewrite Hsim.
rewrite local_invert; lra.
Qed.

Lemma similarity_middle : forall (sim : similarity) x y, sim ((x + y) / 2) = (sim x + sim y) / 2.
Proof.
intros sim x y. destruct (similarity_in_R_case sim) as [Hsim | Hsim];
repeat rewrite Hsim; unfold R.t, Rdef.t in *; field.
Qed.

Lemma is_extremal_map_monotonic_invariant : forall f, monotonic Rleb Rleb f -> injective eq eq f ->
  forall x l, is_extremal (f x) (Spec.map f l) = is_extremal x l.
Proof.
intros f Hfmon Hfinj x l. unfold is_extremal.
assert (Hf : Proper (R.eq ==> R.eq) f). { unfold R.eq, Rdef.eq. repeat intro. now subst. }
destruct Hfmon as [Hfinc | Hfdec].
+ repeat Rdec_full; trivial; rewrite Spec.map_injective_support, (sort_map_increasing Hfinc) in *; trivial.
  - rewrite map_hd in Heq. apply Hfinj in Heq. contradiction.
  - rewrite map_last in Heq. apply Hfinj in Heq. contradiction.
  - elim Hneq. rewrite map_hd. now f_equal.
  - elim Hneq0. rewrite map_last. now f_equal.
+ repeat Rdec_full; trivial;rewrite Spec.map_injective_support, (sort_map_decreasing Hfdec) in *; trivial.
  - rewrite hd_rev_last, map_last in Heq. apply Hfinj in Heq. contradiction.
  - rewrite last_rev_hd, map_hd in Heq. apply Hfinj in Heq. contradiction.
  - elim Hneq0. rewrite last_rev_hd, map_hd. now f_equal.
  - elim Hneq. rewrite hd_rev_last, map_last. now f_equal.
Qed.

Corollary is_extremal_similarity_invariant : forall sim pos r, sim.(ratio) <> 0 ->
  is_extremal (sim r) (Spec.map sim (Spec.from_config pos)) = is_extremal r (Spec.from_config pos).
Proof.
intros sim pos r Hk. apply is_extremal_map_monotonic_invariant.
- apply similarity_monotonic.
- now apply similarity_injective.
Qed.

(* When there is no robot (s is empty), the center is 0. *)
Definition extreme_center (s : Spec.t) :=
  (List.hd 0 (sort (Spec.support s)) + List.last (sort (Spec.support s)) 0) / 2.

Instance extreme_center_compat : Proper (Spec.eq ==> eq) extreme_center.
Proof. intros s s' Hs. unfold extreme_center. now rewrite Hs. Qed.

Lemma extreme_center_similarity : forall sim, sim.(ratio) <> 0 ->
  forall s, ~Spec.eq s Spec.empty -> extreme_center (Spec.map sim s) = sim (extreme_center s).
Proof.
intros sim Hk s Hs.
assert (Hsim1 : Proper (R.eq ==> R.eq) sim). { intros x y Hxy. now rewrite Hxy. }
assert (Hsim2 : injective R.eq R.eq sim). { now apply similarity_injective. }
destruct (similarity_monotonic sim) as [Hinc | Hdec].
* unfold extreme_center. rewrite Spec.map_injective_support, (sort_map_increasing Hinc); trivial.
  assert (Hperm := Permuted_sort (Spec.support s)). destruct (sort (Spec.support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- Spec.support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. symmetry. now apply similarity_middle.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
* unfold extreme_center. rewrite Spec.map_injective_support, (sort_map_decreasing Hdec); trivial.
  rewrite last_rev_hd, hd_rev_last.
  assert (Hperm := Permuted_sort (Spec.support s)). destruct (sort (Spec.support s)) as [| x l'].
  + symmetry in Hperm. apply Permutation_nil in Hperm. elim Hs. now rewrite <- Spec.support_nil.
  + clear s Hs Hperm. simpl hd. cut (x :: l' <> nil). generalize (x :: l'). intro l.
    generalize 0. induction l; intros r Hl.
    - now elim Hl.
    - simpl. destruct l.
        simpl. rewrite similarity_middle. field.
        rewrite <- IHl. reflexivity. discriminate.
    - discriminate.
(* Anomaly: error with no safe_id attached: Uncaught exception Stm.Vcs_aux.Expired.. *)
Qed.

Lemma extreme_center_similarity_invariant : forall sim pos, sim.(ratio) <> 0 ->
  extreme_center (Spec.map sim (Spec.from_config pos)) = sim (extreme_center (Spec.from_config pos)).
Proof. intros. apply extreme_center_similarity. assumption. apply spec_nil. Qed.


(** The robogram works as follows:
    1) if there is a majority stack, everyone goes there;
    2) if there are three stacks, everyone goes on the middle one;
    3) otherwise, robots located at non extremal locations go to the middle of the extremal locations.
    The last case will necessarily end into one of the first two, ensuring termination.
**)

(** [Smax_mult s] returns the maximal multiplicity of configutation [s]. *)
Definition Smax_mult s := Spec.fold (fun _ => max) s 0%nat.

Instance Smax_mult_compat : Proper (Spec.eq ==> eq) Smax_mult.
Proof.
unfold Smax_mult. intros s1 s2 Heq. apply Spec.fold_compat; trivial; refine _.
intros _ _ n m p. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
Qed.

Lemma Smax_mult_map_injective_invariant : forall f, injective eq eq f ->
  forall s, Smax_mult (Spec.map f s) = Smax_mult s.
Proof.
intros f Hf. apply Spec.ind.
+ intros s1 s2 Hs. now rewrite Hs.
+ intros s x n Hout Hn Hrec. rewrite Spec.map_add; try now intros ? ? Heq; rewrite Heq.
  assert (Haux : Spec.elt -> Spec.elt ->
            forall n m a : nat, Init.Nat.max m (Init.Nat.max n a) = Init.Nat.max n (Init.Nat.max m a)).
  { intros _ _ n' m' p'. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2. }
  unfold Smax_mult in *. repeat rewrite Spec.fold_add; trivial; refine _;try now (hnf;auto).
  - intro Habs. apply Hout. apply Spec.map_In in Habs.
    * destruct Habs as [y [Heq Hin]].
      apply Hf in Heq; subst; assumption.
    * repeat intro.
      rewrite H0.
      reflexivity.
+ now rewrite Spec.map_empty.
Qed.

Corollary Smax_mult_similarity_invariant : forall sim, sim.(ratio) <> 0 ->
  forall s, Smax_mult (Spec.map sim s) = Smax_mult s.
Proof. intros. now apply Smax_mult_map_injective_invariant, similarity_injective. Qed.

Lemma Smax_mult_spec_aux : forall s x n, (n > 0)%nat -> ~Spec.In x s ->
  Smax_mult (Spec.add x n s) = Nat.max n (Smax_mult s).
Proof.
intros s x n Hn. unfold Smax_mult. apply Spec.fold_add; trivial.
- refine _.
- repeat intro. now subst.
- repeat intro. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
Qed.

Theorem Smax_mult_spec : forall s x, (s[x] <= Smax_mult s)%nat.
Proof.
intro s. pattern s. apply Spec.ind; clear s.
* intros s1 s2 Hs. now setoid_rewrite Hs.
* intros m x n Hout Hn Hrec y. rewrite Smax_mult_spec_aux; trivial.
  assert (Hx : m[x] = 0%nat). { rewrite Spec.not_In in Hout. assumption. }
  destruct (Rdec y x) as [Hxy | Hxy].
  + subst. rewrite Spec.add_spec, Hx. rewrite Spec.eq_refl_left. apply Max.le_max_l.
  + rewrite Spec.add_other; auto. transitivity (Smax_mult m).
    - apply Hrec.
    - apply Max.le_max_r.
* intro x. rewrite Spec.empty_spec. omega.
Qed.

Lemma Smax_mult_0 : forall s, Smax_mult s = 0%nat <-> Spec.eq s Spec.empty.
Proof.
intro s. split; intro Heq.
+ destruct (Spec.empty_or_In_dec s) as [? | [x Hin]]; trivial.
  elim (lt_irrefl 0). apply lt_le_trans with s[x].
  - exact Hin.
  - rewrite <- Heq. apply Smax_mult_spec.
+ rewrite Heq. unfold Smax_mult. now rewrite Spec.fold_empty.
Qed.

(** [Smax s] return the configuration [s] where all non maximal positions
    have been removed. *)
Definition Smax s := Spec.filter (fun _ => beq_nat (Smax_mult s)) s.

Instance Smax_compat : Proper (Spec.eq ==> Spec.eq) Smax.
Proof.
intros s1 s2 Heq. unfold Smax. rewrite Heq. apply Spec.filter_extensionality_compat.
- repeat intro. now subst.
- intros _ n. now rewrite Heq.
Qed.

Lemma Smax_map_injective : forall f, injective eq eq f ->
  forall s, Spec.eq (Smax (Spec.map f s)) (Spec.map f (Smax s)).
Proof.
intros f Hf s. unfold Smax. rewrite Spec.map_injective_filter.
+ apply Spec.map_compat.
  - intros ? ? Heq. now rewrite Heq.
  - apply Spec.filter_extensionality_compat; repeat intro; subst; trivial.
    now rewrite Smax_mult_map_injective_invariant.
+ repeat intro. now subst.
+ intros ? ? Heq. now rewrite Heq.
+ assumption.
Qed.

Corollary Smax_similarity : forall sim, sim.(ratio) <> 0 ->
  forall s, Spec.eq (Smax (Spec.map sim s)) (Spec.map sim (Smax s)).
Proof. intros. now apply Smax_map_injective, similarity_injective. Qed.


Instance eqb_Smax_mult_compat s:
  Proper (R.eq ==> eq ==> eq)
         (fun _ : Spec.elt => Nat.eqb (Smax_mult s)).
Proof.
  repeat intro. now subst.
Qed.

Lemma Smax_subset : forall s x, ((Smax s)[x] <= s[x])%nat.
Proof.
  intros s x.
  unfold Smax.
  setoid_rewrite Spec.filter_spec.
  2: apply eqb_Smax_mult_compat.
  destruct (Smax_mult s =? s[x]);auto.
  omega.
Qed.

Theorem Smax_spec : forall s x y, Spec.In y (Smax s) -> (s[x] <= (Smax s)[y])%nat.
Proof.
intros s x y Hy. unfold Smax in *.
assert (Hf := eqb_Smax_mult_compat s).
unfold Spec.In in Hy. rewrite Spec.filter_spec in *; trivial.
destruct (Smax_mult s =? s[y]) eqn:Heq; try omega.
rewrite Nat.eqb_eq in Heq. rewrite <- Heq. apply Smax_mult_spec.
Qed.

Theorem Smax_spec_2 : forall s x y, (s[x] <= (Smax s)[y])%nat -> Spec.In y (Smax s).
Proof.
  admit.
Admitted.


Close Scope R_scope.

Theorem Smax_spec_non_nil : forall s x, Spec.In x s
                                         -> exists y, Spec.In y (Smax s).
Proof.
  intro s.
  pattern s.
  eapply (Spec.ind).
  { intros m1 m2 Hm1m2.
    setoid_rewrite Hm1m2.
    reflexivity. }
  - intros m x n Hxnotinm hpos HI x' hx'.
    destruct (Spec.empty_or_In_dec m).
    + exists x.
      unfold Smax.
      rewrite Spec.filter_In.
      split.
      * admit.
      * rewrite Nat.eqb_eq.
        rewrite Smax_mult_spec_aux;trivial.
        rewrite e at 2.
        rewrite Spec.M.add_empty.
        rewrite Spec.singleton_spec.
        unfold R.eq_dec,Rdef.eq_dec.
        Rdec.
        rewrite <- Smax_mult_0 in e.
        rewrite e.
        apply Max.max_0_r.
      * apply eqb_Smax_mult_compat.
    + destruct e as [x'' hx''].
      specialize (HI x'' hx'').
      destruct HI as [y hy].
      destruct (le_lt_dec n (m[y])).
      * exists y.
        admit.
      * exists x.
        admit.
  - intros x H.
    admit.
Admitted.


Lemma Smax_empty_1 : forall s,  Spec.eq s Spec.empty -> Spec.eq (Smax s) Spec.empty.
Proof.
  intros s h.
  rewrite h.
  unfold Smax.
  rewrite Spec.filter_empty.
  + reflexivity.
  + intros r1 r2 Hr1r2 x1 x2 hx1x2.
    subst.
    reflexivity.
Qed.

(* BUG HERE *)
Lemma Smax_empty_2 : forall s, Spec.eq (Smax s) Spec.empty -> Spec.eq s Spec.empty.
Proof.
  unfold Spec.eq.
  intros s H.
  destruct (Spec.empty_or_In_dec s).
  - intros x.
    rewrite e.
    reflexivity.
  - destruct e as [x hx].
    destruct (Smax_spec_non_nil hx).
    unfold Spec.In in H0.
    rewrite H in H0.
    admit.
Admitted.

Lemma Smax_empty : forall s, Spec.eq (Smax s) Spec.empty <-> Spec.eq s Spec.empty.
Proof.
  split.
  - apply Smax_empty_2.
  - apply Smax_empty_1.
Qed.

Open Scope R_scope.

Lemma support_Smax_nil : forall config, Spec.support (Smax (!! config)) <> nil.
Proof. intros config Habs. rewrite Spec.support_nil, Smax_empty in Habs. apply (spec_nil _ Habs). Qed.

Definition robogram_pgm (s : Spec.t) : R.t :=
  match Spec.support (Smax s) with
    | nil => 0 (* only happen with no robots *)
    | pt :: nil => pt (* case 1: one majority stack *)
    | _ => (* several majority stacks *)
           if beq_nat (length (Spec.support s)) 3
           then List.nth 1 (sort (Spec.support s)) 0 else
           if is_extremal 0 s then 0 else extreme_center s
  end.
(*
Definition robogram (s : Spec.t) : R.t :=
  match majority_stack s with
    | NoResult => 0 (* there is no robot anyway in this case *)
    | Valid p n => p
    | Invalid n => if beq_nat (length (Spec.support s)) 3
                   then List.nth 1 (sort (Spec.support s)) 0 else
                   if is_extremal 0 s then 0 else extreme_center s end.
*)
Print Assumptions robogram_pgm.

(** The robogram is invariant by permutation of spectra. *)
Instance robogram_pgm_compat : Proper (Spec.eq ==> eq) robogram_pgm.
Proof.
unfold robogram_pgm. intros s s' Hs. assert (Hperm := Spec.support_compat (Smax_compat Hs)).
destruct (Spec.support (Smax s)) as [| pt [| pt2 l]].
+ now rewrite (PermutationA_nil _ Hperm).
+ symmetry in Hperm. destruct (PermutationA_length1 _ Hperm) as [pt' [Heq Hin]]. now rewrite Hin.
+ assert (Hlength := PermutationA_length _ Hperm).
  destruct (Spec.support (Smax s')) as [| pt' [| pt2' l']]; try discriminate. rewrite Hs.
  destruct (length (Spec.support s') =? 3); rewrite Hs; trivial.
  destruct (is_extremal 0 s'); try rewrite Hs; reflexivity.
Qed.

Definition robogram := Build_robogram robogram_pgm robogram_pgm_compat.
Print Assumptions robogram.

(*
Lemma nominal_spectrum_alls : forall pt,
  Spec.eq (Spec.from_config (lift_pos (fun _ => pt))) (Spec.singleton pt nG).
Proof.
intros pt x. rewrite Spec.singleton_spec. rewrite Spec.from_config_spec.
Admitted.

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
*)

Lemma sim_compat (sim:similarity) : Proper (R.eq ==> R.eq) sim.
Proof.
  repeat intro.
  rewrite H.
  reflexivity.
Qed.

Lemma forbidden_similarity_invariant : forall (sim : similarity) pos, forbidden pos -> forbidden (Pos.map sim pos).
Proof.
  unfold forbidden.
  intros sim pos H.
  destruct H as [hnG [pt1 [pt2 [hdiff [hpt1 hpt2]]]]].
  split;trivial.
  exists (sim pt1), (sim pt2).
  split.
  - rewrite (sim.(Inversion)).
    intro abs.
    rewrite <- abs in hdiff.
    rewrite <- (sim.(Inversion)) in hdiff.
    elim hdiff;reflexivity.
  - split.
    all: rewrite <- Spec.from_config_map, Spec.map_spec.
    all: try assumption.
    all: try apply sim_compat.
    + rewrite <- hpt1.
      transitivity (Spec.cardinal
     (Spec.filter
        (fun (y : Spec.elt) (_ : nat) =>
         if Spec.Locations.eq_dec y pt1 then true else false)
        (!! pos))).
      2:now apply Spec.cardinal_filter_is_multiplicity.
      apply Spec.M.cardinal_compat.
      apply Spec.filter_extensionality_compat.
      * repeat intro.
        rewrite H.
        reflexivity.
      * intros x n.
        destruct (Spec.Locations.eq_dec x pt1) as [heq | hneq] ,
                 (Spec.Locations.eq_dec (sim x) (sim pt1)) as [heq' | hneq'];auto.
        -- rewrite heq in hneq'.
           elim hneq'.
           reflexivity.
        -- rewrite (sim.(Inversion)) in heq'.
           rewrite <- heq' in hneq.
           unfold Spec.Locations.eq,Rdef.eq in *.
           rewrite <- (sim.(Inversion)) in hneq.
           elim hneq;reflexivity.
    + rewrite <- hpt2.
      transitivity (Spec.cardinal
     (Spec.filter
        (fun (y : Spec.elt) (_ : nat) =>
         if Spec.Locations.eq_dec y pt2 then true else false)
        (!! pos))).
      2:now apply Spec.cardinal_filter_is_multiplicity.
      apply Spec.M.cardinal_compat.
      apply Spec.filter_extensionality_compat.
      * repeat intro.
        rewrite H.
        reflexivity.
      * intros x n.
        destruct (Spec.Locations.eq_dec x pt2) as [heq | hneq] ,
                 (Spec.Locations.eq_dec (sim x) (sim pt2)) as [heq' | hneq'];auto.
        -- rewrite heq in hneq'.
           elim hneq'.
           reflexivity.
        -- rewrite (sim.(Inversion)) in heq'.
           rewrite <- heq' in hneq.
           unfold Spec.Locations.eq,Rdef.eq in *.
           rewrite <- (sim.(Inversion)) in hneq.
           elim hneq;reflexivity.
Qed.


(* intros [gp bp] k t [p1 [p2 [Hneq Hperm]]]. destruct (Rdec k 0).
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

Corollary forbidden_similarity_iff : forall sim pos, sim.(ratio) <> 0 ->
  (forbidden (Pos.map sim pos) <-> forbidden pos).
Proof.
intros sim pos Hk. split.
+ apply forbidden_similarity_invariant.
+ rewrite <- (similarity_inverse t pos Hk) at 1. apply forbidden_similarity_invariant.
Qed.
*)
Lemma no_majority_support_2_forbidden : forall conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  length (Spec.support (Spec.from_config conf)) = 2%nat <-> forbidden conf.
Proof.
intros conf Hlen. split; intro H2.
* destruct (Spec.support (Spec.from_config conf)) as [| pt1 [| pt2 [| ? ?]]] eqn:Hsupp; try discriminate H2.
  admit.
* now apply forbidden_support_length.
Admitted.

Theorem robogram_homothecy_invariant : forall sim s, sim.(ratio) <> 0 ->
  exists k, (k = sim.(ratio) \/ k = - sim.(ratio))
         /\ robogram (Spec.map sim s) = k * (robogram (Spec.map (fun x => x - sim.(center)) s)).
Proof. Admitted.
(*
intros sim s Hk. unfold Grobogram, robogram_pgm. simpl.
destruct (similarity_in_R sim) as [k [Hcasek Hsim]]. exists k. split; try assumption.
assert (Hperm : PermutationA R.eq (Spec.support (Smax (Spec.map sim s))) (map sim (Spec.support (Smax s)))).
{ rewrite <- Spec.map_support. }
= Smax_similarity sim Hk s).
apply Spec.support_compat in Hperm. rewrite Spec.map_support in Hperm.
* destruct (Spec.support (Smax (Spec.map sim s))) as [| pt [| pt2 l]].
  + simpl in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm. lra.
  + simpl in Hperm. apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Heq]].
    rewrite Heq. unfold R.eq, Rdef.eq in Hy. subst.
    destruct (similarity_in_R sim) as [Hsim | Hsim]; rewrite Hsim.
 rewrite Hperm. lra.
  + assert (Hperm := Smax_similarity sim Hk s). apply Spec.support_compat in Hperm.
  rewrite Spec.map_support, Hs in Hperm.
  - simpl in Hperm. symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm. lra.
  - intros ? ? Heq. now rewrite Heq.
  - now apply similarity_injective.
rewrite (Smax_similarity _ Hk).
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
  assert (Hlen : length (Spec.support (M.map (fun x : R => k * (x - t)) (multiset (nominal_spectrum pos))))
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
*)

(** **  General simplification lemmas for [round robogram da _] **)

Lemma round_simplify : forall da pos,
  Pos.eq (round robogram da pos)
         (fun id => match da.(step) id with
                      | None => pos id
                      | Some f =>
                          let s := Spec.from_config pos in
                          match Spec.support (Smax s) with
                            | nil => pos id (* only happen with no robots *)
                            | pt :: nil => pt (* case 1: one majority stack *)
                            | _ => (* several majority stacks *)
                                   if beq_nat (length (Spec.support s)) 3
                                   then List.nth 1 (sort (Spec.support s)) 0 else
                                   if is_extremal (pos id) s then (pos id) else extreme_center s
                          end
                    end).
Proof.
intros da pos id. unfold round.
destruct (step da id) as [simc |] eqn:Hstep, id as [g | b]; try reflexivity || now eapply Fin.case0; exact b.
remember (pos (Good g)) as pt.
(* Simplify the similarity *)
assert (Hratio : (simc pt).(ratio) <> 0). { eapply da.(step_ratio). eassumption. }
destruct (similarity_in_R (simc pt)) as [k [Hk Hsim]].
assert (Hinvsim : forall x, (simc pt ⁻¹) x = x / k + center (simc pt)).
{ apply inverse_similarity_in_R; trivial. destruct Hk; lra. }
rewrite Hinvsim.
assert(Hsimccompat : Proper (R.eq ==> R.eq) (simc pt)). { intros ? ? Heq. now rewrite Heq. }
assert (Hsim_inj : injective R.eq R.eq (simc pt)) by now apply similarity_injective.
(* Unfold the robogram *)
unfold robogram, robogram_pgm. simpl.
assert (Hperm : PermutationA R.eq (Spec.support (Smax (Spec.from_config (Pos.map (simc pt) pos))))
                                  (List.map (simc pt) (Spec.support (Smax (Spec.from_config pos))))).
{ rewrite <- Spec.map_support; trivial. f_equiv.
  rewrite <- Smax_similarity, Spec.from_config_map; auto. reflexivity. }
destruct (Spec.support (Smax (Spec.from_config pos))) as [| pt' [| pt2' l']].
* (* Empty support *)
  simpl in Hperm. symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm.
  rewrite da.(step_center); try eassumption. hnf. field. lra.
* (* A majority stack *)
  simpl in Hperm. apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]]. rewrite Hperm.
  hnf in Hy |- *. subst y. rewrite Hsim. field. lra.
* (* No majority stack *)
  apply (PermutationA_length _) in Hperm.
  destruct (Spec.support (Smax (Spec.from_config (Pos.map (simc pt) pos)))) as [| pt'' [| pt2'' l'']];
  try discriminate Hperm. clear Hperm pt' pt2' l' pt'' pt2'' l''.
  assert (Hlength : length (Spec.support (Spec.from_config (Pos.map (simc pt) pos)))
          = length (Spec.support (Spec.from_config pos))).
  { now rewrite <- Spec.from_config_map, Spec.map_support, map_length. }
  rewrite Hlength. destruct (length (Spec.support (Spec.from_config pos)) =? 3) eqn:Hlen.
  + (* There are three towers *)
    rewrite <- Spec.from_config_map, Spec.map_support; trivial.
    destruct (Spec.support (Spec.from_config pos)) as [| pt1 [| pt2 [| pt3 [| ? ?]]]]; try discriminate Hlen.
    destruct (similarity_monotonic (simc pt)) as [Hinc | Hdec].
    - rewrite (sort_map_increasing Hinc), (nth_indep _ 0 (simc pt 0)),
              map_nth, <- Hinvsim, <- (simc pt).(Inversion); try reflexivity.
      rewrite map_length, <- Permuted_sort. simpl. omega.
    - { rewrite (sort_map_decreasing Hdec).
        assert (Heq1 : Nat.div2 (length (map (simc pt) (sort (pt1 :: pt2 :: pt3 :: nil)))) = 1%nat).
        { now rewrite map_length, <- Permuted_sort. }
        rewrite <- Heq1 at 1. rewrite odd_middle, (nth_indep _ 0 (simc pt 0)).
        + rewrite map_nth, <- Hinvsim, <- (simc pt).(Inversion), <- Heq1; reflexivity.
        + rewrite map_length, <- Permuted_sort. simpl. omega.
        + rewrite map_length, <- Permuted_sort. simpl. exists 1%nat. omega. }
  + (* Generic case *)
    SearchAbout is_extremal.
    change 0 with R.origin. rewrite <- (simc pt).(center_prop) at 1.
    rewrite <- Spec.from_config_map, is_extremal_similarity_invariant, da.(step_center); try eassumption.
    destruct (is_extremal pt (Spec.from_config pos)).
    - (* The current robot is exremal *)
      hnf. unfold R.origin, Rdef.origin. field. lra.
    - (* The current robot is not exremal *)
      rewrite <- Spec.from_config_map, extreme_center_similarity; apply spec_nil || trivial.
      hnf. rewrite <- (da.(step_center) _ _ pt Hstep) at 2. now rewrite <- Hinvsim, <- (simc pt).(Inversion).
Qed.
Print Assumptions round_simplify.

(** ***  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majotiy tower, everyone goes there. **)
Lemma round_simplify_Majority : forall da conf pt,
  Spec.support (Smax (Spec.from_config conf)) = pt :: nil ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => pt
                    end).
Proof.
intros da conf pt Hmaj id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
destruct (Spec.support (Smax (Spec.from_config conf))) as [| ? [| ? ?]]; try discriminate Hmaj.
inversion Hmaj. reflexivity.
Qed.

(** If we have three towers, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config conf)) = 3)%nat ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => nth 1 (sort (Spec.support (Spec.from_config  conf))) 0
                    end).
Proof.
intros da pos Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
destruct (Spec.support (Smax (Spec.from_config pos))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in H3. rewrite H3. reflexivity.
Qed.

(* In the general case, all non extremal robots goes to hte middle of the extreme. *)
Lemma round_simplify_Generic : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config conf)) <> 3)%nat ->
  Pos.eq (round robogram da conf)
         (fun id => match step da id with
                      | None => conf id
                      | Some _ => if is_extremal (conf id) (Spec.from_config conf)
                                  then conf id else extreme_center (Spec.from_config conf)
                    end).
Proof.
intros da pos Hmaj H3 id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta.
destruct (Spec.support (Smax (Spec.from_config pos))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in H3. rewrite H3. reflexivity.
Qed.

Close Scope R_scope.

(*
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
*)

(** ** Simplification of the global position in the three cases of the robogram **)
(*
(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Majority_grow :  forall pt config da,
  Spec.support (Smax (!! config)) = pt :: nil -> 
  (!! config)[pt] <= (!! (round robogram da config))[pt].
Proof.
intros pt pos da Hmaj.
(* we first simplify the rhs *)
rewrite (round_simplify_Majority _ _ Hmaj).

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
*)

Lemma nominal_spectrum_3_stacks : forall s,
    (length (Spec.support s) >= 3)%nat <->
    exists pt1 pt2 pt3, pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3
                     /\ Spec.In pt1 s /\ Spec.In pt2 s /\ Spec.In pt3 s.
Proof. Admitted.
(*
intro s. split; intro H.
- assert (Hl : exists pt1 pt2 pt3 l, M.support (multiset (nominal_spectrum pos)) =  pt1 :: pt2 :: pt3 :: l).
  { destruct (M.support (multiset (nominal_spectrum pos))) as [| a [| b [| c [| d l]]]];
    inversion H; try (exfalso;omega).
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
*)
(*
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
*)

Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

(*
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
*)

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


(** If we have no majority stack (hence more than one stack), then the extreme locations are different. **)
Lemma Generic_min_max_diff_aux : forall l, (length l > 1)%nat -> NoDupA eq l ->
  hd 0%R (sort l) <> last (sort l) 0%R.
Proof.
intros l Hl Hnodup. rewrite Permuted_sort in Hl.
apply (@PermutationA_NoDupA _ eq _ l (sort l)) in Hnodup.
- apply (hd_last_diff _); auto.
- rewrite PermutationA_Leibniz. apply Permuted_sort.
Qed.

Lemma Generic_min_max_diff : forall config,
  (length (Spec.support (Smax (Spec.from_config config))) > 1)%nat ->
  hd 0%R (sort (Spec.support (!! config))) <> last (sort (Spec.support (!! config))) 0%R.
Proof.
intros config Hmaj. apply Generic_min_max_diff_aux.
+ apply lt_le_trans with (length (Spec.support (Smax (Spec.from_config config)))); trivial.
  apply (NoDupA_inclA_length _).
  - apply Spec.support_NoDupA.
  - apply Spec.support_filter. repeat intro. now subst.
+ apply Spec.support_NoDupA.
Qed.

Corollary Generic_min_mid_diff : forall config,
  (length (Spec.support (Smax (Spec.from_config config))) > 1)%nat ->
  hd 0%R (sort (Spec.support (!! config))) <> extreme_center (!! config).
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_diff in H. lra. Qed.

Corollary Generic_mid_max_diff : forall config,
  (length (Spec.support (Smax (Spec.from_config config))) > 1)%nat ->
  extreme_center (!! config) <> last (sort (Spec.support (!! config))) 0%R.
Proof. intros ? H. unfold extreme_center. apply Generic_min_max_diff in H. lra. Qed.

Theorem Generic_min_same : forall da conf,
  (length (Spec.support (Smax (!! conf))) > 1)%nat ->
  (length (Spec.support (!! conf)) <> 3)%nat ->
    hd 0%R (sort (Spec.support (!! (round robogram da conf))))
    = hd 0%R (sort (Spec.support (!! conf))).
Proof.
Admitted.

Theorem Generic_max_same : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config  conf)) <> 3)%nat ->
    last (sort (Spec.support (Spec.from_config (round robogram da conf)))) 0%R
    = last (sort (Spec.support (Spec.from_config conf))) 0%R.
Proof.
Admitted.


Corollary Generic_extreme_center_same : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config  conf)) <> 3)%nat ->
  extreme_center (Spec.from_config (round robogram da conf))
  = extreme_center (Spec.from_config conf).
Proof.
intros da conf Hmaj Hlen. unfold extreme_center.
now rewrite (Generic_min_same _ _ Hmaj Hlen), (Generic_max_same _ _ Hmaj Hlen).
Qed.

Theorem Generic_min_mult_same : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config  conf)) <> 3)%nat ->
  Spec.multiplicity
    (hd 0%R (sort (Spec.support (Spec.from_config conf))))
    (Spec.from_config (round robogram da conf))
  = Spec.multiplicity
    (hd 0%R (sort (Spec.support (Spec.from_config conf))))
    (Spec.from_config conf).
Proof. Admitted.
(*
intros da conf Hmaj Hlen.
remember (hd 0%R (sort (Spec.support (Spec.from_config conf)))) as pt.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in Hlen.
rewrite round_simplify. , Hmaj, Hlen, multiset_app, M.union_spec.
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
*)

Theorem Generic_max_mult_same : forall da conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  (length (Spec.support (Spec.from_config  conf)) <> 3)%nat ->
  Spec.multiplicity
    (last (sort (Spec.support (Spec.from_config conf))) 0%R)
    (Spec.from_config (round robogram da conf))
  = Spec.multiplicity
    (last (sort (Spec.support (Spec.from_config conf))) 0%R)
    (Spec.from_config conf).
Proof.
Admitted.

(*
Theorem Stack_at_meeting : forall pos pt (d : demon nG 0) k,
  kFair k d -> Stack_at pt pos -> WillGather pt (execute robogram d (gp pos)).
Proof.
Admitted.

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
*)

(*
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
*)
(* Other proof for never_forbidden *)

Theorem same_destination : forall da config id1 id2,
  In id1 (moving robogram da config) -> In id2 (moving robogram da config) ->
  round robogram da config id1 = round robogram da config id2.
Proof.
intros da config id1 id2 Hid1 Hid2. do 2 rewrite round_simplify.
destruct (step da id1) eqn:Hmove1; [destruct (step da id2) eqn:Hmove2 |].
* (* the real case *)
  cbv zeta.
  destruct (Spec.support (Smax (!! config))) as [| pt [| ? ?]] eqn:Hmaj.
  + (* no robots *)
    rewrite Spec.support_nil, Smax_empty in Hmaj. elim (spec_nil _ Hmaj).
  + (* a majority tower *)
    reflexivity.
  + destruct (length (Spec.support (!! config)) =? 3) eqn:Hlen.
    - (* three towers *)
      reflexivity.
    - { (* generic case *)
        rewrite Nat.eqb_neq in Hlen. rename Hmaj into Hmaj'.
        assert (Hmaj : length (Spec.support (Smax (!! config))) > 1).
        { rewrite Hmaj'. simpl. omega. } clear Hmaj'.
        destruct (is_extremal (config id1) (!! config)) eqn:Hextreme1.
        + exfalso. unfold moving in Hid1. rewrite filter_In in Hid1. destruct Hid1 as [_ Hid1].
          destruct (R.eq_dec (round robogram da config id1) (config id1)) as [_ | Hneq]; try discriminate.
          apply Hneq. rewrite round_simplify_Generic; trivial.
          destruct (step da id1); try reflexivity. now rewrite Hextreme1.
        + destruct (is_extremal (config id2) (!! config)) eqn:Hextreme2.
          - exfalso. unfold moving in Hid2. rewrite filter_In in Hid2. destruct Hid2 as [_ Hid2].
            destruct (R.eq_dec (round robogram da config id2) (config id2)) as [_ | Hneq]; try discriminate.
            apply Hneq. rewrite round_simplify_Generic; trivial.
            destruct (step da id2); try reflexivity. now rewrite Hextreme2.
          - reflexivity. }
* apply moving_active in Hid2. unfold active in Hid2.
  rewrite filter_In, Hmove2 in Hid2. destruct Hid2; discriminate.
* apply moving_active in Hid1. unfold active in Hid1.
  rewrite filter_In, Hmove1 in Hid1. destruct Hid1; discriminate.
Qed.

Lemma no_active_same_conf :
  forall da conf, active da = nil -> Pos.eq (round robogram da conf) conf.
Proof.
intros da conf Hactive. setoid_rewrite lift_pos_equiv. apply lift_pos_compat.
intros g' g ?. subst g'. rewrite round_simplify.
destruct (step da (Good g)) eqn:Heq; trivial.
assert (Hin : In (Good g) (active da)).
{ unfold active. rewrite filter_In. split.
  - apply Names.In_names.
  - now rewrite Heq. }
rewrite Hactive in Hin. elim Hin.
Qed.

(* TODO *)
Lemma nominal_spectrum_3_stacks_beaucoup_mieux:
  forall pos,
    (length (Spec.support (!! pos)) >= 3)%nat ->
    exists (pt1 pt2 pt3 : R) l,
      pt1 <> pt2 /\
      pt2 <> pt3 /\
      pt1 <> pt3 /\
      Permutation (Spec.support (!! pos)) (pt1::pt2::pt3::l).
Proof.
(*  intros pos H.
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
    apply Permutation_middle. *)
Admitted.


Corollary nominal_spectrum_3_stacks_beaucoup_mieux_mieux:
  forall pos pt3,
    (length (Spec.support (!! pos)) >= 3)%nat ->
    Spec.In pt3 (!! pos) ->
    exists (pt1 pt2 : R) l,
        pt1 <> pt2 /\
        pt2 <> pt3 /\
        pt1 <> pt3 /\
      Permutation (Spec.support (!! pos)) (pt1::pt2::l).
Proof.
(*  intros pos pt3 H H0.
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
    eapply perm_swap. *)
Admitted.

Lemma increase_move1 :
  forall r conf da pt,
    ((Spec.from_config conf)[pt] < (Spec.from_config (round r da conf))[pt])%nat ->
    exists id, round r da conf id = pt /\ round r da conf id <> conf id.
Proof.
  intros r conf da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (Rdec_bool ((round r da conf x))  pt)
                             (negb (Rdec_bool (conf x) pt)))) Names.names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id.
    rewrite andb_true_iff, negb_true_iff, Rdec_bool_true_iff, Rdec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, round r da conf id <> pt \/ conf id = pt).
    { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- Rdec_bool_false_iff, <- Rdec_bool_true_iff. apply Hex, Names.In_names. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt. SearchAbout Spec.filter.
Admitted.

Lemma increase_move :
  forall r conf da pt,
    ((Spec.from_config conf)[pt] < (Spec.from_config (round r da conf))[pt])%nat <->
    exists id, round r da conf id = pt /\ round r da conf id <> conf id.
Proof. Admitted.

Lemma not_forbidden_not_majority_length : forall conf,
  (length (Spec.support (Smax (Spec.from_config conf))) > 1)%nat ->
  ~forbidden conf -> (length (Spec.support (Spec.from_config conf)) >= 3)%nat.
Proof.
intros conf H1 H2.
assert (length (Spec.support (Spec.from_config conf)) > 1)%nat.
{ unfold gt. eapply lt_le_trans; try eassumption. apply (NoDupA_inclA_length _).
  - apply Spec.support_NoDupA.
  - unfold Smax. apply Spec.support_filter. repeat intro. now subst. }
 destruct (length (Spec.support (Spec.from_config conf))) as [| [| [| ?]]] eqn:Hlen; try omega.
exfalso. apply H2. now apply no_majority_support_2_forbidden.
Qed.

(* Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_forbidden : forall da conf, ~forbidden conf -> ~forbidden (round robogram da conf).
Proof.
intros da conf Hok.
(* Three cases for the robogram *)
destruct (Spec.support (Smax (Spec.from_config conf))) as [| pt [| ? ?]] eqn:Hmaj.
* (* Absurd case: no robot *)
  intros _. apply (support_Smax_nil _ Hmaj).
* (* There is a majority tower *)
  apply Stack_at_forbidden with l. apply Stack_at_forever. rewrite <- majority_stack_spec. now exists n. }
(* A robot has moved otherwise we have the same configuration before and it is forbidden. *)
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

Definition conf_to_NxN conf :=
  let s := Spec.from_config conf in
  match Spec.support (Smax s) with
    | nil => (0,0)
    | pt :: nil => (1, N.nG - s[pt])
    | _ :: _ :: _ =>
        if beq_nat (length (Spec.support s)) 3
        then (2, N.nG - s[nth 1 (sort (Spec.support s)) 0%R])
        else (3, N.nG - (s[extreme_center s]
                         + s[hd 0%R (sort  (Spec.support s))]
                         + s[last (sort  (Spec.support s)) 0%R]))
  end.

Require Import Inverse_Image.

Let lt_conf x y := lexprod lt lt (conf_to_NxN x) (conf_to_NxN y).

Lemma wf_lt_conf: well_founded lt_conf.
Proof.
  unfold lt_conf.
  apply wf_inverse_image.
  apply wf_lexprod;apply lt_wf.
Qed.

Instance conf_to_NxN_compat: Proper (Pos.eq ==> eq*eq) conf_to_NxN.
Proof.
intros pos1 pos2 Heq. unfold conf_to_NxN.
assert (Hperm : PermutationA R.eq (Spec.support (Smax (Spec.from_config pos1)))
                                  (Spec.support (Smax (Spec.from_config pos2)))) by now rewrite Heq.
destruct (Spec.support (Smax (Spec.from_config pos2))) as [| pt [| ? ?]] eqn:Hsupp.
+ symmetry in Hperm. apply (PermutationA_nil _) in Hperm. rewrite Hperm. reflexivity.
+ apply (PermutationA_length1 _) in Hperm. destruct Hperm as [y [Hy Hperm]].
  rewrite Hperm, <- Hy, Heq. reflexivity.
+ apply (PermutationA_length _) in Hperm.
  destruct (Spec.support (Smax (Spec.from_config pos1))) as [| ? [| ? ?]]; try discriminate Hperm.
  rewrite Heq. destruct (length (Spec.support (Spec.from_config pos2)) =? 3); rewrite Heq; reflexivity.
Qed.

Instance lexprod_compat: Proper (eq*eq ==> eq*eq ==> iff) (lexprod lt lt).
Proof.
  intros (a,b) (a',b') (heqa , heqb) (c,d) (c',d') (heqc , heqd) .
  hnf in *|-.
  simpl in *|-.
  subst.
  reflexivity.
Qed.

Instance lt_conf_compat: Proper (Pos.eq ==> Pos.eq ==> iff) lt_conf.
Proof.
  intros pos1 pos1' heq1 pos2 pos2' heq2.
  unfold lt_conf.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

Lemma conf_to_NxN_nil_spec : forall conf,
  Spec.support (Smax (Spec.from_config conf)) = nil -> conf_to_NxN conf = (0, 0).
Proof. intros conf Heq. unfold conf_to_NxN. rewrite Heq. reflexivity. Qed.
Locate "_ [ _ ]".
Lemma conf_to_NxN_Majority_spec : forall conf pt,
  Spec.support (Smax (Spec.from_config conf)) = pt :: nil ->
  conf_to_NxN conf = (1, N.nG - (Spec.from_config conf)[pt]).
Proof.
  intros conf pt H.
  unfold conf_to_NxN.
  rewrite H.
  reflexivity.
Qed.

Lemma conf_to_NxN_Three_spec : forall conf,
  length (Spec.support (Smax (Spec.from_config conf))) > 1 ->
  length (Spec.support (Spec.from_config  conf)) = 3 ->
  conf_to_NxN conf = (2, N.nG - (Spec.from_config conf)[nth 1 (sort (Spec.support (Spec.from_config conf))) 0%R]).
Proof.
intros conf Hmaj Hlen. unfold conf_to_NxN.
destruct (Spec.support (Smax (Spec.from_config conf))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_eq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma conf_to_NxN_Generic_spec : forall conf,
  length (Spec.support (Smax (Spec.from_config conf))) > 1 ->
  length (Spec.support (Spec.from_config  conf)) <> 3 ->
    conf_to_NxN conf = 
    (3, N.nG - ((Spec.from_config conf)[extreme_center (Spec.from_config conf)]
                + (Spec.from_config conf)[hd 0%R (sort (Spec.support (Spec.from_config conf)))]
                + (Spec.from_config conf)[last (sort (Spec.support (Spec.from_config conf))) 0%R])).
Proof.
intros conf Hmaj Hlen. unfold conf_to_NxN.
destruct (Spec.support (Smax (Spec.from_config conf))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
rewrite <- Nat.eqb_neq in Hlen. rewrite Hlen. reflexivity.
Qed.

Lemma multiplicity_le_nG : forall pt conf, (Spec.from_config conf)[pt] <= N.nG.
Proof.
intros pt conf. etransitivity.
- apply Spec.cardinal_lower.
- rewrite Spec.cardinal_from_config. unfold N.nB. omega.
Qed.

(* When we only have three towers, the new configuration does not create new positions. *)
Lemma support_round_Three_incl : forall conf da,
  length (Spec.support (Smax (Spec.from_config conf))) > 1 ->
  length (Spec.support (Spec.from_config  conf)) = 3 ->
  incl (Spec.support (Spec.from_config (round robogram da conf)))
       (Spec.support (Spec.from_config conf)).
Proof.
Admitted.

Corollary support_decrease : forall conf da,
  length (Spec.support (Smax (Spec.from_config conf))) > 1 ->
  length (Spec.support (Spec.from_config  conf)) = 3 ->
  length (Spec.support (Spec.from_config (round robogram da conf))) <= 3.
Proof.
intros conf da Hmaj Hlen. rewrite <- Hlen.
generalize (support_round_Three_incl _ da Hmaj Hlen).
rewrite <- inclA_Leibniz. apply (NoDupA_inclA_length _). apply Spec.support_NoDupA.
Qed.

Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= N.nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace N.nG with (N.nG + N.nB) by (unfold N.nB; omega).
rewrite <- (Spec.cardinal_from_config config).
rewrite <- (@Spec.add_remove_id _ pt1 (!! config) (reflexivity _)) at 4.
rewrite Spec.cardinal_add.
rewrite <- (@Spec.add_remove_id _ pt2 (!! config) (reflexivity _)) at 6.
rewrite Spec.remove_add_comm, Spec.cardinal_add; trivial.
rewrite <- (@Spec.add_remove_id _ pt3 (!! config) (reflexivity _)) at 8.
rewrite Spec.remove_add_comm, Spec.remove_add_comm, Spec.cardinal_add; trivial.
omega.
Qed.

Theorem round_lt_conf : forall da conf,
  ~forbidden conf -> moving robogram da conf <> nil ->
  lt_conf (round robogram da conf) conf.
Proof.
intros da conf Hvalid Hmove.
apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
assert (Hstep : step da gmove <> None).
{ apply moving_active in Hmove. now rewrite active_spec in Hmove. }
rewrite moving_spec in Hmove.
destruct (Spec.support (Smax (Spec.from_config conf))) as [| pt [| ? ?]] eqn:Hmaj.
* (* No robots *)
  elim (support_Smax_nil _ Hmaj).
* (* A majority tower *)
  assert (Hmaj' : Spec.support (Smax (Spec.from_config (round robogram da conf))) = pt :: nil).
  { admit. }
  red.
  rewrite (conf_to_NxN_Majority_spec _ Hmaj), (conf_to_NxN_Majority_spec _ Hmaj').
  apply right_lex.
  assert ((Spec.from_config (round robogram da conf))[pt] <= N.nG) by apply multiplicity_le_nG.
  cut ((Spec.from_config conf)[pt] < (Spec.from_config (round robogram da conf))[pt]). omega.
  admit.
* rename Hmaj into Hmaj'.
  assert (Hmaj : length (Spec.support (Smax (Spec.from_config conf))) > 1).
  { rewrite Hmaj'. simpl. omega. } clear Hmaj'.
  destruct (eq_nat_dec (length (Spec.support (Spec.from_config conf))) 3) as [Hlen | Hlen].
  + (* Three towers case *)
    red. rewrite (conf_to_NxN_Three_spec _ Hmaj Hlen).
    destruct (Spec.support (Smax (Spec.from_config (round robogram da conf)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (conf_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite (conf_to_NxN_Majority_spec _ Hmaj'). apply left_lex. omega.
    - rename Hmaj' into Hmaj''.
      assert (Hmaj' : length (Spec.support (Smax (Spec.from_config (round robogram da conf)))) > 1).
      { rewrite Hmaj''. simpl. omega. } clear Hmaj''.
      assert (Hlen' : length (Spec.support (Spec.from_config (round robogram da conf))) = 3).
      { apply le_antisym.
        + apply (support_decrease _ _ Hmaj Hlen).
        + apply (not_forbidden_not_majority_length Hmaj'). now apply never_forbidden. }
      rewrite (conf_to_NxN_Three_spec _ Hmaj' Hlen'). apply right_lex.
      rewrite <- Hlen in Hlen'.
      assert (Hperm : Permutation (Spec.support (Spec.from_config (round robogram da conf)))
                                  (Spec.support (Spec.from_config conf))).
      { rewrite <- PermutationA_Leibniz. apply (NoDupA_inclA_length_PermutationA _).
        - apply Spec.support_NoDupA.
        - apply Spec.support_NoDupA.
        - rewrite inclA_Leibniz. eapply support_round_Three_incl; eassumption.
        - assumption. }
      rewrite Hperm.
      assert (Hup := multiplicity_le_nG (nth 1 (sort (Spec.support (Spec.from_config conf))) 0%R)
                                        (round robogram da conf)).
      cut (Spec.multiplicity
              (nth 1 (sort (Spec.support (Spec.from_config conf))) 0%R)
              (Spec.from_config (round robogram da conf))
            >
            Spec.multiplicity
              (nth 1 (sort (Spec.support (Spec.from_config conf))) 0%R)
              (Spec.from_config conf)). omega.
      unfold gt. rewrite increase_move.
      exists gmove. split; trivial.
      erewrite round_simplify_Three; try eassumption.
      destruct (step da gmove) as [Habs | _]; try now elim Hstep.
      destruct gmove eqn:Hid; trivial.
  + (* Generic case *)
    red. rewrite (conf_to_NxN_Generic_spec _ Hmaj Hlen).
    destruct (Spec.support (Smax (Spec.from_config (round robogram da conf)))) as [| pt' [| ? ?]] eqn:Hmaj'.
    - rewrite (conf_to_NxN_nil_spec _ Hmaj'). apply left_lex. omega.
    - rewrite (conf_to_NxN_Majority_spec _ Hmaj'). apply left_lex. omega.
    - { rename Hmaj' into Hmaj''.
        assert (Hmaj' : length (Spec.support (Smax (Spec.from_config (round robogram da conf)))) > 1).
        { rewrite Hmaj''. simpl. omega. } clear Hmaj''.
        destruct (eq_nat_dec (length (Spec.support (Spec.from_config (round robogram da conf)))) 3)
        as [Hlen' | Hlen'].
        + rewrite (conf_to_NxN_Three_spec _ Hmaj' Hlen'). apply left_lex. omega.
        + rewrite (conf_to_NxN_Generic_spec _ Hmaj' Hlen'). apply right_lex.
          rewrite (Generic_min_same _ _ Hmaj Hlen), (Generic_max_same _ _ Hmaj Hlen).
          rewrite (Generic_min_mult_same _ _ Hmaj Hlen), (Generic_max_mult_same _ _ Hmaj Hlen).
          rewrite (Generic_extreme_center_same _ _ Hmaj Hlen).
          assert ((!! (round robogram da conf))[extreme_center (!! conf)]
                  + (!! conf)[hd 0%R (sort (Spec.support (!! conf)))]
                  + (!! conf)[last (sort (Spec.support (!! conf))) 0%R]
                  <= N.nG).
          { rewrite <- (Generic_min_mult_same da),  <- (Generic_max_mult_same da); trivial.
            apply sum3_le_total.
            - apply Generic_min_mid_diff in Hmaj. lra.
            - apply Generic_min_max_diff in Hmaj. lra.
            - apply Generic_mid_max_diff in Hmaj. lra. }
          cut ((!! conf)[extreme_center (!! conf)] < (!! (round robogram da conf))[extreme_center (!! conf)]).
          omega.
          rewrite increase_move. exists gmove. split; trivial.
          admit.
Admitted.

(** Given a k-fair demon, a non-gathered position, then some robot will move some day *)


Theorem Gathering_in_R :
  forall d k, kFair k d -> solGathering robogram d.
Proof.
intros d k Hfair conf. revert d k Hfair. pattern conf.
apply (well_founded_ind wf_lt_conf). clear conf.
intros conf Hind d k Hfair Hok.
destruct (Hind (round robogram (demon_head d) conf)) with (demon_tail d) k as [pt Hpt].
+ apply round_lt_conf. assumption.
  remember (demon_head d) as da. admit.
+ now inversion_clear Hfair.
+ now apply never_forbidden.
+ exists pt. apply Later. rewrite execute_tail. apply Hpt.
Qed.
Print Assumptions Gathering_in_R.

