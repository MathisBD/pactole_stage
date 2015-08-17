Require Import Utf8.
Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.GatheringinR.Definitions.


Set Implicit Arguments.


Parameter nB: nat.
Axiom nB_non_0 : nB <> 0.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := 2 * nB with Definition nB := nB.
  Definition nG := 2 * nB.
  Definition nB := nB.
End N.


(** The spectrum is a multiset of positions *)
Module Spect := MultisetSpectrum.Make(R)(N).
Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).

Add Search Blacklist "Spect.M" "Ring".
Hint Extern 0 (1 <> 0)%R => apply R1_neq_R0.
Hint Extern 0 (0 <> 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (_ <> _) => match goal with | H : ?x <> ?y |- ?y <> ?x => intro; apply H; now symmetry end.
Hint Extern 0 (~R.eq 1 0)%R => apply R1_neq_R0.
Hint Extern 0 (~R.eq 0 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (~R.eq _ _) => match goal with | H : ~R.eq ?x ?y |- ~R.eq ?y ?x => intro; apply H; now symmetry end.


Module Export Common := CommonRealFormalism.Make(R)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(R)(N)(Spect)(Common).

Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.
Close Scope R_scope.


Lemma nG_nB : N.nG = 2 * N.nB.
Proof. reflexivity. Qed.

Corollary even_nG : Nat.Even N.nG.
Proof. exists N.nB. apply nG_nB. Qed.

Corollary nG_non_0 : N.nG <> 0.
Proof. rewrite nG_nB. assert (H0 := nB_non_0). unfold N.nB. omega. Qed.

Corollary half_size_pos : Nat.div2 N.nG > 0.
Proof.
assert (H0 := nB_non_0). rewrite nG_nB. unfold N.nB.
destruct nB as [| n].
- omega.
- simpl. rewrite plus_comm. simpl. omega.
Qed.


(** ** Properties of executions  *)

Open Scope R_scope.

(** Expressing that all good robots are confined in a small disk. *)
CoInductive imprisonned (center : R.t) (radius : R) (e : execution) : Prop
:= InDisk : (forall g, R.dist center (execution_head e (Good g)) <= radius)
            → imprisonned center radius (execution_tail e)
            → imprisonned center radius e.

(** The execution will end in a small disk. *)
Inductive attracted (c : R.t) (r : R) (e : execution) : Prop :=
  | Captured : imprisonned c r e → attracted c r e
  | WillBeCaptured : attracted c r (execution_tail e) → attracted c r e.

Instance imprisonned_compat : Proper (R.eq ==> eq ==> eeq ==> iff) imprisonned.
Proof. Admitted.

Instance attracted_compat : Proper (R.eq ==> eq ==> eeq ==> iff) attracted.
Proof.
intros ? ? Heq ? ? ? e1 e2 He. unfoldR in Heq. subst. split; intro Hin.
+ revert e2 He. induction Hin as [e1 Hin | e1 Hin IHin]; intros e2 He.
  - setoid_rewrite He in Hin. now constructor.
  - constructor 2. apply IHin. now f_equiv.
+ revert e1 He. induction Hin as [e2 Hin | e2 Hin IHin]; intros e1 He.
  - setoid_rewrite <- He in Hin. now constructor.
  - constructor 2. apply IHin. now f_equiv.
Qed.

(** A solution is just convergence property for any demon. *)
Definition solution (r : robogram) : Prop :=
  forall (config : Pos.t) (d : demon), Fair d →
  forall (ε : R), 0 < ε → exists (lim_app : R.t), attracted lim_app ε (execute r d config).

(** A solution is just convergence property for any demon. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  forall (config : Pos.t) (d : demon), FullySynchronous d →
  forall (ε : R), 0 < ε → exists (lim_app : R.t), attracted lim_app ε (execute r d config).


Lemma synchro : ∀ r, solution r → solution_FSYNC r.
Proof.
unfold solution. intros r Hsol config d HFSYNC ε Hε.
auto using fully_synchronous_implies_fair.
Qed.

Close Scope R_scope.


(** We split robots into two halves. *)

Definition left  := half1 Names.Gnames.
Definition right := half2 Names.Gnames.

Definition left_dec (e : Names.G) := List.in_dec Fin.eq_dec e left.

Lemma not_left_is_right : forall g : Names.G, ~In g left -> In g right.
Proof.
intros g Hleft.
assert (Hin : In g Names.Gnames) by apply Names.In_Gnames.
rewrite <- merge_halves, in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof.
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption.
apply Names.Gnames_NoDup.
Qed.

(* Seems like a bad idea because it hides some properties.
Definition left_right_dec (g : Names.G) := half_dec Fin.eq_dec Names.Gnames_NoDup g (Names.In_Gnames g).
*)

(** First and last robots are resp. in the first and in the second half. *)

(*
Section foo.
Variable nG : nat.
Hypothesis nG_non_0 : nG <> 0.

Definition gfirst' : Fin.t nG :=
  match nG as n0 return (nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity nG).

Definition glast' : Fin.t nG :=
  match nG as n return (nG = n -> Fin.t n) with
    | 0 => fun Habs : nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity nG).
End foo.

Require Import Coq.Program.Equality.
Lemma gfirst'_in : forall nG nG_non_0 (even_nG : Nat.Even nG),
  In (@gfirst' nG nG_non_0) (firstn (Nat.div2 nG) (Names.Internals.fin_map (fun x => x))).
Proof.
intros nG nG_non_0.
dependent destruction nG; intros.
+ exfalso; omega.
+ dependent destruction nG0.
  - exfalso; destruct even_nG0; omega.
  - simpl. compute. Print Spect.Names.Internals.fin_map.
      intro abs.
      inversion abs.
Qed.
*)

Definition gfirst : Names.G :=
  match N.nG as n0 return (N.nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : N.nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity N.nG).

Definition glast :=
  match N.nG as n return (N.nG = n -> Fin.t n) with
    | 0 => fun Habs : N.nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity N.nG).

Lemma gfirst_left : In gfirst left.
Proof.
destruct N.nG as [| [| nG]] eqn:HnG.
+ now elim nG_non_0.
+ elim even_nG. intros. omega.
+ unfold left, gfirst.
Admitted.

Lemma glast_right : In glast right.
Proof.
Admitted.

Corollary gfirst_glast : gfirst <> glast.
Proof.
intro Habs. apply (firstn_skipn_nodup_exclusive Names.Gnames_NoDup (Nat.div2 (length Names.Gnames)) gfirst).
- apply gfirst_left.
- rewrite Habs. apply glast_right.
Qed.

Hint Immediate gfirst_left glast_right left_right_exclusive.


(** * Proof of the impossiblity of convergence with one third of robots byzantine. *)

(* A demon that makes the robogram fail:
   - good robots are split into two distinct towers
   - byzantine robots move alternatively between both towers
   - the stack with byzantine is activated, good robots cannot move 
     and you can scale it back on the next round. *)

Open Scope R_scope.
(** The reference starting position **)
Definition config1 : Pos.t := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b => 0
  end.

(** The second position **)
Definition config2 : Pos.t := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b => 1
  end.

Lemma minus_1 : -1 <> 0.
Proof. apply Ropp_neq_0_compat, R1_neq_R0. Qed.

Definition spectrum1 := Spect.add 0 N.nG (Spect.singleton 1 N.nB).
Definition spectrum2 := Spect.add 0 N.nB (Spect.singleton 1 N.nG).

(* An auxiliary lemma to avoid trouble with dependent types. *)
Lemma spect_pos_aux : forall A (eq_dec : forall x y : A, {x = y} + {x <> y}) pt1 pt2, pt1 <> pt2 ->
  forall pt n (l : list A), NoDup l -> length l = (2 * n)%nat ->
  countA_occ R.eq R.eq_dec pt (map (fun x  => if in_dec eq_dec x (half1 l) then pt1 else pt2) l)
  = (Spect.add pt1 n (Spect.singleton pt2 n))[pt].
Proof.
intros A eq_dec pt1 pt2 Hdiff pt n. induction n; simpl; intros l Hnodup Hlen.
* apply length_0 in Hlen. subst. simpl. now rewrite Spect.add_0, Spect.singleton_0, Spect.empty_spec.
* replace (S (n + S (n + 0))) with (S (S ( 2 * n))) in Hlen by ring.
  destruct l as [| a [| b l']]; try discriminate.
  destruct (@not_nil_last _ (b :: l') $(discriminate)$) as [z [l Hl]].
  rewrite Hl in *. clear Hl b l'. rewrite half1_cons2.
  assert (Hdup : ~In a l /\ ~In z l /\ NoDup l /\ a <> z).
  { inversion_clear Hnodup as [| ? ? Hin Hnodup'].
    rewrite <- NoDupA_Leibniz, NoDupA_app_iff in Hnodup'; refine _.
    destruct Hnodup' as [H1 [H2 H3]]. repeat split.
    - intuition.
    - intro Hz. setoid_rewrite InA_Leibniz in H3. apply (H3 z); intuition.
    - now rewrite <- NoDupA_Leibniz.
    - rewrite in_app_iff in Hin. intro Heq. subst. intuition. }
  destruct Hdup as [Hal [Hzl [Hl Haz]]].
  assert (Hlen' : (length l = 2 * n)%nat). { simpl in Hlen. rewrite app_length in Hlen. simpl in Hlen. omega. }
  cbn [map]. rewrite map_app. cbn [map].
   destruct (in_dec eq_dec a (a :: half1 l)) as [_ | Habs]. destruct (in_dec eq_dec z (a :: half1 l)) as [Habs | _].
  + inversion_clear Habs; try contradiction. exfalso. now apply Hzl, half1_incl.
  + rewrite (map_f_dependent_compat _ (fun x => if in_dec eq_dec x (half1 l) then pt1 else pt2)).
    - cbn [countA_occ]. rewrite countA_occ_app. rewrite IHn; trivial.
      assert (pt2 <> pt1) by auto.
      cbn. Rdec_full; subst; Rdec; try Rdec_full; subst; Rdec;
      rewrite ?Spect.add_same, ?Spect.add_other, ?Spect.singleton_same, ?Spect.singleton_other;
      trivial; ring || now unfoldR; auto.
    - { intros x Hin.
        destruct (in_dec eq_dec x (half1 l)) as [Hx | Hx],
                 (in_dec eq_dec x (a :: half1 l)) as [Hx' | Hx']; trivial.
        - elim Hx'. intuition.
        - inversion_clear Hx'; subst; contradiction. }
  + elim Habs. intuition.
Qed.

Theorem spect_pos1 : Spect.eq (!! config1) spectrum1.
Proof.
intro pt. unfold config1, spectrum1.
rewrite Spect.from_config_spec, Spect.Pos.list_spec.
change Spect.Names.names with (map Good Spect.Names.Gnames ++ map Byz Spect.Names.Bnames).
rewrite map_app, map_map, map_map, map_cst, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
unfold left_dec, left. rewrite (spect_pos_aux _ H01 _ nB).
+ destruct (R.eq_dec pt 0) as [Heq | Hneq]; [| destruct (R.eq_dec pt 1) as [Heq | ?]].
  - unfoldR in Heq. subst. rewrite countA_occ_alls_in; refine _.
    repeat rewrite Spect.add_same, Spect.singleton_other; trivial.
    rewrite Names.Bnames_length. unfold N.nG, N.nB. omega.
  - unfoldR in Heq. subst. rewrite countA_occ_alls_out; trivial; refine _.
    repeat rewrite Spect.add_other, Spect.singleton_same; trivial.
    unfold N.nB. omega.
  - rewrite countA_occ_alls_out; auto.
    now repeat rewrite Spect.add_other, Spect.singleton_other.
+ apply Spect.Names.Gnames_NoDup.
+ rewrite Names.Gnames_length. reflexivity.
Qed.

Theorem spect_pos2 : Spect.eq (!! config2) spectrum2.
Proof.
intro pt. unfold config2, spectrum2.
rewrite Spect.from_config_spec, Spect.Pos.list_spec.
change Spect.Names.names with (map Good Spect.Names.Gnames ++ map Byz Spect.Names.Bnames).
rewrite map_app, map_map, map_map, map_cst, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
unfold left_dec, left. rewrite (spect_pos_aux _ H01 _ nB).
+ destruct (R.eq_dec pt 0) as [Heq | Hneq]; [| destruct (R.eq_dec pt 1) as [Heq | Hneq']].
  - unfoldR in Heq. subst. rewrite countA_occ_alls_out; auto.
    repeat rewrite Spect.add_same, Spect.singleton_other; trivial.
    unfold N.nB. omega.
  - unfoldR in Heq. subst. rewrite countA_occ_alls_in; refine _.
    repeat rewrite Spect.add_other, Spect.singleton_same; trivial.
    rewrite Names.Bnames_length. unfold N.nG, N.nB. omega.
  - rewrite countA_occ_alls_out; auto.
    now repeat rewrite Spect.add_other, Spect.singleton_other.
+ apply Spect.Names.Gnames_NoDup.
+ rewrite Names.Gnames_length. reflexivity.
Qed.

Lemma swap_spect2_spect1 : Spect.eq (Spect.map (Sim.homothecy 1 minus_1) spectrum2) spectrum1.
Proof.
intro pt. unfold spectrum1, spectrum2. rewrite Spect.map_add, Spect.map_singleton; refine _.
simpl. unfoldR. ring_simplify (-1 * (0 + -1)). ring_simplify (-1 * (1 + -1)).
destruct (Rdec pt 0); [| destruct (Rdec pt 1)]; subst;
repeat rewrite ?Spect.add_same, ?Spect.singleton_same, ?Spect.singleton_other, ?Spect.add_other; auto.
Qed.

(* An execution alternating config1 and config2 *)
CoFixpoint exec := NextExecution config1 (NextExecution config2 exec).

(** The demon defeating any robogram *)

Definition step1 (id : Names.ident) :=
  match id with
    | Good g => if left_dec g then Some (fun c : R.t => Sim.translation (R.opp c)) else None
    | Byz b => Some (fun c : R.t => Sim.translation (R.opp c))
  end.

Lemma step1_zoom : forall id sim c, step1 id = Some sim -> Sim.zoom (sim c) ≠ 0.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. inversion_clear Hsim. simpl. apply R1_neq_R0.
- inversion_clear Hsim. simpl. apply R1_neq_R0.
Qed.

Lemma step1_center : forall id sim c, step1 id = Some sim → R.eq (Sim.center (sim c)) c.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. inversion_clear Hsim. simpl. now rewrite R.opp_opp.
- inversion_clear Hsim. simpl. now rewrite R.opp_opp.
Qed.

Definition bad_da1 : demonic_action := {|
  step := step1;
  relocate_byz := fun _ => 1;
  step_zoom := step1_zoom;
  step_center := step1_center |}.

Definition step2 (id : Names.ident) :=
  match id with
    | Good g => if left_dec g then None else Some (fun c : R.t => Sim.homothecy c minus_1)
    | Byz b => Some (fun c : R.t => Sim.translation (R.opp c))
  end.

Lemma step2_zoom : forall id sim c, step2 id = Some sim -> Sim.zoom (sim c) ≠ 0.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. inversion_clear Hsim. simpl.
  rewrite Rabs_Ropp, Rabs_R1. apply R1_neq_R0.
- inversion_clear Hsim. simpl. apply R1_neq_R0.
Qed.

Lemma step2_center : forall id sim c, step2 id = Some sim → R.eq (Sim.center (sim c)) c.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. now inversion_clear Hsim.
- inversion_clear Hsim. simpl. now rewrite R.opp_opp.
Qed.

Definition bad_da2 : demonic_action := {|
  step := step2;
  relocate_byz := fun _ => 0;
  step_zoom := step2_zoom;
  step_center := step2_center |}.

CoFixpoint bad_demon := NextDemon bad_da1 (NextDemon bad_da2 bad_demon).

Lemma bad_demon_head : demon_head bad_demon = bad_da1.
Proof. reflexivity. Qed.

Lemma bad_demon_tail_head : demon_head (demon_tail bad_demon) = bad_da2.
Proof. reflexivity. Qed.

Lemma bad_demon_tail_tail : demon_tail (demon_tail bad_demon) = bad_demon.
Proof. reflexivity. Qed.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof.
cofix.
constructor; [| constructor].
* intros [g1 | b1] id2; [destruct (left_dec g1) |].
  + apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
  + destruct id2 as [g2 | b2]; [destruct (left_dec g2) |].
    - apply kReduce; simpl.
        destruct (left_dec g1); trivial; contradiction.
        destruct (left_dec g2); discriminate || contradiction.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
    - apply kStall; simpl.
        destruct (left_dec g1); trivial; contradiction.
        destruct (left_dec g2); trivial; contradiction.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
    - apply kReduce; simpl.
        destruct (left_dec g1); trivial; contradiction.
        discriminate.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
  + apply kReset. discriminate.
* intros [g1 | b1] id2; [destruct (left_dec g1) |].
  + destruct id2 as [g2 | b2]; [destruct (left_dec g2) |].
    - apply kStall; simpl.
        destruct (left_dec g1); trivial; contradiction.
        destruct (left_dec g2); trivial; contradiction.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
    - apply kReduce; simpl.
        destruct (left_dec g1); trivial; contradiction.
        destruct (left_dec g2); discriminate || contradiction.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
    - apply kReduce; simpl.
        destruct (left_dec g1); trivial; contradiction.
        discriminate.
        apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
  + apply kReset. simpl. destruct (left_dec g1); discriminate || contradiction.
  + apply kReset. discriminate.
* simpl. assumption.
Qed.

Corollary Fair_bad_demon : Fair bad_demon.
Proof. apply (@kFair_Fair 1%nat). apply kFair_bad_demon. Qed.

Corollary kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon;auto.
- auto.
Qed.

(** From now on and until the final theorem we give us a robogram [r].
    We now prove that [r] does not move in spectrum *)
Section PropRobogram.

Variable r : robogram.
Hypothesis sol : solution r.


(** Idea: If all robots are gathered at the same position, then the robogram cannot make them move.
          Indeed, otherwise, the convergence would not be valid for ε = half the move. *)
Definition gathered_at (pt : R) (pos : Pos.t) := forall g : Names.G, pos (Good g) = pt.

Theorem gathered_at_no_move : forall pt config, gathered_at pt config -> r (!! config) = pt.
Proof. Admitted.

(** Any spectrum containing a tower of size at least [N.nG] could be the previous configuration,
    hence the robogram does not make robots move. *)
Theorem no_move : forall spectrum pt, (spectrum[pt] >= N.nG)%nat -> r spectrum = pt.
Proof.
intros spectrum pt Hpt.
pose (config := (fun _ => pt) : Pos.t).
assert (Spect.eq (!! config) spectrum).
Admitted.

Corollary no_move1 : r spectrum1 = 0.
Proof.
assert (0 <> 1) by auto using R1_neq_R0.
apply no_move. unfold spectrum1.
rewrite Spect.add_same, Spect.singleton_other; trivial. omega.
Qed.

Corollary no_move2 : r spectrum2 = 1.
Proof.
assert (1 <> 0) by apply R1_neq_R0.
apply no_move. unfold spectrum2.
rewrite Spect.add_other, Spect.singleton_same; trivial. omega.
Qed.

Lemma round_config1 : Pos.eq (round r bad_da1 config1) config2.
Proof.
intros id. unfold round. simpl. destruct id as [g | b]; simpl; try reflexivity; [].
destruct (left_dec g) as [Hleft | Hright]; try reflexivity; [].
rewrite R.opp_origin, Sim.translation_origin, Pos.map_id, spect_pos1.
simpl. apply no_move1.
Qed.

Lemma round_config2 : Pos.eq (round r bad_da2 config2) config1.
Proof.
intros id. unfold round. simpl. destruct id as [g | b]; simpl; try reflexivity; [].
destruct (left_dec g) as [Hleft | Hright]; try reflexivity; [].
rewrite <- Spect.from_config_map; refine _. rewrite spect_pos2, swap_spect2_spect1.
simpl. unfoldR. rewrite no_move1. ring.
Qed.

Lemma execute_bad_demon_aux : forall e, eeq (execute r bad_demon config1) e -> eeq e exec.
Proof.
cofix exec. intros e He; constructor; [| constructor].
+ rewrite <- He. simpl. reflexivity.
+ rewrite <- He. simpl. apply round_config1.
+ cbn. apply exec. rewrite <- He. cbn. now rewrite round_config1, round_config2.
Qed.

Theorem execute_bad_demon : eeq (execute r bad_demon config1) exec.
Proof. now apply execute_bad_demon_aux. Qed.

End PropRobogram.


(***********************)
(** *  Final theorem  **)
(***********************)

(** A 2-step induction scheme for attracted. *)
Definition attracted_ind2 (c : R.t) (r : R) (P : execution → Prop)
  (P0 : ∀ e : execution, imprisonned c r e → P e)
  (P1 : ∀ e : execution, imprisonned c r (execution_tail e) → P e)
  (Ps : ∀ e : execution, attracted c r (execution_tail (execution_tail e)) →
                         P (execution_tail (execution_tail e)) → P e)
  := fix F (e : execution) (a : attracted c r e) {struct a} : P e :=
    match a with
      | Captured i => P0 e i
      | WillBeCaptured _ (Captured i) => P1 e i
      | WillBeCaptured _ (WillBeCaptured _ a0) => Ps e a0 (F (execution_tail (execution_tail e)) a0)
    end.

Theorem noConvergence : forall r, ~solution r.
Proof.
intros r Hr.
assert (Hpos : 0 < 1/4) by lra.
destruct (Hr config1 bad_demon Fair_bad_demon _ Hpos) as [pt Hpt].
rewrite execute_bad_demon in Hpt; trivial.
revert Hpt. cut (eeq exec exec); try reflexivity. generalize exec at -2. intros e He Hpt.
induction Hpt using attracted_ind2.
+ (* First step *)
  rewrite He in H. inversion H as [Habs _].
  assert (Hfirst := Habs gfirst). assert (Hlast := Habs glast). simpl in *.
  pose (gfirst_left). pose (glast_right).
  destruct (left_dec gfirst); try contradiction.
  destruct (left_dec glast).
  - now apply (left_right_exclusive glast).
  - clear -Hfirst Hlast. cut (1 <= 1/4 + 1/4). lra.
    replace 1 with ((pt - 0) + (1 - pt)) at 1 by ring.
    setoid_rewrite <- Rabs_pos_eq at 1; try lra.
    eapply Rle_trans; try now apply Rabs_triang.
    apply Rplus_le_compat; assumption || now rewrite Rabs_minus_sym.
+ (* Second step, same proof *)
  rewrite He in H. inversion H as [Habs _].
  assert (Hfirst := Habs gfirst). assert (Hlast := Habs glast). simpl in *.
  pose (gfirst_left). pose (glast_right).
  destruct (left_dec gfirst); try contradiction.
  destruct (left_dec glast).
  - now apply (left_right_exclusive glast).
  - clear -Hfirst Hlast. cut (1 <= 1/4 + 1/4). lra.
    replace 1 with ((pt - 0) + (1 - pt)) at 1 by ring.
    setoid_rewrite <- Rabs_pos_eq at 1; try lra.
    eapply Rle_trans; try now apply Rabs_triang.
    apply Rplus_le_compat; assumption || now rewrite Rabs_minus_sym.
+ (* Inductive step *)
  apply IHHpt. rewrite He. simpl. reflexivity.
Qed.

Print Assumptions noConvergence.
