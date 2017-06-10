(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8.
Require Import Reals.
Require Import Psatz.
Require Import SetoidDec.
Require Import Arith.Div2.
Require Import Omega.
Require Import SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.R.
Require Import Pactole.Spectra.MultisetSpectrum.
Require Import Pactole.Models.Rigid.


Set Implicit Arguments.
Close Scope R_scope.
Import List.
Import SetoidClass.


(** There are [2 * n] good robots and [n] byzantine ones. *)
Parameter n: nat.
Axiom n_non_0 : n <> 0%nat.

Instance MyRobotsDef : NamesDef := RobotsDef (2 * n) n.
Instance MyRobots : Names := Robots (2 * n) n.

(* BUG?: To help finding correct instances, loops otherwise! *)
Existing Instance R_Setoid.
Existing Instance R_EqDec.
Existing Instance R_RMS.

(** The spectrum is a multiset of positions *)
Notation "!!" := spect_from_config (at level 1).

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall config l, (!! config)[l] = countA_occ _ equiv_dec l (config_list config)
 := spect_from_config_spec.


Add Search Blacklist "Spect.M" "Ring".
Hint Extern 0 (1 =/= 0)%R => apply R1_neq_R0.
Hint Extern 0 (0 =/= 1)%R => symmetry; trivial.
Hint Extern 0 (1 <> 0)%R => apply R1_neq_R0.
Hint Extern 0 (0 <> 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (_ <> _) => match goal with | H : ?x <> ?y |- ?y <> ?x => intro; apply H; now symmetry end.
Hint Extern 0 (~@equiv R _ 1 0)%R => apply R1_neq_R0.
Hint Extern 0 (~@equiv R _ 0 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (~equiv R _ _ _) =>
  match goal with | H : ~@equiv R _ ?x ?y |- ~@equiv R _ ?y ?x => intro; apply H; now symmetry end.


Lemma nB_value : nB = n.
Proof. reflexivity. Qed.

Lemma nG_nB : nG = 2 * nB.
Proof. reflexivity. Qed.

Corollary even_nG : Nat.Even nG.
Proof. exists nB. apply nG_nB. Qed.

Corollary nG_non_0 : nG <> 0.
Proof. rewrite nG_nB. assert (H0 := n_non_0). simpl. omega. Qed.

Corollary half_size_conf : Nat.div2 nG > 0.
Proof.
assert (H0 := n_non_0). rewrite nG_nB, nB_value.
destruct n as [| n].
- omega.
- simpl. rewrite plus_comm. simpl. omega.
Qed.


(** ** Properties of executions  *)

Open Scope R_scope.

(** Expressing that all good robots are confined in a small disk. *)
Definition imprisoned (center : R) (radius : R) (e : execution) : Prop :=
  Streams.forever (Streams.instant (fun config => forall g, dist center (config (Good g)) <= radius)) e.

(** The execution will end in a small disk. *)
Definition attracted (c : R) (r : R) (e : execution) : Prop := Streams.eventually (imprisoned c r) e.

Instance fun_equiv_pointwise_compat A B `{Setoid B} :
  subrelation (@equiv _ (fun_equiv A _)) (pointwise_relation _ equiv).
Proof. intros f g Hfg x. apply Hfg. Qed.

Instance imprisoned_compat : Proper (equiv ==> Logic.eq ==> equiv ==> iff) imprisoned.
Proof.
intros c1 c2 Hc ? r Hr e1 e2 He. subst. split.
+ revert c1 c2 e1 e2 Hc He. coinduction Hrec.
  - intro g. apply Streams.hd_compat in He. rewrite <- He, <- Hc. apply H.
  - inversion_clear H. eapply Hrec; try eassumption. now f_equiv.
+ revert c1 c2 e1 e2 Hc He. coinduction Hrec.
  - intro g. apply Streams.hd_compat in He. rewrite He, Hc. apply H.
  - inversion_clear H. eapply Hrec; try eassumption. now f_equiv.
Qed.

Instance attracted_compat : Proper (equiv ==> eq ==> equiv ==> iff) attracted.
Proof. intros ? ? Heq ? ? ?. now apply Streams.eventually_compat, imprisoned_compat. Qed.

(** A solution is just convergence property for any demon. *)
Definition solution (r : robogram) : Prop :=
  forall (config : configuration) (d : demon), Fair d →
  forall (ε : R), 0 < ε → exists (pt : R), attracted pt ε (execute r d config).

(** A solution is just convergence property for any demon. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : demon), FullySynchronous d →
  forall (ε : R), 0 < ε → exists (pt : R), attracted pt ε (execute r d config).


Lemma synchro : ∀ r, solution r → solution_FSYNC r.
Proof. unfold solution. intros r Hfair config d Hd. now apply Hfair, fully_synchronous_implies_fair. Qed.

Close Scope R_scope.


(** We split robots into two halves. *)

Definition left  := half1 Gnames.
Definition right := half2 Gnames.

Definition left_dec (e : G) := List.in_dec Fin.eq_dec e left.

Lemma not_left_is_right : forall g : G, ~In g left -> In g right.
Proof.
intros g Hleft.
assert (Hin : List.In g Gnames) by apply In_Gnames.
rewrite <- merge_halves, List.in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof.
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption.
apply Gnames_NoDup.
Qed.

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

Definition gfirst : G :=
  match nG as n0 return (nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity nG).

Definition glast :=
  match nG as n return (nG = n -> Fin.t n) with
    | 0 => fun Habs : nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity nG).

Lemma gfirst_left : In gfirst left.
Proof.
destruct nG as [| [| nG]] eqn:HnG.
+ now elim nG_non_0.
+ elim even_nG. intros. omega.
+ unfold left, gfirst.
  unfold reflexivity, eq_Reflexive.
Admitted.

Lemma glast_right : In glast right.
Proof.
Admitted.

Hint Immediate gfirst_left glast_right left_right_exclusive.


(** * Proof of the impossiblity of convergence with one third of robots byzantine. *)

(* A demon that makes the robogram fail:
   - good robots are split into two distinct towers
   - byzantine robots move alternatively between both towers
   - the stack with byzantine is activated, good robots cannot move 
     and you can scale it back on the next round. *)

Open Scope R_scope.
(** The reference starting configuration **)
Definition config1 : configuration := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b => 0
  end.

(** The second configuration **)
Definition config2 : configuration := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b => 1
  end.

Lemma minus_1 : -1 <> 0.
Proof. apply Ropp_neq_0_compat, R1_neq_R0. Qed.

Definition spectrum1 := add 0 nG (singleton 1 nB).
Definition spectrum2 := add 0 nB (singleton 1 nG).

(* An auxiliary lemma to avoid trouble with dependent types. *)
Lemma spect_config_aux : forall pt1 pt2, pt1 <> pt2 ->
  forall pt n l, NoDup l -> length l = (2 * n)%nat ->
  countA_occ equiv equiv_dec pt
    (map (fun x  => if in_dec (@Fin.eq_dec nG) x (half1 l) then pt1 else pt2) l)
  = (add pt1 n (singleton pt2 n))[pt].
Proof.
intros pt1 pt2 Hdiff pt n. induction n as [| n]; intros l Hnodup Hlen.
* apply length_0 in Hlen. subst. simpl map. now rewrite add_0, singleton_0, empty_spec.
* replace (2 * S n)%nat with (S (S (2 * n)))%nat in Hlen by ring.
  destruct l as [| a [| b l']]; try discriminate.
  destruct (@not_nil_last _ (b :: l') ltac:(discriminate)) as [z [l Hl]].
  rewrite Hl in *. clear Hl b l'. rewrite half1_cons2.
  assert (Hdup : ~List.In a l /\ ~List.In z l /\ NoDup l /\ a <> z).
  { inversion_clear Hnodup as [| ? ? Hin Hnodup'].
    rewrite <- NoDupA_Leibniz, NoDupA_app_iff in Hnodup'; refine _.
    destruct Hnodup' as [H1 [H2 H3]]. repeat split.
    - intuition.
    - intro Hz. setoid_rewrite InA_Leibniz in H3. apply (H3 z); intuition.
    - now rewrite <- NoDupA_Leibniz.
    - rewrite in_app_iff in Hin. intro Heq. subst. intuition. }
  destruct Hdup as [Hal [Hzl [Hl Haz]]].
  assert (Hlen' : (length l = 2 * n)%nat). { simpl in Hlen. rewrite app_length in Hlen. simpl in *. omega. }
  cbn [map]. rewrite map_app. cbn [map].
   destruct (in_dec Fin.eq_dec a (a :: half1 l)) as [_ | Habs].
   destruct (in_dec Fin.eq_dec z (a :: half1 l)) as [Habs | _].
  + inversion_clear Habs; try (now elim Haz); [].
    exfalso. now apply Hzl, half1_incl.
  + rewrite (map_ext_in _ (fun x => if in_dec Fin.eq_dec x (half1 l) then pt1 else pt2)).
    - cbn [countA_occ]. rewrite countA_occ_app. rewrite IHn; trivial.
      assert (pt2 <> pt1) by auto.
      cbn [countA_occ]. unfold equiv_dec, R_EqDec.
      Rdec_full; subst; Rdec; try Rdec_full; subst; Rdec; change Rdec with R_EqDec;
      rewrite ?add_same, ?add_other, ?singleton_same, ?singleton_other;
      trivial; ring || (try (intro; auto)).
    - intros x Hin.
      destruct (in_dec Fin.eq_dec x (half1 l)) as [Hx | Hx],
               (in_dec Fin.eq_dec x (a :: half1 l)) as [Hx' | Hx']; trivial.
      -- elim Hx'. intuition.
      -- inversion_clear Hx'; subst; contradiction.
  + elim Habs. intuition.
Qed.

Theorem spect_config1 : (!! config1) == spectrum1.
Proof.
intro pt. unfold config1, spectrum1, multiset_spectrum.
rewrite spect_from_config_spec, config_list_spec.
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_app, map_map, map_map, map_cst, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
unfold left_dec, left. erewrite (spect_config_aux H01 _ nB).
+ destruct (equiv_dec pt 0) as [Heq | Hneq]; [| destruct (equiv_dec pt 1) as [Heq | ?]].
  - cbn in Heq. subst. rewrite countA_occ_alls_in; autoclass.
    repeat rewrite add_same, singleton_other; trivial.
    rewrite Bnames_length. unfold nG, nB. simpl. omega.
  - cbn in Heq. subst. rewrite countA_occ_alls_out; trivial; autoclass.
    repeat rewrite add_other, singleton_same; trivial.
    unfold nB. omega.
  - rewrite countA_occ_alls_out; auto; [].
    now repeat rewrite add_other, singleton_other.
+ change (Fin.t (@nG MyRobotsDef)) with G. apply Gnames_NoDup.
+ change (Fin.t (@nG MyRobotsDef)) with G. rewrite Gnames_length. reflexivity.
Qed.

Theorem spect_conf2 : (!! config2) == spectrum2.
Proof.
intro pt. unfold config2, spectrum2, multiset_spectrum in *.
rewrite spect_from_config_spec, config_list_spec.
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_app, map_map, map_map, map_cst, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
unfold left_dec, left. rewrite (spect_config_aux H01 _ nB).
+ destruct (equiv_dec pt 0) as [Heq | Hneq]; [| destruct (equiv_dec pt 1) as [Heq | Hneq']].
  - cbn in Heq. subst. rewrite countA_occ_alls_out; auto; [].
    repeat rewrite add_same, singleton_other; trivial.
    unfold nB. simpl. omega.
  - cbn in Heq. subst. rewrite countA_occ_alls_in; autoclass.
    repeat rewrite add_other, singleton_same; trivial.
    rewrite Bnames_length. unfold nG, nB. simpl. omega.
  - rewrite countA_occ_alls_out; auto; [].
    now repeat rewrite add_other, singleton_other.
+ change (Fin.t (@nG MyRobotsDef)) with G. apply Gnames_NoDup.
+ change (Fin.t (@nG MyRobotsDef)) with G. rewrite Gnames_length. reflexivity.
Qed.

Lemma swap_spect2_spect1 : MMultisetExtraOps.map (homothecy 1 minus_1) spectrum2 == spectrum1.
Proof.
intro pt. unfold spectrum1, spectrum2. rewrite map_add, map_singleton; autoclass.
simpl ((homothecy 1 minus_1) 0). ring_simplify (-1 * (0 + -1)).
simpl ((homothecy 1 minus_1) 1). ring_simplify (-1 * (1 + -1)).
destruct (Rdec pt 0); [| destruct (Rdec pt 1)]; subst;
repeat rewrite ?add_same, ?singleton_same, ?singleton_other, ?add_other; auto.
Qed.

(* An execution alternating config1 and config2 *)
Definition exec : execution := Streams.alternate config1 config2.

(** The demon defeating any robogram *)

Definition step1 (id : ident) :=
  match id with
    | Good g => if left_dec g then Some (fun c : R => translation (opp c)) else None
    | Byz b => Some (fun c : R => translation (opp c))
  end.

Lemma step1_zoom : forall id sim c, step1 id = Some sim -> zoom (sim c) ≠ 0.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. inversion_clear Hsim. simpl. apply R1_neq_R0.
- inversion_clear Hsim. simpl. apply R1_neq_R0.
Qed.

Lemma step1_center : forall id sim c, step1 id = Some sim → center (sim c) == c.
Proof.
intros [g | b] sim c Hsim. simpl in Hsim.
- destruct (left_dec g); try discriminate. inversion_clear Hsim.
  simpl center. change (- - c) with (opp (opp c)). apply opp_opp.
- inversion_clear Hsim. simpl center. change (- - c) with (opp (opp c)). apply opp_opp.
Qed.

Definition bad_da1 : demonic_action := {|
  step := step1;
  relocate_byz := fun _ => 1;
  step_zoom := step1_zoom;
  step_center := step1_center |}.

Definition step2 (id : ident) :=
  match id with
    | Good g => if left_dec g then None else Some (fun c : R => homothecy c minus_1)
    | Byz b => Some (fun c : R => translation (opp c))
  end.

Lemma step2_zoom : forall id sim c, step2 id = Some sim -> zoom (sim c) ≠ 0.
Proof.
intros [g | b] sim c Hsim; simpl in *.
- destruct (left_dec g); try discriminate. inversion_clear Hsim. simpl.
  rewrite Rabs_Ropp, Rabs_R1. auto.
- inversion_clear Hsim. simpl. auto.
Qed.

Lemma step2_center : forall id sim c, step2 id = Some sim → center (sim c) == c.
Proof.
intros [g | b] sim c Hsim; simpl in Hsim.
- destruct (left_dec g); try discriminate. now inversion_clear Hsim.
- inversion_clear Hsim. simpl center. change (- - c) with (opp (opp c)). apply opp_opp.
Qed.

Definition bad_da2 : demonic_action := {|
  step := step2;
  relocate_byz := fun _ => 0;
  step_zoom := step2_zoom;
  step_center := step2_center |}.

Definition bad_demon : demon := Streams.alternate bad_da1 bad_da2.

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
Proof. apply (@kFair_Fair _ _ _ _ _ 1%nat). apply kFair_bad_demon. Qed.

Corollary kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon; auto.
- auto.
Qed.

(** From now on and until the final theorem we give us a robogram [r].
    We now prove that [r] does not move in spectrum *)
Section PropRobogram.

Variable r : robogram.
Hypothesis sol : solution r.

(** In any spectrum containing a tower of size at least [N.nG], the robogram does not make robots move.
    Indeed, otherwise they all go to the same location and we can build a demon that shift byzantine robots
    by the same amount in order to get the same translated configuration. *)

Definition shifting_da (pt : R) : demonic_action.
refine {| step := fun _ => Some (fun c => translation (opp c));
          relocate_byz := fun _ => pt |}.
Proof.
+ abstract (intros _ sim c Heq; inversion_clear Heq; simpl; apply R1_neq_R0).
+ abstract (intros _ sim c Heq; inversion_clear Heq; simpl; now rewrite Ropp_involutive).
Defined.

(** A demon that shifts byzantine robots by d each round. *)
CoFixpoint shifting_demon d pt := Streams.cons (shifting_da (pt + d + 1)) (shifting_demon d (pt + d)).

Lemma Fair_shifting_demon : forall d pt, Fair (shifting_demon d pt).
Proof.
intros d pt. apply fully_synchronous_implies_fair. revert pt.
cofix shift_fair. intro pt. constructor.
+ intro. simpl. discriminate.
+ cbn. apply shift_fair.
Qed.

(** The configuration that will be shifted **)
Definition config0 pt : configuration := fun id =>
  match id with
    | Good _ => pt
    | Byz b => pt + 1
  end.

(* An execution that shifts by [d] at each round, starting from [pt]. *)
CoFixpoint shifting_execution d pt := Streams.cons (config0 pt) (shifting_execution d (pt + d)).

Lemma spectrum_config0 : forall pt : R,
  !! (map_config (fun x : R => RealMetricSpaces.add x (opp pt)) (config0 pt)) == spectrum1.
Proof.
intros pt x. unfold config0, spectrum1.
rewrite spect_from_config_spec, config_list_spec.
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_app, map_map, map_map, countA_occ_app.
rewrite (map_ext_in _ (fun _ : G => 0)), (map_ext_in _ (fun _ : B => 1)).
+ do 2 rewrite map_cst. destruct (equiv_dec x 0) as [Hx | Hnx]; [| destruct (equiv_dec x 1) as [Hx | Hnx']].
  - rewrite Hx, countA_occ_alls_in, Gnames_length; autoclass.
    rewrite countA_occ_alls_out; auto.
    rewrite add_same, singleton_other; auto.
  - rewrite Hx, countA_occ_alls_in, Bnames_length; autoclass.
    rewrite countA_occ_alls_out; auto.
    rewrite add_other, singleton_same; auto.
  - repeat rewrite countA_occ_alls_out; auto.
    rewrite add_other, singleton_other; auto.
+ intros b Hin. unfold map_config. simpl. ring.
+ intros g Hin. unfold map_config. simpl. ring.
Qed.

Corollary spect_config0_0 : !! (config0 0) == spectrum1.
Proof. rewrite <- (spectrum_config0 0). f_equiv. intro. compute. ring. Qed.

Section AbsurdMove.
Definition move := r spectrum1.
Hypothesis absurdmove : move <> 0.

Lemma round_move : forall pt, round r (shifting_da (pt + move + 1)) (config0 pt) == config0 (pt + move).
Proof.
intros pt id. unfold round. simpl (step (shifting_da (pt + move + 1)) id). cbn iota beta.
destruct id as [g | b].
- rewrite (spectrum_config0 pt). simpl. fold move. ring.
- reflexivity.
Qed.

Lemma keep_moving_by_eq : forall pt config,
  config == config0 pt -> execute r (shifting_demon move pt) config == shifting_execution move pt.
Proof.
cofix shift_exec. intros pt config Heq.
constructor.
+ simpl. assumption.
+ simpl. apply shift_exec. rewrite <- round_move. now apply round_compat. (* BUG? rewrite Heq shoud work *)
Qed.

Theorem keep_moving : forall pt, execute r (shifting_demon move pt) (config0 pt) == shifting_execution move pt.
Proof. intro. apply keep_moving_by_eq. reflexivity. Qed.

Theorem absurd : False.
Proof.
assert (Hthird_move : 0 < Rabs (move / 3)). { apply Rabs_pos_lt. lra. }
specialize (sol (config0 0) (Fair_shifting_demon move 0) Hthird_move).
destruct sol as [pt Hpt]. rewrite keep_moving in Hpt.
remember (shifting_execution move 0) as e. remember (Rabs (move / 3)) as ε.
revert Heqe. generalize 0.
induction Hpt as [e IHpt | e IHpt]; intros start Hstart.
+ subst e ε. destruct IHpt as [Hnow1 [Hnow2 Hlater]]. cbn in *.
  clear -absurdmove Hnow1 Hnow2. specialize (Hnow1 gfirst). specialize (Hnow2 gfirst).
  cut (Rabs move <= Rabs (move / 3) + Rabs (move / 3)).
  - assert (Hpos : 0 < Rabs move) by now apply Rabs_pos_lt.
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv; try lra.
    assert (Habs3 : Rabs 3 = 3). { apply Rabs_pos_eq. lra. } rewrite Habs3 in *.
    lra.
  - replace move with ((pt - start) - (pt - (start + move))) at 1 by ring.
    unfold Rminus at 1. eapply Rle_trans; try (now apply Rabs_triang); [].
    apply Rplus_le_compat; trivial; []. now rewrite Rabs_Ropp.
+ apply (IHIHpt (start + move)). subst e. simpl. reflexivity.
Qed.

End AbsurdMove.

Theorem no_move1 : r spectrum1 = 0.
Proof.
destruct (Rdec (r spectrum1) 0) as [? | Hmove]; trivial.
exfalso. apply absurd. assumption.
Qed.

Corollary no_move2 : r (!! (map_config (homothecy  1 minus_1) config2 )) = 0.
Proof.
assert (1 <> 0) by apply R1_neq_R0.
rewrite <- (@spect_from_config_map _ _ _ _ _ _ (homothecy 1 minus_1) ltac:(autoclass) config2).
rewrite spect_conf2. rewrite swap_spect2_spect1. apply no_move1.
Qed.

Lemma round_config1 : round r bad_da1 config1 == config2.
Proof.
intros id. unfold round. simpl (step bad_da1 id).
destruct id as [g | b]; try reflexivity; []. simpl (step1 (Good g)).
destruct (left_dec g) as [Hleft | Hright] eqn:Heq; try reflexivity; [].
simpl config1. rewrite Heq. ring_simplify (- 0). change 0 with origin.
unfold translation. rewrite translation_origin at 1.
unfold id. simpl. rewrite Heq. rewrite <- no_move1 at 1.
change (r (!! (map_config (fun x => x + 0) config1)) == r spectrum1).
assert (map_config (λ x : R, x + 0) config1 == config1).
{ rewrite <- (Configurations.map_id config1) at 2.
  apply map_config_compat; try reflexivity; []. compute. intros. lra. }
apply pgm_compat. rewrite H. apply spect_config1.
Qed.

Lemma round_config2 : round r bad_da2 config2 == config1.
Proof.
intros id. unfold round. destruct id as [g | b]; try reflexivity; [].
simpl. destruct (left_dec g) as [Hleft | Hright]; try reflexivity; [].
cbn. replace 1 with (0 + 1) at 3 by ring. f_equal.
change (/-1 * r (!! (map_config (homothecy 1 minus_1) config2)) = 0).
rewrite no_move2. field.
Qed.

Lemma execute_bad_demon_aux : forall e, execute r bad_demon config1 == e -> e == exec.
Proof.
cofix exec. intros e He; constructor; [| constructor].
+ rewrite <- He. simpl. reflexivity.
+ rewrite <- He. simpl. apply round_config1.
+ apply exec. rewrite <- He.
  change (Streams.tl (Streams.tl (execute r bad_demon config1)))
    with (execute r bad_demon (round r bad_da2 (round r bad_da1 config1))).
f_equiv. rewrite <- round_config2 at 1.
apply round_compat; try reflexivity; []. now rewrite round_config1.
Qed.

Theorem execute_bad_demon : execute r bad_demon config1 == exec.
Proof. now apply execute_bad_demon_aux. Qed.

End PropRobogram.


(***********************)
(** *  Final theorem  **)
(***********************)

(** A 2-step induction scheme for attracted. *)
Definition attracted_ind2 (c : R) (r : R) (P : execution → Prop)
  (P0 : ∀ e : execution, imprisoned c r e → P e)
  (P1 : ∀ e : execution, imprisoned c r (Streams.tl e) → P e)
  (Ps : ∀ e : execution, attracted c r (Streams.tl (Streams.tl e)) →
                         P (Streams.tl (Streams.tl e)) → P e)
  := fix F (e : execution) (a : attracted c r e) {struct a} : P e :=
    match a with
      | Streams.Now i => P0 e i
      | Streams.Later (Streams.Now i) => P1 e i
      | Streams.Later (Streams.Later a0) => Ps e a0 (F (Streams.tl (Streams.tl e)) a0)
    end.

Theorem noConvergence : forall r, ~solution r.
Proof.
intros r Hr.
assert (Hpos : 0 < 1/4) by lra.
destruct (Hr config1 bad_demon Fair_bad_demon _ Hpos) as [pt Hpt].
rewrite execute_bad_demon in Hpt; trivial.
revert Hpt. cut (exec == exec); try reflexivity. generalize exec at -2. intros e He Hpt.
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
  apply IHHpt. rewrite He. reflexivity.
Qed.

Print Assumptions noConvergence.
