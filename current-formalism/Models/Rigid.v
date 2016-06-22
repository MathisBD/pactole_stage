(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.


Section RigidFormalism.

Context {loc : Type}.
Context {Sloc : Setoid loc}.
Context {ESloc : EqDec Sloc}.
Context {RMS : @RealMetricSpace loc Sloc ESloc}.
Context {Ndef : NamesDef}.
Context {N : Names}.
Context {Spect : @Spectrum loc Sloc ESloc Ndef N}.


(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it wishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : B → loc;
  step : ident → option (loc → similarity loc);
  step_compat : Proper (eq ==> opt_eq (equiv ==> equiv)) step;
  step_zoom :  forall id sim c, step id = Some sim -> (sim c).(zoom) <> 0%R;
  step_center : forall id sim c, step id = Some sim -> (sim c).(center) == c}.

Global Instance da_Setoid : Setoid demonic_action := {|
  equiv := fun (da1 da2 : demonic_action) =>
           (forall id, opt_eq (equiv ==> equiv)%signature (da1.(step) id) (da2.(step) id)) /\
           (forall b : B, da1.(relocate_byz) b == da2.(relocate_byz) b) |}.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros da1 da2 [Hda1 Hda2]. repeat split; repeat intro; try symmetry; auto.
  specialize (Hda1 id). destruct (step da1 id), (step da2 id); trivial.
  intros x y Hxy. simpl in Hda1. intro. symmetry in Hxy |- *. apply Hda1 in Hxy. apply Hxy.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4]. repeat split; intros; try etransitivity; eauto.
  specialize (Hda1 id). specialize (Hda3 id).
  destruct (step da1 id), (step da2 id), (step da3 id); simpl in *; trivial.
  - simpl in *. intros x y Hxy z. rewrite (Hda1 _ _ (reflexivity x) z). now apply Hda3.
  - elim Hda1.
Defined.

Global Instance step_da_compat : Proper (equiv ==> Logic.eq ==> opt_eq (equiv ==> equiv)) step.
Proof. intros da1 da2 [Hda1 Hda2] p1 p2 Hp. subst. apply Hda1. Qed.

Global Instance relocate_byz_compat : Proper (equiv ==> Logic.eq ==> equiv) relocate_byz.
Proof. intros [] [] Hda b1 b2 Hb. subst. destruct Hda as [Hda1 Hda2]. simpl in *. apply (Hda2 b2). Qed.

Lemma da_eq_step_None : forall da1 da2, da1 == da2 -> forall id, step da1 id = None <-> step da2 id = None.
Proof.
intros da1 da2 Hda id.
assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition idle da := List.filter
  (fun id => match step da id with Some _ => false | None => true end)
  names.

Definition active da := List.filter
  (fun id => match step da id with Some _ => true | None => false end)
  names.

Global Instance idle_compat : Proper (equiv ==> Logic.eq) idle.
Proof.
intros da1 da2 Hda. unfold idle. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id) eqn:Hstep1, (step da2 id) eqn:Hstep2.
  - apply IHl.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - f_equal. apply IHl.
Qed.

Global Instance active_compat : Proper (equiv ==> Logic.eq) active.
Proof.
intros da1 da2 Hda. unfold active. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id) eqn:Hstep1, (step da2 id) eqn:Hstep2.
  - f_equal. apply IHl.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - apply IHl.
Qed.

Lemma idle_spec : forall da id, List.In id (idle da) <-> step da id = None.
Proof.
intros da id. unfold idle. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate.
apply In_names.
Qed.

Lemma active_spec : forall da id, List.In id (active da) <-> step da id <> None.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate.
apply In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Streams.t demonic_action.

Global Instance demon_Setoid : Setoid demon := {| equiv := Streams.eq equiv |}.

Global Instance demon_hd_compat : Proper (equiv ==> equiv) (@Streams.hd _) := Streams.hd_compat _.
Global Instance demon_tl_compat : Proper (equiv ==> equiv) (@Streams.tl _) := Streams.tl_compat _.

(** ** Fairness *)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne g (d : demon) : Prop :=
  | NowFair : step (Streams.hd d) g ≠ None → LocallyFairForOne g d
  | LaterFair : step (Streams.hd d) g = None → LocallyFairForOne g (Streams.tl d) → LocallyFairForOne g d.

Definition Fair : demon -> Prop := Streams.forever (fun d => ∀ g, LocallyFairForOne g d).

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k, step (Streams.hd d) g <> None -> Between g h d k
| kReduce : forall k, step (Streams.hd d) g = None -> step (Streams.hd d) h <> None ->
                      Between g h (Streams.tl d) k -> Between g h d (S k)
| kStall : forall k, step (Streams.hd d) g = None -> step (Streams.hd d) h = None ->
                     Between g h (Streams.tl d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
Definition kFair k : demon -> Prop := Streams.forever (fun d => forall g h, Between g h d k).

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, d1 == d2 -> LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
intros g da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda.
+ constructor 1. rewrite da_eq_step_None; try eassumption. now f_equiv.
+ constructor 2.
  - rewrite da_eq_step_None; try eassumption. now f_equiv.
  - apply IHHfair. now f_equiv.
Qed.

Global Instance LocallyFairForOne_compat : Proper (eq ==> equiv ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Global Instance Fair_compat : Proper (equiv ==> iff) Fair.
Proof. apply Streams.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall g h k d1 d2, d1 == d2 -> Between g h d1 k -> Between g h d2 k.
Proof.
intros g h k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
+ constructor 1. rewrite <- da_eq_step_None; try eassumption. now f_equiv.
+ constructor 2.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - apply IHbet. now f_equiv.
+ constructor 3.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - apply IHbet. now f_equiv.
Qed.

Global Instance Between_compat : Proper (eq ==> eq ==> equiv ==> eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Global Instance kFair_compat : Proper (eq ==> equiv ==> iff) kFair.
Proof. intros k ? ?. subst. apply Streams.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof. intros g h d k Hg. induction Hg; now constructor. Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof. intros g d k Hd. induction Hd; now constructor. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Streams.forever_impl_compat. intros. eauto using (@Between_LocallyFair g _ g). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
intros g h d k Hd. induction Hd; intros k' Hk.
+ now constructor 1.
+ destruct k'.
  - now inversion Hk.
  - constructor 2; assumption || now (apply IHHd; auto with arith).
+ constructor 3; assumption || now (apply IHHd; auto with arith).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; destruct H.
- intros. now apply Between_mon with k.
- now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall g h, (Streams.hd d).(step) g = None <-> (Streams.hd d).(step) h = None.
Proof.
intros d Hd g h. destruct Hd as [Hd _]. split; intro H.
- assert (Hg := Hd g h). inversion Hg. contradiction. assumption.
- assert (Hh := Hd h g). inversion Hh. contradiction. assumption.
Qed.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the step function
  of the demon never returns None. *)


(** A demon is fully synchronous at the first step. *)
Definition FullySynchronousInstant : demon -> Prop := Streams.instant (fun da => forall g, step da g ≠ None).

(** A demon is fully synchronous if it is fully synchronous at all step. *)
Definition FullySynchronous : demon -> Prop := Streams.forever FullySynchronousInstant.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_0Fair: ∀ d, FullySynchronous d → kFair 0 d.
Proof. apply Streams.forever_impl_compat. intros s Hs g. constructor. apply Hs. Qed.

Corollary fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof. intros. now eapply kFair_Fair, fully_synchronous_implies_0Fair. Qed.

(** ** One step executions *)

(** [round r da conf] return the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)

Definition round r (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    match da.(step) id with (** first see whether the robot is activated *)
      | None => config id (** If id is not activated, do nothing *)
      | Some sim => (** id is activated and [sim (conf id)] is its similarity *)
        match id with
          | Byz b => da.(relocate_byz) b (* byzantine robots are relocated by the demon *)
          | Good g =>  (* change of frame of reference *)
            let frame_change := sim (config id) in
            (* local configuration seen by g *)
            let local_config : configuration := map_config frame_change config in
            (* apply r on spectrum + back to demon ref. *)
            frame_change⁻¹ (r (spect_from_config local_config))
        end
    end.

Global Instance round_compat : Proper (@equiv robogram _ ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try now elim Hstep.
* f_equiv.
  + do 2 f_equiv. apply Hstep, Hconf.
  + transitivity (r1 (spect_from_config (map_config (s0 (conf2 (Good g))) conf2))).
    - apply pgm_compat, spect_from_config_compat, map_config_compat; trivial; [].
      cbn in *. intros x y Hxy. f_equiv; trivial; []. intro z. apply Hstep, Hconf.
    - apply Hr.
* rewrite Hda. reflexivity.
Qed.

(** A third subset of robots, moving ones *)
Definition moving (r : robogram) da config := List.filter
  (fun id => if equiv_dec (round r da config id) (config id) then false else true)
  names.

Global Instance moving_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) moving.
Proof.
intros r1 r2 Hr da1 da2 Hda c1 c2 Hc. unfold moving.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (equiv_dec (round r1 da1 c1 id) (c1 id)) as [Heq1 | Heq1],
           (equiv_dec (round r2 da2 c2 id) (c2 id)) as [Heq2 | Heq2].
  + apply IHl.
  + elim Heq2. transitivity (round r1 da1 c1 id).
    - symmetry. now apply round_compat.
    - rewrite Heq1. apply Hc.
  + elim Heq1. transitivity (round r2 da2 c2 id).
    - now apply round_compat.
    - rewrite Heq2. symmetry. apply Hc.
  + f_equal. apply IHl.
Qed.

Lemma moving_spec : forall r da config id,
  List.In id (moving r da config) <-> round r da config id =/= config id.
Proof.
intros r da config id. unfold moving. rewrite List.filter_In.
split; intro H.
+ destruct H as [_ H].
  destruct (equiv_dec (round r da config id) (config id)) as [_ | Hneq]; intuition.
+ split.
  - apply In_names.
  - destruct (equiv_dec (round r da config id) (config id)) as [Heq | _]; intuition.
Qed.

Lemma moving_active : forall r da config, List.incl (moving r da config) (active da).
Proof.
intros r config da id. rewrite moving_spec, active_spec. intro Hmove.
unfold round in Hmove. destruct (step config id).
- discriminate.
- now elim Hmove.
Qed.

(** Some results *)

Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof.
intros r da config Hmove id.
destruct (equiv_dec (round r da config id) (config id)) as [Heq | Heq]; trivial.
rewrite <- moving_spec, Hmove in Heq. inversion Heq.
Qed.

Corollary no_active_same_config :
  forall (r : robogram) da conf, active da = List.nil -> equiv (round r da conf) conf.
Proof.
intros r da conf Hactive.
assert (moving r da conf = List.nil). { apply incl_nil. rewrite <- Hactive. apply moving_active. }
now apply no_moving_same_config.
Qed.


(** [execute r d pos] returns an (infinite) execution from an initial global
    position [pos], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram) : demon → configuration → execution :=
  cofix execute d config :=
  Streams.cons config (execute (Streams.tl d) (round r (Streams.hd d) config)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (config : configuration),
  Streams.tl (execute r d config) = execute r (Streams.tl d) (round r (Streams.hd d) config).
Proof. intros. destruct d. reflexivity. Qed.

Global Instance execute_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor.
+ simpl. assumption.
+ apply proof; clear proof.
  - now inversion H.
  - apply round_compat; trivial. now inversion H.
Qed.

End RigidFormalism.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
