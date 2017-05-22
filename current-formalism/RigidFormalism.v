(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RealMetricSpace.
Require Pactole.CommonRealFormalism.



Module Make (Location : RealMetricSpace)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableTypeWithApplication(Location))
            (Config : Configuration(Location)(N)(Names)(Info))
            (Spect : Spectrum(Location)(N)(Names)(Info)(Config))
            (Common : CommonRealFormalism.Sig(Location)(N)(Names)(Info)(Config)(Spect)).

Import Common.
Notation "s ⁻¹" := (Sim.inverse s) (at level 99).

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : Names.B → Config.RobotConf;
  step : Names.ident → option (Location.t → Sim.t);
  step_compat : Proper (eq ==> opt_eq (Location.eq ==> Sim.eq)) step;
  step_zoom :  forall id sim c, step id = Some sim -> (sim c).(Sim.zoom) <> R0;
  step_center : forall id sim c, step id = Some sim -> Location.eq (sim c).(Sim.center) c}.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id, opt_eq (Location.eq ==> Sim.eq)%signature (da1.(step) id) (da2.(step) id)) /\
  (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros d1 d2 [H1 H2]. split; repeat intro; try symmetry; auto; [].
  specialize (H1 id). destruct (step d1 id), (step d2 id); trivial.
  intros x y Hxy. simpl in H1. symmetry. apply H1. now symmetry.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. split; intros; try etransitivity; eauto; [].
  specialize (H1 id). specialize (H3 id). destruct (step d1 id), (step d2 id), (step d3 id); simpl in *; trivial.
  - simpl in *. intros x y Hxy. rewrite (H1 _ _ (reflexivity x)). now apply H3.
  - elim H1.
Qed.

Instance step_da_compat : Proper (da_eq ==> eq ==> opt_eq (Location.eq ==> Sim.eq)) step.
Proof. intros da1 da2 [Hd1 Hd2] p1 p2 Hp. subst. apply Hd1. Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_None : forall da1 da2, da_eq da1 da2 -> forall id, step da1 id = None <-> step da2 id = None.
Proof.
intros da1 da2 Hda id.
assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition idle da := List.filter
  (fun id => match step da id with Some _ => false | None => true end)
  Names.names.

Definition active da := List.filter
  (fun id => match step da id with Some _ => true | None => false end)
  Names.names.

Instance idle_compat : Proper (da_eq ==> eq) idle.
Proof.
intros da1 da2 Hda. unfold idle. induction Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id) eqn:Hstep1, (step da2 id) eqn:Hstep2.
  - apply IHl.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - f_equal. apply IHl.
Qed.

Instance active_compat : Proper (da_eq ==> eq) active.
Proof.
intros da1 da2 Hda. unfold active. induction Names.names as [| id l]; simpl.
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
apply Names.In_names.
Qed.

Lemma active_spec : forall da id, List.In id (active da) <-> step da id <> None.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate.
apply Names.In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Streams.t demonic_action.

Definition deq (d1 d2 : demon) : Prop := Streams.eq da_eq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. apply Streams.eq_equiv. apply da_eq_equiv. Qed.

Instance demon_hd_compat : Proper (deq ==> da_eq) (@Streams.hd _) := Streams.hd_compat _.
Instance demon_tl_compat : Proper (deq ==> deq) (@Streams.tl _) := Streams.tl_compat _.

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

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
intros g da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda.
+ constructor 1. rewrite da_eq_step_None; try eassumption. now f_equiv.
+ constructor 2.
  - rewrite da_eq_step_None; try eassumption. now f_equiv.
  - apply IHHfair. now f_equiv.
Qed.

Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. apply Streams.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall g h k d1 d2, deq d1 d2 -> Between g h d1 k -> Between g h d2 k.
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

Instance Between_compat : Proper (eq ==> eq ==> deq ==> eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Instance kFair_compat : Proper (eq ==> deq ==> iff) kFair.
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
  - constructor 2; assumption || now (apply IHHd; omega).
+ constructor 3; assumption || now (apply IHHd; omega).
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

(* FIXME: the Info type should also carry the way to apply similarities on Info.t *)
Definition apply_sim (sim : Sim.t) (infoR : Config.RobotConf) :=
  {| Config.loc := sim (Config.loc infoR);
     Config.info := Info.app sim (Config.info infoR) |}.

Instance apply_sim_compat : Proper (Sim.eq ==> Config.eq_RobotConf ==> Config.eq_RobotConf) apply_sim.
Proof.
intros sim sim' Hsim conf conf' Hconf. unfold apply_sim. hnf. split; simpl.
- apply Hsim, Hconf.
- apply Info.app_compat, Hconf; []. now do 2 f_equiv.
Qed.

Lemma apply_sim_id : (Config.eq_RobotConf ==> Config.eq_RobotConf)%signature (apply_sim Sim.id) Datatypes.id.
Proof.
intros [? ?] [? ?] [? ?]; split; simpl in *.
- assumption.
- now apply Info.app_id.
Qed.

Lemma apply_sim_compose : forall sim1 sim2,
  (Config.eq_RobotConf ==> Config.eq_RobotConf)%signature (apply_sim (Sim.compose sim1 sim2))
                                                          (fun infoR => apply_sim sim1 (apply_sim sim2 infoR)).
Proof.
intros ? ? [? ?] [? ?] [? ?]; split; simpl in *.
- now do 2 f_equiv.
- now apply Info.app_compose.
Qed.


(** [round r da conf] return the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (r : robogram) (da : demonic_action) (conf : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    match da.(step) id with (** first see whether the robot is activated *)
      | None => conf id (** If g is not activated, do nothing *)
      | Some sim => (** g is activated and [sim (conf g)] is its similarity *)
        match id with
        | Byz b => (* byzantine robots are relocated by the demon *)
            {| Config.loc := da.(relocate_byz) b;
               Config.info := Config.info (conf id) |}
        | Good g => (* configuration expressed in the frame of g *)
          let frame_change := sim (conf id) in
          let local_conf := Config.map (apply_sim frame_change) conf in
          (* apply r on spectrum + back to demon ref. *)
          {| Config.loc := frame_change⁻¹ (r (Spect.from_config local_conf));
             Config.info := Config.info (conf id) |}
        end
    end.

Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold req in Hr. unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try now elim Hstep.
* hnf. simpl. split.
  + f_equiv.
    - apply Hstep, Hconf.
    - apply Hr, Spect.from_config_compat, Config.map_compat; trivial. f_equiv. apply Hstep, Hconf.
  + apply Hconf.
* hnf. split; try apply Hconf; []. simpl. f_equiv. rewrite Hda. reflexivity.
Qed.

(** A third subset of robots, moving ones *)
Definition moving r da config := List.filter
  (fun id => if Location.eq_dec (round r da config id) (config id) then false else true)
  Names.names.

Instance moving_compat : Proper (req ==> da_eq ==> Config.eq ==> eq) moving.
Proof.
intros r1 r2 Hr da1 da2 Hda c1 c2 Hc. unfold moving.
induction Names.names as [| id l]; simpl.
* reflexivity.
* destruct (Location.eq_dec (round r1 da1 c1 id) (c1 id)) as [Heq1 | Heq1],
           (Location.eq_dec (round r2 da2 c2 id) (c2 id)) as [Heq2 | Heq2].
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
  List.In id (moving r da config) <-> ~Location.eq (round r da config id) (config id).
Proof.
intros r da config id. unfold moving. rewrite List.filter_In.
split; intro H.
+ destruct H as [_ H].
  destruct (Location.eq_dec (round r da config id) (config id)) as [_ | Hneq]; intuition.
+ split.
  - apply Names.In_names.
  - destruct (Location.eq_dec (round r da config id) (config id)) as [Heq | _]; intuition.
Qed.

Lemma moving_active : forall r da config, List.incl (moving r da config) (active da).
Proof.
intros r config da id. rewrite moving_spec, active_spec. intro Hmove.
unfold round in Hmove. destruct (step config id).
- discriminate.
- now elim Hmove.
Qed.

(** Some results *)

(* no longer true as the state may change even if the robot does not move. *)
Lemma no_moving_same_conf : forall r da config,
  moving r da config = List.nil -> Config.eq (round r da config) config.
Proof.
(* intros r da config Hmove id. hnf. split; simpl.
+ destruct (Location.eq_dec (round r da config id) (config id)) as [Heq | Heq]; trivial; [].
  rewrite <- moving_spec, Hmove in Heq. inversion Heq.
+ hnf. unfold moving in *. unfold round. 
  destruct (step da id) eqn:Hstep. 
  Focus 2. destruct id. destruct (Config.Sta (config (Good g)));intuition.
destruct (Config.Sta (config (Byz b)));intuition. 
  destruct (config id). simpl. *)
Abort.

Lemma no_active_same_conf :
  forall r da conf, active da = List.nil -> Config.eq (round r da conf) conf.
Proof.
intros r da conf Hactive. split; simpl; unfold round.
  + destruct (step da id) eqn : Heq ; try reflexivity.
    assert (Heq': step da id <> None). intro. rewrite Heq in H. discriminate.
    rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
  + destruct (step da id) eqn : Heq. 
    assert (Heq': step da id <> None). intro. rewrite Heq in H. discriminate.
    rewrite <- active_spec, Hactive in Heq'. inversion Heq'. 
    reflexivity. 
Qed.


(** [execute r d pos] returns an (infinite) execution from an initial global
    position [pos], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon → Config.t → execution :=
  cofix execute d config :=
  Streams.cons config (execute (Streams.tl d) (round r (Streams.hd d) config)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (config : Config.t),
  Streams.tl (execute r d config) = execute r (Streams.tl d) (round r (Streams.hd d) config).
Proof. intros. destruct d. reflexivity. Qed.

Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor.
+ simpl. assumption.
+ apply proof; clear proof.
  - now inversion H.
  - apply round_compat; trivial. now inversion H.
Qed.

End Make.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
