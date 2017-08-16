(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.


Section RigidFormalism.

Context {loc info : Type}.
Context {Sloc : Setoid loc}.
Context {Eloc : EqDec Sloc}.
Context {Sinfo : Setoid info}.
Context {Einfo : EqDec Sinfo}.
Context {RMS : @RealMetricSpace loc Sloc Eloc}.
Context {Ndef : NamesDef} {N : Names}.
Context {Info : Information loc info}.
Context {Spect : Spectrum loc info}.

(* Notations to avoid typeclass resolution taking forever. *)
Notation configuration := (@configuration loc info _ _ _ _ _ _ _).
Notation robogram := (@robogram loc info _ _ _ _ _ _ _ _).
Notation execution := (@execution loc info _ _ _ _ _ _ _).
Notation map_config := (@map_config loc info _ _ _ _ _ _ _).
Notation app := (@app _ _ _ _ _ _ Info).


(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it wishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : B → loc * info;
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
+ intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto; [].
  specialize (Hda1 id). destruct (step da1 id), (step da2 id); trivial; [].
  intros x y Hxy. simpl in Hda1. symmetry in Hxy |- *. now apply Hda1 in Hxy.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4]. split; intros; try etransitivity; eauto; [].
  specialize (Hda1 id). specialize (Hda3 id).
  destruct (step da1 id), (step da2 id), (step da3 id); simpl in *; trivial; [|].
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
destruct (step da id).
+ split; intros [? ?] || intro; discriminate.
+ repeat split. apply In_names.
Qed. (* BUG?: intuition uses Eqdep.eq_rect_eq *)

Lemma active_spec : forall da id, List.In id (active da) <-> step da id <> None.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate.
apply In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

(** **  Fairness  **)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne id (d : demon) : Prop :=
  | NowFair : step (Stream.hd d) id ≠ None → LocallyFairForOne id d
  | LaterFair : step (Stream.hd d) id = None → LocallyFairForOne id (Stream.tl d) → LocallyFairForOne id d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ id, LocallyFairForOne id d).

(** [Between id id' d] means that [id] will be activated before at most [k]
    steps of [id'] in demon [d]. *)
Inductive Between id id' (d : demon) : nat -> Prop :=
| kReset : forall k, step (Stream.hd d) id <> None -> Between id id' d k
| kReduce : forall k, step (Stream.hd d) id = None -> step (Stream.hd d) id' <> None ->
                      Between id id' (Stream.tl d) k -> Between id id' d (S k)
| kStall : forall k, step (Stream.hd d) id = None -> step (Stream.hd d) id' = None ->
                     Between id id' (Stream.tl d) k -> Between id id' d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall id id', Between id id' d k).

Lemma LocallyFairForOne_compat_aux : forall id d1 d2, d1 == d2 -> LocallyFairForOne id d1 -> LocallyFairForOne id d2.
Proof.
intros id da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda.
+ constructor 1. rewrite da_eq_step_None; try eassumption. now f_equiv.
+ constructor 2.
  - rewrite da_eq_step_None; try eassumption. now f_equiv.
  - apply IHHfair. now f_equiv.
Qed.

Global Instance LocallyFairForOne_compat : Proper (Logic.eq ==> equiv ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Global Instance Fair_compat : Proper (equiv ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall id id' k d1 d2, d1 == d2 -> Between id id' d1 k -> Between id id' d2 k.
Proof.
intros id id' k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
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

Global Instance Between_compat : Proper (Logic.eq ==> Logic.eq ==> equiv ==> Logic.eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Global Instance kFair_compat : Proper (Logic.eq ==> equiv ==> iff) kFair.
Proof. intros k ? ?. subst. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_LocallyFair : forall id (d : demon) id' k,
  Between id id' d k -> LocallyFairForOne id d.
Proof. intros id id' d k Hg. induction Hg; now constructor. Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall id (d : demon) k, LocallyFairForOne id d -> Between id id d k.
Proof. intros id d k Hd. induction Hd; now constructor. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros ? ? id. eauto using (@Between_LocallyFair id _ id). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mono : forall id id' (d : demon) k,
  Between id id' d k -> forall k', (k <= k')%nat -> Between id id' d k'.
Proof.
intros id id' d k Hd. induction Hd; intros k' Hk.
+ now constructor 1.
+ destruct k'.
  - now inversion Hk.
  - constructor 2; assumption || now (apply IHHd; auto with arith).
+ constructor 3; assumption || now (apply IHHd; auto with arith).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mono : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; destruct H.
- intros. now apply Between_mono with k.
- now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall id id', (Stream.hd d).(step) id = None <-> (Stream.hd d).(step) id' = None.
Proof.
intros d Hd id id'. destruct Hd as [Hd _]. split; intro H.
- assert (Hg := Hd id id'). inversion Hg. contradiction. assumption.
- assert (Hh := Hd id' id). inversion Hh. contradiction. assumption.
Qed.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the step function
  of the demon never returns None. *)


(** A demon is fully synchronous at the first step. *)
Definition FullySynchronousInstant : demon -> Prop := Stream.instant (fun da => forall id, step da id ≠ None).

Instance FullySynchronousInstant_compat : Proper (equiv ==> iff) FullySynchronousInstant.
Proof.
unfold FullySynchronousInstant.
intros d1 d2 Hd. apply Stream.instant_compat; trivial; [].
intros da1 da2 Hda. now split; intros Hstep id; rewrite da_eq_step_None; auto.
Qed.

(** A demon is fully synchronous if it is fully synchronous at all steps. *)
Definition FullySynchronous : demon -> Prop := Stream.forever FullySynchronousInstant.

Instance FullySynchronous_compat : Proper (equiv ==> iff) FullySynchronous.
Proof. unfold FullySynchronous. autoclass. Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_0Fair: ∀ d, FullySynchronous d → kFair 0 d.
Proof. apply Stream.forever_impl_compat. intros s Hs g. constructor. apply Hs. Qed.

Corollary fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof. intros. now eapply kFair_Fair, fully_synchronous_implies_0Fair. Qed.

(** **  One step executions  **)

(* FIXME: what to do with the extra information contained in RobotConf? Who should update it? *)
(* FIXME: should the similarity use the full robot info or only its location? *)

(** [round r da config] returns the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [config] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)

Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    match da.(step) id with (** first see whether the robot is activated *)
      | None => config id (** If id is not activated, do nothing *)
      | Some sim => (** id is activated and [sim (config id)] is its similarity *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robots are relocated by the demon *)
        | Good g => (* configuration expressed in the frame of g *)
          let frame_change := sim (fst (config id)) in
          let local_config := map_config frame_change config in
          (* apply r on spectrum + back to demon ref. *)
          (frame_change⁻¹ (r (spect_from_config local_config)),
           app frame_change (snd (config id)))
        end
    end.

Global Instance round_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda config1 config2 Hconfig id.
unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try (now elim Hstep); [|].
* split; cbn [fst snd].
  + f_equiv.
    - do 2 f_equiv. apply Hstep. f_equiv. apply Hconfig.
    - etransitivity; try apply Hr; [].
      apply pgm_compat. f_equiv. apply map_config_compat; trivial; [].
      intros x y Hxy. f_equiv; trivial; []. intro z. apply Hstep, Hconfig.
  + apply app_compat.
    - do 2 f_equiv. apply Hstep. f_equiv. apply Hconfig.
    - f_equiv. apply Hconfig.
* now rewrite Hda.
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

Lemma no_active_same_config : forall r da config,
  active da = List.nil -> round r da config == config.
Proof.
intros r da config Hactive id. split; simpl; unfold round.
+ destruct (step da id) eqn : Heq ; try reflexivity.
  assert (Heq': step da id <> None). intro. rewrite Heq in H. discriminate.
  rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
+ destruct (step da id) eqn : Heq.
  assert (Heq': step da id <> None). intro. rewrite Heq in H. discriminate.
  rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
  reflexivity.
Qed.


(** [execute r d config] returns an (infinite) execution from an initial global
    configuration [config], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram) : demon -> configuration -> execution :=
  cofix execute d config :=
  Stream.cons config (execute (Stream.tl d) (round r (Stream.hd d) config)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (config : configuration),
  Stream.tl (execute r d config) = execute r (Stream.tl d) (round r (Stream.hd d) config).
Proof. intros. destruct d. reflexivity. Qed.

Global Instance execute_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) execute.
Proof. intros r1 r2 Hr. coinduction proof; repeat (trivial; f_equiv). Qed.

End RigidFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
