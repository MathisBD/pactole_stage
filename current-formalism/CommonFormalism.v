(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.    *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Pactole.Util.Bijection.
Require Pactole.Util.Stream.
Require Import Pactole.Robots.
Require Import Pactole.RobotInfo.
Require Import Pactole.Configurations.
Require Import Pactole.Spectra.Definition.
Import Pactole.Util.Bijection.Notations.


Section Formalism.

Context {loc info : Type}.
Context `{IsLocation loc info}.
Context `{Names}.
Context {Spect : Spectrum loc info}.

Local Notation configuration := (@configuration info _ _ _ _).
Local Notation spectrum := (@spectrum loc info _ _ _ _ _ _ Spect).

(** **  Robograms and Executions  **)

(** Good robots have a common program, which we call a [robogram]. *)
Record robogram := {
  pgm :> spectrum -> loc;
  pgm_compat : Proper (equiv ==> equiv) pgm}.

Global Instance robogram_Setoid : Setoid robogram := {|
  equiv := fun r1 r2 => forall s, pgm r1 s == pgm r2 s |}.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Global Instance pgm_full_compat : Proper (equiv ==> equiv ==> equiv) pgm.
Proof. intros r1 r2 Hr s1 s2 Hs. rewrite (Hr s1). now apply pgm_compat. Qed.

(** Executions are simply streams of configurations. *)
Definition execution := Stream.t configuration.

(** ** Demonic schedulers *)

(** A [demonic_action] performs four things:
    - it selects which robots are activated,
    - it moves all activated byzantine robots as it wishes,
    - in the compute phase, it sets the referential of all activated good robots,
    - in the move phase, it decides what changes in their states. *)
(* The byzantine robots are not always activated because fairness depends on all robots, not only good ones. *)
Record demonic_action := {
  (** Select which robots are activated *)
  activate : configuration -> ident -> bool;
  (** Update the state of (activated) byzantine robots *)
  relocate_byz : configuration -> B -> info;
  (** Local referential for (activated) good robots in the compute phase *)
  change_frame : configuration -> G -> Bijection.bijection loc;
  (** Update the state of (activated) good robots in the move phase  *)
  update_state : configuration -> G -> loc -> info;
  (** Compatibility properties *)
  activate_compat : Proper (equiv ==> Logic.eq ==> equiv) activate;
  relocate_byz_compat : Proper (equiv ==> Logic.eq ==> equiv) relocate_byz;
  change_frame_compat : Proper (equiv ==> Logic.eq ==> equiv) change_frame;
  update_state_compat : Proper (equiv ==> Logic.eq ==> equiv ==> equiv) update_state }.

(* These constraint will only appear while specializing the models.
  option ((loc -> similarity loc) (* change of referential *)
                               * R); (* travel ratio (rigid or flexible moves) *)
  step_compat : Proper (Logic.eq ==> opt_eq ((equiv ==> equiv) * (@eq R))) step;
  step_zoom :  forall id sim c, step id = Some sim -> (fst sim c).(zoom) <> 0%R;
  step_center : forall id sim c, step id = Some sim -> (fst sim c).(center) == c;
  step_flexibility : forall id sim, step id = Some sim -> (0 <= snd sim <= 1)%R}.
*)
Global Instance da_Setoid : Setoid demonic_action := {|
  equiv := fun (da1 da2 : demonic_action) =>
           (forall config id, da1.(activate) config id == da2.(activate) config id)
        /\ (forall config b, da1.(relocate_byz) config b == da2.(relocate_byz) config b)
        /\ (forall config g, da1.(change_frame) config g == da2.(change_frame) config g)
        /\ (forall config g pt, da1.(update_state) config g pt == da2.(update_state) config g pt) |}.
Proof. split.
+ intuition.
+ intros da1 da2 [? [? [? ?]]]. repeat split; intros; symmetry; auto.
+ intros da1 da2 da3 [? [? [? ?]]] [? [? [? ?]]]. repeat split; intros; etransitivity; eauto.
Defined.

Global Instance activate_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) activate.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply activate_compat. Qed.

Global Instance relocate_byz_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) relocate_byz.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply relocate_byz_compat. Qed.

Global Instance change_frame_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) change_frame.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply change_frame_compat. Qed.

Global Instance update_state_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv ==> equiv) update_state.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply update_state_compat. Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition active da config := List.filter (activate da config) names.

Definition idle da config := List.filter (fun id => negb (activate da config id)) names.

Global Instance active_compat : Proper (equiv ==> equiv ==> Logic.eq) active.
Proof.
intros da1 da2 Hda config1 config2 Hconfig.
unfold active. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 config1 id) eqn:Hactivate1, (activate da2 config2 id) eqn:Hactivate2.
  - f_equal. apply IHl.
  - rewrite Hda, Hconfig, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hconfig, Hactivate2 in Hactivate1. discriminate.
  - apply IHl.
Qed.

Global Instance idle_compat : Proper (equiv ==> equiv ==> Logic.eq) idle.
Proof.
intros da1 da2 Hda config1 config2 Hconfig.
unfold idle. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 config1 id) eqn:Hactivate1, (activate da2 config2 id) eqn:Hactivate2.
  - apply IHl.
  - rewrite Hda, Hconfig, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hconfig, Hactivate2 in Hactivate1. discriminate.
  - simpl. f_equal. apply IHl.
Qed.

Lemma idle_spec : forall da config id, List.In id (idle da config) <-> activate da config id = false.
Proof.
intros da config id. unfold idle. rewrite List.filter_In.
destruct (activate da config id); intuition; try discriminate; [].
apply In_names.
Qed.

Lemma active_spec : forall da config id, List.In id (active da config) <-> activate da config id = true.
Proof.
intros da config id. unfold active. rewrite List.filter_In.
destruct (activate da config id); intuition; try discriminate; [].
apply In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

(** **  One step executions  **)

Typeclasses eauto := 5.

(** [round r da config] returns the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [config] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(relocate_byz)]
    is used for byzantine robots.
    
    As this is a general setting similarities preserve distance ratios, we can perform the multiplication by [mv_ratio]
    either in the local frame or in the global one. *)
Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let state := config id in
    if da.(activate) config id                (* first see whether the robot is activated *)
    then
      match id with
        | Byz b => da.(relocate_byz) config b (* byzantine robots are relocated by the demon *)
        | Good g =>
          (* change the frame of reference *)
          let new_frame := da.(change_frame) config g in
          let local_config := map_config (app new_frame) config in
          (* apply r on spectrum *)
          let local_target := r (spect_from_config local_config (get_location (local_config (Good g)))) in
          (* return to the global frame of reference *)
          let global_target := new_frame ⁻¹ local_target in
          (* the demon performs the actual update of the robot state *)
          da.(update_state) config g global_target
        end
    else state.


Global Instance round_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda config1 config2 Hconfig id.
unfold round. rewrite Hda, Hconfig. destruct_match.
* (* active robot *)
  destruct id as [g | b].
  + (* good robot *)
    do 4 f_equiv; trivial; [|].
    - apply map_config_compat; trivial; []. apply app_compat. now do 2 f_equiv.
    - apply get_location_compat, map_config_compat; trivial; []. apply app_compat. now do 2 f_equiv.
  + (* byzantine robot *)
    now f_equiv.
* (* inactive robot *)
  apply Hconfig.
Qed.

(** A third subset of robots, moving ones *)
Definition moving r da config := List.filter
  (fun id => if round r da config id =?= config id then false else true)
  names.

Global Instance moving_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) moving.
Proof.
intros r1 r2 Hr da1 da2 Hda c1 c2 Hc. unfold moving.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (round r1 da1 c1 id =?= c1 id) as [Heq1 | Heq1],
           (round r2 da2 c2 id =?= c2 id) as [Heq2 | Heq2].
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
split; intro Hin.
+ destruct Hin as [_ Hin].
  destruct (round r da config id =?= config id) as [_ | Hneq]; intuition.
+ split.
  - apply In_names.
  - destruct (round r da config id =?= config id) as [Heq | _]; intuition.
Qed.

Lemma moving_active : forall r da config, List.incl (moving r da config) (active da config).
Proof.
intros r config da id. rewrite moving_spec, active_spec.
unfold round. destruct_match; intuition.
Qed.

(** Some results *)

Lemma no_active_same_config : forall r da config,
  active da config = List.nil -> round r da config == config.
Proof.
intros r da config Hactive.
assert (Hfalse : forall id, activate da config id = false).
{ intro id. destruct (activate da config id) eqn:Heq; trivial; []. exfalso.
  rewrite <- active_spec, Hactive in Heq. intuition. }
intro id. unfold round. now rewrite (Hfalse id).
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
Proof.
intros r1 r2 Hr. coinduction proof.
- simpl. assumption.
- now f_equiv.
- apply round_compat; trivial. now f_equiv.
Qed.

(** **  Fairness  **)

(* FIXME: these definitions are very likely wrong because of the qunitification on config. *)
(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne id (d : demon) : Prop :=
  | NowFair : forall config, activate (Stream.hd d) config id == true -> LocallyFairForOne id d
  | LaterFair : forall config, activate (Stream.hd d) config id = false ->
                LocallyFairForOne id (Stream.tl d) -> LocallyFairForOne id d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ id, LocallyFairForOne id d).

(** [Between id id' d] means that [id] will be activated before at most [k]
    steps of [id'] in demon [d]. *)
Inductive Between id id' (d : demon) : nat -> Prop :=
| kReset : forall k, forall config, activate (Stream.hd d) config id = true -> Between id id' d k
| kReduce : forall k, forall config, activate (Stream.hd d) config id = false ->
            activate (Stream.hd d) config id' = true -> Between id id' (Stream.tl d) k -> Between id id' d (S k)
| kStall : forall k, forall config, activate (Stream.hd d) config id = false ->
           activate (Stream.hd d) config id' = false -> Between id id' (Stream.tl d) k -> Between id id' d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall id id', Between id id' d k).

Lemma LocallyFairForOne_compat_aux : forall id d1 d2, d1 == d2 -> LocallyFairForOne id d1 -> LocallyFairForOne id d2.
Proof.
intros id da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda.
+ constructor 1 with config. now rewrite <- Hda.
+ constructor 2 with config.
  - now rewrite <- Hda.
  - apply IHHfair. now f_equiv.
Qed.

Global Instance LocallyFairForOne_compat : Proper (Logic.eq ==> equiv ==> iff) LocallyFairForOne.
Proof.
intros ? ? ? ? ? Heq. subst. split; intro.
- eapply LocallyFairForOne_compat_aux; eauto.
- symmetry in Heq. eapply LocallyFairForOne_compat_aux; eauto.
Qed.

Global Instance Fair_compat : Proper (equiv ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall id id' k d1 d2, d1 == d2 -> Between id id' d1 k -> Between id id' d2 k.
Proof.
intros id id' k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
+ constructor 1 with config. now rewrite <- Heq.
+ constructor 2 with config.
  - now rewrite <- Heq.
  - now rewrite <- Heq.
  - apply IHbet. now f_equiv.
+ constructor 3 with config.
  - now rewrite <- Heq.
  - now rewrite <- Heq.
  - apply IHbet. now f_equiv.
Qed.

Global Instance Between_compat : Proper (Logic.eq ==> Logic.eq ==> equiv ==> Logic.eq ==> iff) Between.
Proof.
intros ? ? ? ? ? ? ? ? Heq ? ? ?. subst. split; intro.
- now eapply Between_compat_aux; eauto.
- symmetry in Heq. now eapply Between_compat_aux; eauto.
Qed.

Global Instance kFair_compat : Proper (Logic.eq ==> equiv ==> iff) kFair.
Proof. intros k ? ?. subst. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_LocallyFair : forall id (d : demon) id' k,
  Between id id' d k -> LocallyFairForOne id d.
Proof. intros id id' d k Hg. now induction Hg; econstructor; eauto. Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall id (d : demon) k, LocallyFairForOne id d -> Between id id d k.
Proof. intros id d k Hd. induction Hd; now econstructor; eauto. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros ? ? id. eauto using (@Between_LocallyFair id _ id). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall id id' (d : demon) k,
  Between id id' d k -> forall k', (k <= k')%nat -> Between id id' d k'.
Proof.
intros id id' d k Hd. induction Hd; intros k' Hk.
+ now constructor 1 with config.
+ destruct k'.
  - now inversion Hk.
  - constructor 2 with config; assumption || now (apply IHHd; auto with arith).
+ constructor 3 with config; assumption || now (apply IHHd; auto with arith).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; match goal with H : kFair _ _ |- _ => destruct H end.
- intros. now apply Between_mon with k.
- now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall config id id', (Stream.hd d).(activate) config id = (Stream.hd d).(activate) config id'.
Proof.
intros d Hd config id id'. destruct Hd as [Hd _].
assert (Hg := Hd id id'). assert (Hh := Hd id' id).
inv Hg; inv Hh.
Abort. (* FIXME: fails because the definition of fair is likely incorrect *)

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the activate function
  of the demon never returns None. *)


(** A demon is fully synchronous at the first step. *)
Definition FullySynchronousInstant : demon -> Prop := Stream.instant (fun da => forall config g, activate da config g = true).

(** A demon is fully synchronous if it is fully synchronous at all step. *)
Definition FullySynchronous : demon -> Prop := Stream.forever FullySynchronousInstant.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_0Fair: ∀ d, FullySynchronous d → kFair 0 d.
Proof. apply Stream.forever_impl_compat. intros s Hs id id'. econstructor. apply Hs. Admitted. (* FIXME *)

Corollary fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof. intros. now eapply kFair_Fair, fully_synchronous_implies_0Fair. Qed.

End Formalism.
