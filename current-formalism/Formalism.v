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
Require Import Pactole.Util.Bijection.
Require Pactole.Util.Stream.
Require Import Pactole.Robots.
Require Import Pactole.RobotInfo.
Require Import Pactole.Configurations.
Require Import Pactole.Spectra.Definition.
Import Pactole.Util.Bijection.Notations.


Typeclasses eauto := 5.


Section Formalism.

Context {loc info : Type}.
Variables T1 T2 : Type.
Context `{EqDec loc} `{EqDec info}.
Context {Loc : IsLocation loc info}.
Context `{Names}.
Context {Spect : Spectrum loc info}.

Local Notation configuration := (@configuration info _ _ _ _).
Local Notation spectrum := (@spectrum loc info _ _ _ _ _ _ Spect).

(** **  Robograms and Executions  **)

(** Good robots have a common program, which we call a [robogram]. *)
Record robogram := {
  pgm :> spectrum -> loc; (* TODO: switch [loc] for [info] as a robogram can upate its memory, etc. *)
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
    - in the move phase, it makes some choices about how the robots' states should be updated.
    
    Therefore, it can make choices at two places: while computing the local frame of reference for a robot
    and while updating robot states.  These choice points will be represented explicitely as demon choices. *)

(** A [frame_choice] represents the choices made by the demon to compute the spectrum.
    It must at least contain at bijection to compute the change of frame of reference.  *)
Class frame_choice `{IsLocation loc info} := {
  frame_choice_bijection : T1 -> bijection loc;
  frame_choice_Setoid :> Setoid T1;
  frame_choice_bijection_compat :> Proper (equiv ==> equiv) frame_choice_bijection }.
Global Existing Instance frame_choice_bijection_compat.

(** An [update_choice] represents the choices the demon makes after a robot decides where it wants to go. *)
Class update_choice := {
  update_choice_Setoid :> Setoid T2;
  update_choice_EqDec :> EqDec update_choice_Setoid }.

(** These choices are then used by an update function that depends on the model. *)
Class update_function `{IsLocation loc info} `{update_choice} := {
  update :> configuration -> G -> loc -> T2 -> info;
  update_compat :> Proper (equiv ==> Logic.eq ==> equiv ==> equiv ==> equiv) update }.

Context `{@frame_choice _ _ _ _ _}.
Context `{update_choice}.
Context `{@update_function _ _ _ _ _ _}.

(* NB: The byzantine robots are not always activated because fairness depends on all robots, not only good ones. *)
Record demonic_action := {
  (** Select which robots are activated *)
  activate : ident -> bool;
  (** Update the state of (activated) byzantine robots *)
  relocate_byz : configuration -> B -> info;
  (** Local referential for (activated) good robots in the compute phase *)
  change_frame : configuration -> G -> T1;
  (** Update the state of (activated) good robots in the move phase  *)
  choose_update : configuration -> G -> loc -> T2;
  (** Compatibility properties *)
  activate_compat : Proper (Logic.eq ==> equiv) activate;
  relocate_byz_compat : Proper (equiv ==> Logic.eq ==> equiv) relocate_byz;
  change_frame_compat : Proper (equiv ==> Logic.eq ==> equiv) change_frame;
  choose_update_compat : Proper (equiv ==> Logic.eq ==> equiv ==> equiv) choose_update }.


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
           (forall id, da1.(activate) id == da2.(activate) id)
        /\ (forall config b, da1.(relocate_byz) config b == da2.(relocate_byz) config b)
        /\ (forall config g, da1.(change_frame) config g == da2.(change_frame) config g)
        /\ (forall config g pt, da1.(choose_update) config g pt == da2.(choose_update) config g pt) |}.

Proof. split.
+ intuition.
+ intros da1 da2 [? [? [? ?]]]. repeat split; intros; symmetry; auto.
+ intros da1 da2 da3 [? [? [? ?]]] [? [? [? ?]]]. repeat split; intros; etransitivity; eauto.
Defined.

Global Instance activate_da_compat : Proper (equiv ==> Logic.eq ==> equiv) activate.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply activate_compat. Qed.

Global Instance relocate_byz_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) relocate_byz.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply relocate_byz_compat. Qed.

Global Instance change_frame_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv) change_frame.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply change_frame_compat. Qed.

Global Instance choose_update_da_compat : Proper (equiv ==> equiv ==> Logic.eq ==> equiv ==> equiv) choose_update.
Proof. intros ? ? Hda. repeat intro. now etransitivity; apply Hda || apply choose_update_compat. Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition active da := List.filter (activate da) names.

Definition idle da := List.filter (fun id => negb (activate da id)) names.

Global Instance active_compat : Proper (equiv ==> Logic.eq) active.
Proof.
intros da1 da2 Hda.
unfold active. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 id) eqn:Hactivate1, (activate da2 id) eqn:Hactivate2.
  - f_equal. apply IHl.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - apply IHl.
Qed.

Global Instance idle_compat : Proper (equiv ==> Logic.eq) idle.
Proof.
intros da1 da2 Hda.
unfold idle. induction names as [| id l]; simpl.
+ reflexivity.
+ destruct (activate da1 id) eqn:Hactivate1, (activate da2 id) eqn:Hactivate2.
  - apply IHl.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - rewrite Hda, Hactivate2 in Hactivate1. discriminate.
  - simpl. f_equal. apply IHl.
Qed.

Lemma idle_spec : forall da id, List.In id (idle da) <-> activate da id = false.
Proof.
intros da id. unfold idle. rewrite List.filter_In.
destruct (activate da id); intuition; try discriminate; [].
apply In_names.
Qed.

Lemma active_spec : forall da id, List.In id (active da) <-> activate da id = true.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (activate da id); intuition; try discriminate; [].
apply In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

(** **  One step executions  **)

(** [round r da config] returns the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [config] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(relocate_byz)]
    is used for byzantine robots.
    
    As this is a general setting similarities preserve distance ratios, we can perform the multiplication
    by [mv_ratio] either in the local frame or in the global one. *)
Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let state := config id in
    if da.(activate) id                       (* first see whether the robot is activated *)
    then
      match id with
        | Byz b => da.(relocate_byz) config b (* byzantine robots are relocated by the demon *)
        | Good g =>
          (* change the frame of reference *)
          let new_frame := frame_choice_bijection (da.(change_frame) config g) in
          let local_config := map_config (app new_frame) config in
          let local_pos := get_location (local_config (Good g)) in
          (* compute the spectrum *)
          let spect := spect_from_config local_config local_pos in
          (* apply r on spectrum *)
          let local_target := r spect in
          (* return to the global frame of reference *)
          let global_target := new_frame ⁻¹ local_target in
          (* the demon chooses how to perform the state update *)
          let choice := da.(choose_update) config g global_target in
          (* the actual update of the robot state is performed by the update function *)
          update config g global_target choice
        end
    else state.


Global Instance round_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda config1 config2 Hconfig id.
unfold round. rewrite Hda. destruct_match.
* (* active robot *)
  destruct id as [g | b].
  + (* good robot *)
    apply update_compat; try apply choose_update_da_compat; trivial; [|];
    do 2 f_equiv; try apply frame_choice_bijection_compat; f_equiv; trivial;
    solve [ apply map_config_compat; trivial; []; apply app_compat; f_equiv;
            apply frame_choice_bijection_compat; now do 2 f_equiv
          | apply get_location_compat, map_config_compat; trivial; []; apply app_compat; f_equiv;
            apply frame_choice_bijection_compat; now do 2 f_equiv ].
  + (* byzantine robot *)
    now f_equiv.
* (* inactive robot *)
  apply Hconfig.
Qed.

(** A third subset of robots, moving ones *)
Definition moving r da config :=
  List.filter
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

Lemma moving_active : forall r da config, List.incl (moving r da config) (active da).
Proof.
intros r config da id. rewrite moving_spec, active_spec.
unfold round. destruct_match; intuition.
Qed.

(** Some results *)

Lemma no_active_same_config : forall r da config,
  active da = List.nil -> round r da config == config.
Proof.
intros r da config Hactive.
assert (Hfalse : forall id, activate da id = false).
{ intro id. destruct (activate da id) eqn:Heq; trivial; []. exfalso.
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

(* FIXME: these definitions are very likely wrong because of the quantification on config. *)
(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne id (d : demon) : Prop :=
  | NowFair : activate (Stream.hd d) id == true -> LocallyFairForOne id d
  | LaterFair : activate (Stream.hd d) id = false ->
                LocallyFairForOne id (Stream.tl d) -> LocallyFairForOne id d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ id, LocallyFairForOne id d).

(** [Between id id' d] means that [id] will be activated before at most [k]
    steps of [id'] in demon [d]. *)
Inductive Between id id' (d : demon) : nat -> Prop :=
| kReset : forall k, activate (Stream.hd d) id = true -> Between id id' d k
| kReduce : forall k, activate (Stream.hd d) id = false ->
                      activate (Stream.hd d) id' = true ->
                      Between id id' (Stream.tl d) k -> Between id id' d (S k)
| kStall : forall k, activate (Stream.hd d) id = false ->
                     activate (Stream.hd d) id' = false ->
                     Between id id' (Stream.tl d) k -> Between id id' d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall id id', Between id id' d k).

Lemma LocallyFairForOne_compat_aux : forall id d1 d2,
  d1 == d2 -> LocallyFairForOne id d1 -> LocallyFairForOne id d2.
Proof.
intros id da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda;
constructor; solve [now rewrite <- Hda | apply IHHfair; now f_equiv].
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
intros id id' k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq;
constructor; solve [now rewrite <- Heq | apply IHbet; now f_equiv].
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
Proof. intros * Hg. induction Hg; now constructor; trivial; firstorder. Qed.

(** A robot is never activated before itself with a fair demon!
    The fairness hypothesis is necessary, otherwise the robot may never be activated. *)
Lemma Between_same :
  forall id (d : demon) k, LocallyFairForOne id d -> Between id id d k.
Proof. intros id d k Hd. induction Hd; now econstructor; eauto. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros ? ? id. eauto using (@Between_LocallyFair id _ id). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mono : forall id id' (d : demon) k,
  Between id id' d k -> forall k', (k <= k')%nat -> Between id id' d k'.
Proof.
intros id id' d k Hd. induction Hd; intros k' Hk; auto using Between; [].
destruct k'.
- now inversion Hk.
- constructor; assumption || now (apply IHHd; auto with arith).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mono : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; match goal with H : kFair _ _ |- _ => destruct H end.
- intros. now apply Between_mono with k.
- now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall id id', (Stream.hd d).(activate) id = (Stream.hd d).(activate) id'.
Proof.
intros d Hd id id'. destruct Hd as [Hd _].
assert (Hg := Hd id id'). assert (Hh := Hd id' id).
inv Hg; inv Hh;
repeat match goal with
  | H : forall c : configuration, _ |- _ => specialize (H config)
  | H : _ /\ _ |- _ => destruct H
  | |- _ => congruence
end.
Qed.

(** [FirstMove r d config] gives the number of rounds before one robot moves. *)
Inductive FirstMove r (d : demon) (config : configuration) : Prop :=
  | MoveNow : moving r (Stream.hd d) config <> nil -> FirstMove r d config
  | MoveLater : moving r (Stream.hd d) config = nil ->
                FirstMove r (Stream.tl d) (round r (Stream.hd d) config) -> FirstMove r d config.

Global Instance FirstMove_compat : Proper (equiv ==> equiv ==> equiv ==> iff) FirstMove.
Proof.
intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst.
* revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc.
  + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc.
  + apply MoveLater.
    - now rewrite <- Hr, <- Hd, <- Hc.
    - destruct Hd. now apply IHHfirst, round_compat.
* revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc.
  + apply MoveNow. now rewrite Hr, Hd, Hc.
  + apply MoveLater.
    - now rewrite Hr, Hd, Hc.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat; f_equiv.
Qed.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the activate function
  of the demon never returns None. *)


(** A demon is fully synchronous at the first step. *)
Definition FullySynchronousInstant : demon -> Prop :=
  Stream.instant (fun da => forall g, activate da g = true).

(** A demon is fully synchronous if it is fully synchronous at all step. *)
Definition FullySynchronous : demon -> Prop := Stream.forever FullySynchronousInstant.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_0Fair: ∀ d, FullySynchronous d → kFair 0 d.
Proof. apply Stream.forever_impl_compat. intros s Hs id id'. constructor. apply Hs. Qed.

Corollary fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof. intros. now eapply kFair_Fair, fully_synchronous_implies_0Fair. Qed.

End Formalism.

Arguments update_choice_Setoid {_} {_}.
Arguments update_choice_EqDec {_} {_}.
Arguments update_function {loc} {info} T2 {_} {_} {_} {_} {_} {_} {_}.
Arguments demonic_action {loc} {info} {T1} {T2} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments demon {loc} {info} {T1} {T2} {_} {_} {_} {_} {_} {_} {_} {_}.


Section ChoiceExample.

Context {loc info : Type}.
Context `{EqDec loc} `{EqDec info}.
Context {Loc : IsLocation loc info}.


(** An exemple of first choice: just a bijection *)
Definition FrameChoiceBijection : frame_choice (bijection loc) := {|
  frame_choice_bijection := Datatypes.id;
  frame_choice_Setoid := @bij_Setoid loc _;
  frame_choice_bijection_compat := fun _ _ Heq => Heq |}.

Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.

(* Similarities as a first choice, only inside real metric spaces *)
Definition FirstChoiceSimilarity {RMS : RealMetricSpace loc}
  : @frame_choice loc info (similarity loc) _ _ _ _ _ := {|
  frame_choice_bijection := @sim_f loc _ _ _;
  frame_choice_Setoid := similarity_Setoid loc;
  frame_choice_bijection_compat := f_compat |}.


(** An exemple of second choice: no choice at all. *)
Definition NoChoice : update_choice Datatypes.unit := {|
  update_choice_Setoid := _;
  update_choice_EqDec := _ |}.

(** Combining two choices into one. *)
Definition MergeUpdateChoices A B `{update_choice A} `{update_choice B} : update_choice (A * B) := {|
  update_choice_Setoid := _;
  update_choice_EqDec := _ |}.

End ChoiceExample.
