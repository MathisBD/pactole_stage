(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain               
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence       
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Spaces.Graph.
Require Import Pactole.Spaces.Isomorphism.
Require Pactole.Util.Stream.
Require Import Pactole.Spectra.Definition.


Section Formalism.
Context (V E info  : Type).
Context {G : Graph V E}.
Context `{Names}.
Context `{Setoid info} `{@EqDec info _}.
Context `{Info : @Information V info _ _ _ _}.

(* Never used if we start from a good config. *)
Axiom e_default : E.

Instance Info2 : Information V (V * info) := @pair_Information V V info _ _ _ _ (Location V) _ _ Info.

Context `{@Spectrum V (V * info) _ _ _ _ _ _ _}.

Notation "s ⁻¹" := (Isomorphism.inverse s) (at level 99).
Notation spectrum := (@spectrum V (V * info) _ _ _ _ Info2 _ _).
Notation configuration := (@configuration V (V * info) _ _ _ _ Info2 _ _ _).


Record robogram := {
  pgm :> spectrum -> V -> V;
  pgm_compat : Proper (equiv ==> equiv ==> equiv) pgm;
  pgm_range : forall spect lpre, exists e, opt_eq (@equiv E _) (Graph.find_edge lpre (pgm spect lpre)) (Some e) }.

(* pgm s l a du dens si l est dans dans s (s[l] > 0)
   si l n'est pas occupée par un robot, on doit revoyer un voisin (à cause de pgm_range). *)

Global Existing Instance pgm_compat.

Instance robogram_Setoid : Setoid robogram := {
  equiv := fun r1 r2 => (equiv ==> equiv ==> equiv)%signature r1 r2 }.
Proof. split.
+ intros [robogram Hrobogram] x y Heq g1 g2 Hg; simpl. now rewrite Hg, Heq.
+ intros ? ? Hr. repeat intro. symmetry. apply Hr; now symmetry.
+ intros r1 r2 r3 Hr12 Hr23. repeat intro. etransitivity; apply Hr12 || apply Hr23; eauto; reflexivity.
Defined.

(** ** Executions *)

(** Now we can [execute] some robogram from a given configuration with a [demon] *)
Definition execution := Stream.t configuration.

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
  and sets the referential of all good robots it selects. *)
Inductive Active_or_Moving :=
  | Moving (dist : bool)                  (* moving ratio, only the model equivalence uses the dist boolean *)
  | Active (iso : @isomorphism V E G).    (* change of referential *)

Instance Active_or_Moving_Setoid : Setoid Active_or_Moving := {
  equiv := fun a1 a2 =>
    match a1, a2 with
      | Moving d1, Moving d2 => d1 = d2
      | Active iso1, Active iso2 => iso1 == iso2
      | _, _ => False
    end }.
Proof. split.
+ now intros [].
+ intros [] [] ?; auto; now symmetry.
+ intros [] [] [] ? ?; congruence || easy || etransitivity; eauto.
Defined.

Instance Active_compat : Proper (equiv ==> equiv) Active.
Proof. intros ? ? ?. simpl. auto. Qed.

(* on a besoin de Rconfig car ça permet de faire la conversion d'un modèle à l'autre *)

Record demonic_action := {
  relocate_byz : B -> (V * (V * info));
  step : ident -> (V * (V * info)) -> Active_or_Moving;
  step_delta : forall g rc iso, step (Good g) rc == Active iso -> fst rc == fst (snd rc);
  step_compat : Proper (eq ==> equiv ==> equiv) step }.
Set Implicit Arguments.

Instance da_Setoid : Setoid demonic_action := {
  equiv := fun da1 da2 => (forall id config, da1.(step) id config == da2.(step) id config)
                       /\ (forall b, da1.(relocate_byz) b == da2.(relocate_byz) b) }.
Proof. split.
+ now split.
+ intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
  split; intros; try etransitivity; eauto.
Defined.

Instance step_da_compat : Proper (equiv ==> eq ==> equiv ==> equiv) step.
Proof.
  intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
  etransitivity.
  - apply Hd1.
  - apply (step_compat da2); auto.
Qed.

Instance relocate_byz_compat : Proper (equiv ==> Logic.eq ==> equiv) relocate_byz.
Proof. intros [] [] [] ? ? ?. subst. auto. Qed.

Lemma da_eq_step_Moving : forall da1 da2, da1 == da2 ->
  forall id config r, step da1 id config == Moving r <-> step da2 id config == Moving r.
Proof.
intros da1 da2 Hda id config r.
now rewrite  (step_da_compat Hda (reflexivity id) (reflexivity config)).
Qed.

Lemma da_eq_step_Active : forall da1 da2, da1 == da2 -> 
  forall id config sim, step da1 id config == Active sim <-> step da2 id config == Active sim.
Proof.
intros da1 da2 Hda id config sim.
now rewrite (step_da_compat Hda (reflexivity id) (reflexivity config)).
Qed.

(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.


(** [round r da conf] return the new configuration of robots (that is a function
  giving the configuration of each robot) from the previous one [conf] by applying
  the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
  is used for byzantine robots. *)
(* TODO: Should we keep the Moving/Active disctinction?
       We could use :
       1) bool in da, 2 states for robots (Loc / MoveTo)
       2) 3 states in da (Compute, Move, Wait), 2 states for robots *)

(* No need of apply_sim: use instead Config.app
 Definition apply_sim (sim : Iso.t) (infoR : Config.RobotConf). *)

Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let rconf := config id in
    let pos := fst rconf in
    match da.(step) id rconf with (** first see whether the robot is activated *)
      | Moving false => rconf
      | Moving true =>
        match id with
          | Good g => let tgt := fst (snd rconf) in (tgt, snd rconf)
          | Byz b => rconf
        end
      | Active iso => (* g is activated with similarity [iso (conf g)] *)
        match id with
          | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
          | Good g =>
            let local_config := map_config iso config in
            let local_target := (r (spect_from_config local_config) (fst (local_config (Good g)))) in
            let target := (iso⁻¹).(iso_V) local_target in
(* This if is unnecessary: with the invariant on da: inside rconf, loc = target *)
(*           if (Location.eq_dec (target) pos) then rconf else *)
            (pos, (target, app iso (snd (snd rconf))))
        end
    end.

Instance round_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold round.
assert (Hrconf : conf1 id == conf2 id) by apply Hconf.
assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
assert (Hsim: step da1 id (conf1 id) == step da1 id (conf2 id)).
{ apply step_da_compat; reflexivity || apply Hrconf. }
destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2;
  destruct (step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
* rewrite Hstep. destruct_match.
  + destruct Hrconf as [_ []]. now repeat split.
  + apply Hrconf.
* rewrite Hstep. destruct_match; apply Hrconf.
* repeat split; simpl.
  + now destruct Hrconf.
  + f_equiv; try (now apply iso_V_compat); [].
    apply Hr.
    - f_equiv. apply map_config_compat; trivial; []. f_equiv. now apply iso_V_compat.
    - f_equiv; try (now apply iso_V_compat); []. apply Hrconf.
  + apply app_compat.
    - f_equiv. now apply iso_V_compat.
    - apply Hrconf.
* rewrite Hda. now destruct (Hconf (Byz b)).
Qed.


(** [execute r d conf] returns an (infinite) execution from an initial global
  configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon -> configuration -> execution :=
  cofix execute d config :=
    Stream.cons config (execute (Stream.tl d) (round r (Stream.hd d) config)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (conf : configuration),
    Stream.tl (execute r d conf) = execute r (Stream.tl d) (round r (Stream.hd d) conf).
Proof. intros. destruct d. reflexivity. Qed.

Instance execute_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) execute.
Proof. intros r1 r2 Hr. coinduction proof; repeat (trivial; f_equiv). Qed.

(** ** Fairness *)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne id (d : demon) : Prop :=
  | ImmediatelyFair : forall iso config,
      step (Stream.hd d) id (config id) == Active iso ->
      LocallyFairForOne id d
  | LaterFair : forall dist config,
      step (Stream.hd d) id (config id) == Moving dist ->
      LocallyFairForOne id (Stream.tl d) ->
      LocallyFairForOne id d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ id, LocallyFairForOne id d).

(** [Between id id' d] means that [id] will be activated before at most [k]
  steps of [id'] in demon [d]. *)
Inductive Between id id' (d : demon) : nat -> Prop :=
  | kReset : forall k config iso,
      step (Stream.hd d) id (config id) == Active iso ->
      Between id id' d k
  | kReduce : forall k config dist iso,
      step (Stream.hd d) id (config id) == Moving dist ->
      step (Stream.hd d) id (config id) == Active iso ->
      Between id id' (Stream.tl d) k -> Between id id' d (S k)
  | kStall : forall k config dist dist',
      step (Stream.hd d) id (config id) == Moving dist ->
      step (Stream.hd d) id' (config id') == Moving dist' ->
      Between id id' (Stream.tl d) k -> Between id id' d k.

Local Hint Constructors LocallyFairForOne Between.

(* k-fair: every robot id is activated within at most k activation of any other robot id' *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall id id', Between id id' d k).

Lemma LocallyFairForOne_compat_aux : forall id d1 d2,
  d1 == d2 -> LocallyFairForOne id d1 -> LocallyFairForOne id d2.
Proof.
intros id d1 d2 Hd Hfair.
revert d2 Hd. induction Hfair; intros d2 Hd.
+ constructor 1 with iso config.
  rewrite da_eq_step_Active; eauto; []. now f_equiv.
+ constructor 2 with dist config.
  - rewrite da_eq_step_Moving; eauto; []. now f_equiv.
  - apply IHHfair; now f_equiv.
Qed.

Instance LocallyFairForOne_compat : Proper (Logic.eq ==> equiv ==> iff) LocallyFairForOne.
Proof. split; intro; subst; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Lemma Fair_compat_aux : forall d1 d2, d1 == d2 -> Fair d1 -> Fair d2.
Proof.
cofix be_fair. intros d1 d2 Heq Hfair.
destruct Hfair as [Hnow Hlater]. constructor.
+ intros. now rewrite <- Heq.
+ eapply be_fair; try eassumption; now f_equiv.
Qed.

Instance Fair_compat : Proper (equiv ==> iff) Fair.
Proof. split; intro; now eapply Fair_compat_aux; eauto. Qed.

Lemma Between_compat_aux : forall id id' k d1 d2, d1 == d2 -> Between id id' d1 k -> Between id id' d2 k.
Proof.
intros id id' k d1 d2 Heq bet.
revert d2 Heq. induction bet; intros d2 Heq.
+ constructor 1 with config iso. rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
+ constructor 2 with config dist iso.
  - rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
  - apply IHbet. now f_equiv.
+ constructor 3 with config dist dist'.
  - rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - apply IHbet. now f_equiv.
Qed.

Instance Between_compat : Proper (Logic.eq ==> Logic.eq ==> equiv ==> Logic.eq ==> iff) Between.
Proof. split; intro; subst; now eapply Between_compat_aux; eauto. Qed.

Lemma kFair_compat_aux : forall k d1 d2, d1 == d2 -> kFair k d1 -> kFair k d2.
Proof.
cofix be_fair. intros k d1 d2 Heq Hkfair.
destruct Hkfair as [Hnow Hlater]. constructor.
+ intros. now rewrite <- Heq.
+ eapply be_fair; try eassumption; now f_equiv.
Qed.

Instance kFair_compat : Proper (Logic.eq ==> equiv ==> iff) kFair.
Proof. split; intro; subst; now eapply kFair_compat_aux; eauto. Qed.

Lemma Between_LocallyFair : forall id (d : demon) id' k,
  Between id id' d k -> LocallyFairForOne id d.
Proof. intros * Hid. induction Hid; eauto. Qed.

(** A robot is never activated before itself with a fair demon!
    The fairness hypothesis is necessary, otherwise the robot may never be activated. *)
Lemma Between_same : forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof. intros * Hd. induction Hd; eauto. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof.
coinduction kfair_is_fair.
+ intro id. revert_one kFair. intros []. now apply Between_LocallyFair with id k.
+ apply (kfair_is_fair k). revert_one kFair. now intros [].
Qed.

(** [Between id id' d k] is monotonic on [k]. *)
Lemma Between_mono : forall id id' (d : demon) k,
  Between id id' d k -> forall k', (k <= k')%nat -> Between id id' d k'.
Proof. intros * Hd. induction Hd; intros k' Hk; eauto. Qed.

(** [kFair k d] is monotonic in [k]. *)
Theorem kFair_mono : forall k (d : demon), kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; revert_one kFair; intros [].
- intros. now apply Between_mono with k.
- now apply (fair k).
Qed.

(** ** Full synchronicity

A fully synchronous demon is a particular case of fair demon: all good robots
are activated at each round. In our setting this means that the demon never
return a null reference. *)

(** A demonic action is synchronous if all robots are in the same state: either all [Active], or all [Moving]. *)
Definition da_Synchronous da : Prop := forall id id' rc rc',
  match step da id rc, step da id' rc' with
    | Moving b, Moving b' => b = b'
    | Active iso, Active iso' => True
    | _, _ => False
  end.

Instance da_Synchronous_compat : Proper (equiv ==> iff) da_Synchronous.
Proof.
unfold da_Synchronous. intros d1 d2 Hd.
assert (Hequiv : forall id rc, step d1 id rc == step d2 id rc).
{ intros. now apply step_da_compat. }
split; intros Heq id id' rc rc'; generalize (Heq id id' rc rc');
assert (Hid := Hequiv id rc); assert (Hid' := Hequiv id' rc');
repeat destruct_match; simpl in Hid, Hid'; tauto || congruence.
Qed.

Definition StepSynchronous := Stream.forever (Stream.instant da_Synchronous).

Instance StepSynchronous_compat : Proper (equiv ==> iff) StepSynchronous.
Proof. unfold StepSynchronous. autoclass. Qed.

End Formalism.
