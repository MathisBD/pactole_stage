(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
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
Require Pactole.CommonRealFormalism.


Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


Module Make (Location : RealMetricSpace)(N : Size)(Spect : Spectrum(Location)(N))
            (Common : CommonRealFormalism.Sig(Location)(N)(Spect)).

Import Common.
Notation "s ⁻¹" := (Sim.inverse s) (at level 99).

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : Names.B → Location.t;
  step : Names.ident → option (Location.t → Sim.t);
  step_compat : Proper (eq ==> opt_eq (Location.eq ==> Sim.eq)) step;
  step_zoom :  forall id sim c, step id = Some sim -> (sim c).(Sim.zoom) <> R0;
  step_center : forall id sim c, step id = Some sim -> Location.eq (sim c).(Sim.center) c}.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id, opt_eq (Location.eq ==> Sim.eq)%signature (da1.(step) id) (da2.(step) id)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros d1 d2 [H1 H2]. repeat split; repeat intro; try symmetry; auto.
  specialize (H1 id). destruct (step d1 id), (step d2 id); trivial.
  intros x y Hxy. simpl in H1. symmetry. apply H1. now symmetry.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. repeat split; intros; try etransitivity; eauto.
  specialize (H1 id). specialize (H3 id). destruct (step d1 id), (step d2 id), (step d3 id); simpl in *; trivial.
  - simpl in *. intros x y Hxy. rewrite (H1 _ _ (reflexivity x)). now apply H3.
  - elim H1.
Qed.

Instance step_da_compat : Proper (da_eq ==> eq ==> opt_eq (Location.eq ==> Sim.eq)) step.
Proof. intros da1 da2 [Hd1 Hd2] p1 p2 Hp. subst. apply Hd1. Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_None : forall da1 da2, da_eq da1 da2 -> forall id, step da1 id = None <-> step da2 id = None.
Proof.
intros da1 da2 Hda id.
assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

(*
Instance spectrum_of_compat : Proper (da_eq ==> Logic.eq ==> Config.eq ==> Spec.eq) spectrum_of. 
Proof.
intros [? ? da1 ?] [? ? da2 ?] [Hda1 [Hda2 Hda3]] g1 g2 Hg p1 p2 Hp. simpl in *. subst. apply Hda3. assumption.
Qed.
*)

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
CoInductive demon :=
  NextDemon : demonic_action → demon → demon.

(** Destructors for demons, getting the head demonic action or the
    tail of the demon. *)

Definition demon_head (d : demon) : demonic_action :=
  match d with NextDemon da _ => da end.

Definition demon_tail (d : demon) : demon :=
  match d with NextDemon _ d => d end.

CoInductive deq (d1 d2 : demon) : Prop :=
  | Cdeq : da_eq (demon_head d1) (demon_head d2) -> deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. split.
+ coinduction deq_refl. reflexivity.
+ coinduction deq_sym. symmetry. now inversion H. now inversion H.
+ coinduction deq_trans.
  - inversion H. inversion H0. now transitivity (demon_head y).
  - apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
      now inversion H.
      now inversion H0.
Qed.

Instance deq_bisim : Bisimulation demon.
Proof. exists deq. apply deq_equiv. Qed.

Instance demon_head_compat : Proper (deq ==> da_eq) demon_head.
Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

Instance demon_tail_compat : Proper (deq ==> deq) demon_tail.
Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

(** ** Fairness *)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne g (d : demon) : Prop :=
  | ImmediatelyFair : step (demon_head d) g ≠ None → LocallyFairForOne g d
  | LaterFair : step (demon_head d) g = None → 
                LocallyFairForOne g (demon_tail d) → LocallyFairForOne g d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (∀ g, LocallyFairForOne g d) → Fair (demon_tail d) →
               Fair d.

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k, step (demon_head d) g <> None -> Between g h d k
| kReduce : forall k, step (demon_head d) g = None -> step (demon_head d) h <> None ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k, step (demon_head d) g = None -> step (demon_head d) h = None ->
                     Between g h (demon_tail d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) : Prop :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

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

Lemma Fair_compat_aux : forall d1 d2, deq d1 d2 -> Fair d1 -> Fair d2.
Proof.
cofix be_fair. intros d1 d2 Heq Hfair. destruct Hfair as [Hnow Hlater]. constructor.
+ intro. now rewrite <- Heq.
+ eapply be_fair; try eassumption. now f_equiv.
Qed.

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. repeat intro. split; intro; now eapply Fair_compat_aux; eauto. Qed.

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

Lemma kFair_compat_aux : forall k d1 d2, deq d1 d2 -> kFair k d1 -> kFair k d2.
Proof.
cofix be_fair. intros k d1 d2 Heq Hkfair. destruct Hkfair as [Hnow Hlater]. constructor.
+ intros. now rewrite <- Heq.
+ eapply be_fair; try eassumption. now f_equiv.
Qed.

Instance kFair_compat : Proper (eq ==> deq ==> iff) kFair.
Proof. repeat intro. subst. split; intro; now eapply kFair_compat_aux; eauto. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof.
  intros g h d k Hg. induction Hg.
  now constructor 1.
  now constructor 2.
  now constructor 2.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof.
  intros g d k Hd. induction Hd.
  now constructor 1.
  now constructor 3.
Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof.
  coinduction kfair_is_fair.
  destruct H as [Hbetween H]. intro. apply Between_LocallyFair with g k. now apply Hbetween.
  apply (kfair_is_fair k). now destruct H.
Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
  intros g h d k Hd. induction Hd; intros k' Hk.
  now constructor 1.
  destruct k'.
    now inversion Hk.
    constructor 2; assumption || now (apply IHHd; omega).
  constructor 3; assumption || now (apply IHHd; omega).
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
  forall g h, (demon_head d).(step) g = None <-> (demon_head d).(step) h = None.
Proof.
intros d Hd g h. destruct Hd as [Hd _]. split; intro H.
  assert (Hg := Hd g h). inversion Hg. contradiction. assumption.
  assert (Hh := Hd h g). inversion Hh. contradiction. assumption.
Qed.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2:
    (step (demon_head d) g) ≠ None → 
                      FullySynchronousForOne g d.

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    (∀ g, FullySynchronousForOne g d)
    → FullySynchronous (demon_tail d)
    → FullySynchronous d.


(** A locally synchronous demon is fair *)
Lemma local_fully_synchronous_implies_fair:
  ∀ g d, FullySynchronousForOne g d → LocallyFairForOne g d.
Proof. induction 1. now constructor. Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof.
  coinduction fully_fair.
  - intro. apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
Qed.

(** ** One step executions *)

(** [round r da conf] return the new configuration of robots (that is a function
    giving the position of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (r : robogram) (da : demonic_action) (conf : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
(*     let t := conf id in (** t is the current position of g seen by the demon *) *)
    match da.(step) id with (** first see whether the robot is activated *)
      | None => conf id (** If g is not activated, do nothing *)
      | Some sim => (** g is activated and [sim (conf g)] is its similarity *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
        | Good g => (* configuration expressed in the frame of g *)
          let conf_seen_by_g := Config.map (sim (conf (Good g))) conf in
          (* apply r on spectrum + back to demon ref. *)
          (sim (conf (Good g)))⁻¹ (r (Spect.from_config conf_seen_by_g))
        end
    end.

Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold req in Hr. unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try now elim Hstep.
+ f_equiv.
  - do 2 f_equiv. apply Hstep, Hconf.
  - apply Hr, Spect.from_config_compat, Config.map_compat; trivial. apply Hstep, Hconf.
+ rewrite Hda. reflexivity.
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

Lemma no_moving_same_conf : forall r da config,
  moving r da config = List.nil -> Config.eq (round r da config) config.
Proof.
intros r da config Hmove id.
destruct (Location.eq_dec (round r da config id) (config id)) as [Heq | Heq]; trivial.
rewrite <- moving_spec, Hmove in Heq. inversion Heq.
Qed.

Corollary no_active_same_conf :
  forall r da conf, active da = List.nil -> Config.eq (round r da conf) conf.
Proof.
intros r da conf Hactive.
assert (moving r da conf = List.nil). { apply incl_nil. rewrite <- Hactive. apply moving_active. }
now apply no_moving_same_conf.
Qed.


(** [execute r d conf] returns an (infinite) execution from an initial global
    configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon → Config.t → execution :=
  cofix execute d conf :=
  NextExecution conf (execute (demon_tail d) (round r (demon_head d) conf)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
  execution_tail (execute r d conf) = execute r (demon_tail d) (round r (demon_head d) conf).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. assumption.
apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.

(* Definitions of imprisonned, attracted, solution, solution_FSYNC, solution_FAIR_FSYNC
   (for the convergence problem) are removed. *)

End Make.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
