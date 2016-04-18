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
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Pactole.CommonRealFormalism.
(* Require Pactole.Similarity. *)


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
Inductive Active_or_idle := 
  | Idle (dist :R)                    (* moving distance, only use is state is Moving *)
  | Active (sim : Location.t → Sim.t) (* change of referential *)
                 ( r: R). (* travel ratio (rigid or flexible moves) *)

Definition Aoi_eq (a1 a2: Active_or_idle) := 
  match a1 with 
    | Idle d1 => match a2 with | Idle d2 => (d1 = d2) | _ => False end
    | Active sim1 r1 => match a2 with 
      | Active sim2 r2 => ((Location.eq ==> Sim.eq))%signature sim1 sim2 /\ r1 = r2
      | _ => False
    end
  end.

Instance Active_compat : Proper ((Location.eq ==> Sim.eq) ==>  eq ==> Aoi_eq) Active.
Proof. repeat intro. now split. Qed.

Instance Aoi_eq_equiv : Equivalence Aoi_eq.
Proof.
split.
+ intros x. unfold Aoi_eq. destruct x; try reflexivity. split; trivial.


Admitted.

Record demonic_action := {
  relocate_byz : Names.B → Location.t;
  step : Names.ident → Active_or_idle;
  step_compat : Proper (eq ==> Aoi_eq) step;
  step_zoom :  forall id sim r c, step id = Active sim r -> (sim c).(Sim.zoom) <> 0%R;
  step_center : forall id sim c r, step id = Active sim r -> Location.eq (sim c).(Sim.center) c;
  step_flexibility : forall id sim r, step id = Active sim r -> (0 <= r <= 1)%R}.
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id, (Aoi_eq)%signature (da1.(step) id) (da2.(step) id)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; reflexivity.
+ intros d1 d2 [H1 H2]. repeat split; repeat intro; try symmetry; auto.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. repeat split; intros; try etransitivity; eauto.
Qed.
(*
Proof. split.
+ split; intuition. now apply step_compat.
+ intros d1 d2 [H1 H2]. repeat split; repeat intro; try symmetry; auto.
  specialize (H1 id). destruct (step d1 id) eqn:Haoi1, (step d2 id) eqn:Haoi2; trivial;
  unfold Aoi_eq in *. symmetry. apply H1. destruct H1 as [H1 ?]. split; auto.
  intros x y Hxy. simpl in *. symmetry. apply H1. now symmetry.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. repeat split; intros; try etransitivity; eauto.
  specialize (H1 id). specialize (H3 id).
  destruct (step d1 id) eqn:Haoi1, (step d2 id) eqn:Haoi2, (step d3 id) eqn:Haoi3;
  simpl in *; trivial. transitivity dist0. apply H1. apply H3. exfalso; auto.
  - elim H1.
  - destruct H1 as [H1 H1']. split.
    * intros x y Hxy. rewrite (H1 _ _ (reflexivity x)). now apply H3.
    * rewrite H1'. now destruct H3.
Qed.
*)

Instance step_da_compat : Proper (da_eq ==> eq ==> Aoi_eq) step.
Proof. intros da1 da2 [Hd1 Hd2] p1 p2 Hp. subst. apply Hd1. Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_Idle : forall da1 da2, da_eq da1 da2 -> 
                        forall id r, step da1 id = (Idle r) <-> step da2 id = (Idle r).
Proof.
intros da1 da2 Hda id r.
assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
split; intro Hidle; rewrite Hidle in Hopt_eq; destruct step; reflexivity || elim Hopt_eq; auto.
Qed.

Lemma da_eq_step_Active : forall da1 da2, da_eq da1 da2 -> 
                          forall id sim r, step da1 id = (Active sim r) 
                                       <-> step da2 id = (Active sim r).
Proof.
intros da1 da2 Hda id sim r.
assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
split; intro Hactive; rewrite Hactive in Hopt_eq; destruct step; try reflexivity; elim Hopt_eq;
intros. erewrite H.


Qed.

(** Definitions of two subsets of robots: active and idle ones. *)
Definition idle da := List.filter
  (fun id => match step da id with Active _ _ => false | Idle _ => true end)
  Names.names.

Definition active da := List.filter
  (fun id => match step da id with Active _ _ => true | Idle _ => false end)
  Names.names.

Instance idle_compat : Proper (da_eq ==> eq) idle.
Proof.
intros da1 da2 Hda. unfold idle. induction Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id) eqn:Hstep1, (step da2 id) eqn:Hstep2.
  - rewrite IHl. reflexivity.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - apply IHl.
Qed.

Instance active_compat : Proper (da_eq ==> eq) active.
Proof.
intros da1 da2 Hda. unfold active. induction Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id) eqn:Hstep1, (step da2 id) eqn:Hstep2.
  - apply IHl.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id)).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - rewrite IHl. reflexivity.
Qed.

Lemma idle_spec : forall da id, List.In id (idle da) <-> exists r, step da id = Idle r.
Proof.
intros da id. unfold idle. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate. exists dist; auto.
apply Names.In_names. apply Names.In_names. destruct H. discriminate.
Qed.

Lemma active_spec : forall da id, List.In id (active da) <-> forall r, step da id <> Idle r.
Proof.
intros da id. unfold active. rewrite List.filter_In.
destruct (step da id); intuition; try discriminate.
apply Names.In_names. exfalso. apply (H dist). auto.
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
  | ImmediatelyFair : forall sim r, step (demon_head d) g = Active sim r → LocallyFairForOne g d
  | LaterFair : (exists r, step (demon_head d) g = Idle r) →
                LocallyFairForOne g (demon_tail d) → LocallyFairForOne g d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (∀ g, LocallyFairForOne g d) → Fair (demon_tail d) →
               Fair d.

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k r, step (demon_head d) g <> Idle r -> Between g h d k
| kReduce : forall k r1 r2, step (demon_head d) g = Idle r1 -> step (demon_head d) h <> Idle r2 ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k r1 r2, step (demon_head d) g = Idle r1 -> step (demon_head d) h = Idle r2 ->
                     Between g h (demon_tail d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) : Prop :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
intros g d1 d2 Hd Hfair. revert d2 Hd. induction Hfair; intros d2 Hd.
+ assert (Heq : Aoi_eq (step (demon_head d2) g) (Active sim r)) by now rewrite <- Hd, H.
  destruct (step (demon_head d2) g) eqn:?; simpl in Heq.
  - easy.
  - now constructor 1 with sim0 r0.
+ constructor 2.
  - destruct H. exists x. rewrite da_eq_step_Idle; try eassumption. now f_equiv.
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
+ constructor 1 with r. rewrite <- da_eq_step_None; try eassumption. now f_equiv.
+ constructor 2 with r1 r2.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - rewrite <- da_eq_step_None; try eassumption. now f_equiv.
  - apply IHbet. now f_equiv.
+ constructor 3 with r1 r2.
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
  now constructor 1 with r.
  constructor 2. exists r1. apply H. apply IHHg.
  constructor 2. exists r1. apply H. apply IHHg.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof.
  intros g d k Hd. induction Hd.
  now constructor 1 with r.
   destruct H. now constructor 3 with x x.
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
  now constructor 1 with r.
  destruct k'.
    now inversion Hk.
    constructor 2 with r1 r2; assumption || now (apply IHHd; omega).
  constructor 3 with r1 r2; assumption || now (apply IHHd; omega).
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
  forall g h, (forall r1, (demon_head d).(step) g = Idle r1) <-> forall r2, (demon_head d).(step) h = Idle r2.
Proof.
intros d Hd. destruct Hd as [Hd _]. split; intros H.
  assert (Hg := Hd g h). inversion Hg. specialize (H r). contradiction.
  destruct (H r2). intros r0. specialize (H r0). rewrite H in H1. assumption.
  assert (Hh := Hd h g). inversion Hh. specialize (H r). contradiction.
  destruct (H r2). intros r0. specialize (H r0). rewrite H in H1. assumption.
Qed. 

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2: forall r,
    (step (demon_head d) g) ≠ Idle r →
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
Proof. induction 1. now (constructor 1 with r). Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof.
  coinduction fully_fair.
  - intro. apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
Qed.



(** ** One step executions *)

Definition apply_sim (sim : Sim.t) (info : Config.RobotConf) :=
  {| Config.Loc := sim info; Config.Sta := Config.Sta info |}.

Instance apply_sim_compat : Proper (Sim.eq ==> Config.eq_RobotConf ==> Config.eq_RobotConf) apply_sim.
Proof.
intros sim sim' Hsim conf conf' Hconf. unfold apply_sim. hnf. split; simpl.
- apply Hsim, Hconf.
- apply Hconf.
Qed.

(** [round r da conf] return the new configuration of robots (that is a function
    giving the configuration of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (δ : R) (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
  let config' := fun id =>
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let conf := config id in (** t is the current configuration of g seen by the demon *)
    match da.(step) id with (** first see whether the robot is activated *)
      | None => conf (** If g is not activated, do nothing *)
      | Some (sim, mv_ratio) => (** g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => {| Config.Loc := da.(relocate_byz) b;
                      Config.Sta := Config.Sta (config id) |} (* byzantine robot are relocated by the demon *)
        | Good g => 
            match Config.Sta (config (Good g)) with
              | Config.RDY2LookCompute => (* configuration expressed in the frame of g *)
                let config_seen_by_g := Config.map (apply_sim (sim (Config.Loc (config (Good g))))) config in
                (* apply r on spectrum *)
                let local_target := r (Spect.from_config config_seen_by_g) in
                (* the demon chooses a point on the line from the target by mv_ratio *)
                let chosen_target := Location.mul mv_ratio local_target in 
                  (Config.mk_RC (Config.Loc (config (Good g))) (Config.RDY2Move (local_target,chosen_target)))
              | Config.RDY2Move targets =>
                {| Config.Loc := (sim (config (Good g)))⁻¹
                (if Rle_bool δ (Location.dist (snd targets) conf) then (snd targets) else (fst targets));
                   Config.Sta := Config.RDY2LookCompute |}
            end 

        end
    end.

Instance round_compat : Proper (eq ==> req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros ? δ ? r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id. subst.
unfold req in Hr. unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id) as [[f1 mvr1] |], (step da2 id) as [[f2 mvr2] |], id as [ g| b]; try now elim Hstep.
+ destruct Hstep as [Hstep Hstep']. hnf in Hstep, Hstep'. simpl in Hstep, Hstep'. subst.
(* we lack some instances to ba able to perform directly the correct rewrites
SearchAbout Proper Spect.from_config.
SearchAbout Proper Config.map.
SearchAbout Proper Location.eq.
 *)
  
  assert (Heq : Location.eq (Config.map (apply_sim (f2 (conf2 (Good g)))) conf2 (Good g))
                          (Config.map (apply_sim (f1 (conf1 (Good g)))) conf1 (Good g))).
{ f_equiv. apply apply_sim_compat. symmetry. apply Hstep, Hconf. symmetry; apply Hconf. }
 destruct (Config.Sta (conf1 (Good g))) eqn:HSta1, (Config.Sta (conf2 (Good g))) eqn:HSta2;
 unfold Config.mk_RC, Config.eq_RobotConf, Config.eq_State; simpl.
 * destruct (Hconf (Good g)). rewrite HSta1, HSta2 in H0. unfold Config.eq_State in H0.
   repeat split. assumption. apply Hr. f_equiv. do 2 f_equiv. apply Hstep, Hconf. assumption.
   f_equiv. apply Hr. f_equiv. f_equiv. f_equiv. apply Hstep. assumption. assumption.
 * exfalso. destruct (Hconf (Good g)). rewrite HSta1, HSta2 in H0.
   unfold Config.eq_State in H0. assumption.
 * exfalso. destruct (Hconf (Good g)). rewrite HSta1, HSta2 in H0.
   unfold Config.eq_State in H0. destruct targets in H0. assumption.
 * split; auto. f_equiv. f_equiv. apply Hstep. f_equiv. auto.
   destruct (Hconf (Good g)). rewrite HSta1, HSta2 in H0. unfold Config.eq_State in H0.
   destruct targets, targets0 in *.  
   destruct H0. rewrite H1,H0. simpl. rewrite H. 
   destruct (Rle_bool δ (Location.dist t2 (conf2 (Good g)))); simpl; assumption.
+ rewrite Hda. destruct (Hconf (Byz b)). rewrite H0. reflexivity.
Qed.

(** A third subset of robots, moving ones *)
Definition moving δ r da config := List.filter
  (fun id => if Location.eq_dec (round δ r da config id) (config id) then false else true)
  Names.names.

Instance moving_compat : Proper (eq ==> req ==> da_eq ==> Config.eq ==> eq) moving.
Proof.
intros ? δ ? r1 r2 Hr da1 da2 Hda c1 c2 Hc. subst. unfold moving.
induction Names.names as [| id l]; simpl.
* reflexivity.
* destruct (Location.eq_dec (round δ r1 da1 c1 id) (c1 id)) as [Heq1 | Heq1],
           (Location.eq_dec (round δ r2 da2 c2 id) (c2 id)) as [Heq2 | Heq2].
  + apply IHl.
  + elim Heq2. transitivity (round δ r1 da1 c1 id).
    - symmetry. now apply round_compat.
    - rewrite Heq1. apply Hc.
  + elim Heq1. transitivity (round δ r2 da2 c2 id).
    - now apply round_compat.
    - rewrite Heq2. symmetry. apply Hc.
  + f_equal. apply IHl.
Qed.

Lemma moving_spec : forall δ r da config id,
  List.In id (moving δ r da config) <-> ~Location.eq (round δ r da config id) (config id).
Proof.
intros δ r da config id. unfold moving. rewrite List.filter_In.
split; intro H.
+ destruct H as [_ H].
  destruct (Location.eq_dec (round δ r da config id) (config id)) as [_ | Hneq]; intuition.
+ split.
  - apply Names.In_names.
  - destruct (Location.eq_dec (round δ r da config id) (config id)) as [Heq | _]; intuition.
Qed.

Lemma moving_active : forall δ r da config, List.incl (moving δ r da config) (active da).
Proof.
intros δ r config da id. rewrite moving_spec, active_spec. intro Hmove.
unfold round in Hmove. destruct (step config id).
- discriminate.
- now elim Hmove.
Qed.

(** Some results *)

Lemma no_active_same_conf :
  forall δ r da conf, active da = List.nil -> Config.eq (round δ r da conf) conf.
Proof.
intros δ r da conf Hactive.
unfold round, Config.eq, Config.eq_RobotConf; split;
destruct (step da id) eqn : Heq. assert (Heq': step da id <> None).
 intro. rewrite H in Heq. discriminate. rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
 reflexivity.
 assert (Heq': step da id <> None). intro. rewrite H in Heq. discriminate.
 rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
 reflexivity. 
Qed.


(** [execute r d conf] returns an (infinite) execution from an initial global
    configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute δ (r : robogram): demon → Config.t → execution :=
  cofix execute d conf :=
  NextExecution conf (execute (demon_tail d) (round δ r (demon_head d) conf)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall δ (r : robogram) (d : demon) (conf : Config.t),
  execution_tail (execute δ r d conf) = execute δ r (demon_tail d) (round δ r (demon_head d) conf).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

Instance execute_compat : Proper (eq ==> req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
intros ? δ ? r1 r2 Hr. subst.
cofix proof. constructor. simpl. assumption.
apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.

End Make.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
