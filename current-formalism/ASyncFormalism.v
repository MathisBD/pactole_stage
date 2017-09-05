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
Require Import RelationClasses.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RealMetricSpace.
Require Pactole.CommonRealFormalism.
(* Require Pactole.Similarity. *)


Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

Module Type Delta.
  Parameter delta: R.
End Delta.

Module Make (Location : RealMetricSpace)
            (N : Size)
            (Import D: Delta)
            (Names : Robots(N))
            (Info : SourceTargetSig(Location))
            (Config : Configuration(Location)(N)(Names)(Info))
            (Spect : Spectrum(Location)(N)(Names)(Info)(Config))
            (Common : CommonRealFormalism.Sig(Location)(N)(Names)(Info)(Config)(Spect)).

  Import Common.
Notation "s ⁻¹" := (Sim.inverse s) (at level 99).

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Inductive Active_or_Moving := 
  | Moving (dist :R)                   (* moving ratio *)
  | Active (sim : Location.t → Sim.t). (* change of referential *)

Definition Aom_eq (a1 a2: Active_or_Moving) :=
  match a1, a2 with
    | Moving d1, Moving d2 => d1 = d2
    | Active sim1, Active sim2 => (Location.eq ==> Sim.eq)%signature sim1 sim2
    | _, _ => False
  end.


Instance Active_compat : Proper ((Location.eq ==> Sim.eq) ==> Aom_eq) Active.
Proof. intros ? ? ?. auto. Qed.

(* as Active give a function, Aom_eq is not reflexive. It's still symmetric and transitive.*)
Instance Aom_eq_Symmetric : Symmetric Aom_eq.
Proof.
intros x y H. unfold Aom_eq in *. destruct x, y; auto. intros ? ? Heq. symmetry. now apply H.
Qed.

Instance Aom_eq_Transitive : Transitive Aom_eq.
Proof.
intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto; [].
intros ? ? Heq. rewrite (H12 _ _ Heq). now apply H23.
Qed.

Record demonic_action := {
  relocate_byz : Names.B → Location.t;
  step : Names.ident → Config.RobotConf -> Active_or_Moving;
  step_delta : forall id Rconfig sim, step id Rconfig = Active sim -> 
       (Location.eq Rconfig.(Config.loc) Rconfig.(Config.state).(Info.target)) \/
       (Location.dist Rconfig.(Config.loc) Rconfig.(Config.state).(Info.source) >= delta)%R;
  step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step;
  step_zoom :  forall id config sim c, step id config = Active sim -> (sim c).(Sim.zoom) <> 0%R;
  step_center : forall id config sim c , step id config = Active sim -> 
                                         Location.eq (sim c).(Sim.center) c;
  step_flexibility : forall id config r, step id config = Moving r -> (0 <= r <= 1)%R}.
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros da1 da2 [Hda1 Hda2]. repeat split; repeat intro; try symmetry; auto.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
  repeat split; intros; try etransitivity; eauto.
Qed.

Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
Proof.
intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
etransitivity.
- apply Hd1.
- apply (step_compat da2); auto.
Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_Moving : forall da1 da2, da_eq da1 da2 -> 
                        forall id config r, step da1 id config = (Moving r) <-> 
                                            step da2 id config = (Moving r).
Proof.
intros da1 da2 Hda id config r.
assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; auto.
Qed.

(* small function to know is an object of type Active_or_Moving is Active *) 
Definition is_Active aom :=
  match aom with
    | Active _ => true
    | _ => false
  end.

Instance is_Active_compat : Proper (Aom_eq ==> eq) is_Active.
Proof.
intros a1 a2 Haom.
unfold is_Active, Aom_eq in *.
destruct a1,a2; auto.
exfalso; auto.
Qed.

 
(** Definitions of two subsets of robots: active and idle ones. *)
Definition moving da config := List.filter
  (fun id => if (is_Active (step da id config)) then false else true)
  Names.names.

Definition active da config := List.filter
  (fun id => is_Active (step da id config))
  Names.names.

Instance moving_compat : Proper (da_eq ==> Config.eq_RobotConf ==> eq) moving.
Proof.
intros da1 da2 Hda c1 c2 Hc. unfold moving. induction Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id c1) eqn:Hstep1, (step da2 id c2) eqn:Hstep2.
  - rewrite IHl. reflexivity.
  - assert (Hcompat := step_da_compat Hda (reflexivity id) Hc ).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id) Hc).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - apply IHl.
Qed.

Instance active_compat : Proper (da_eq ==> Config.eq_RobotConf ==> eq) active.
Proof.
intros da1 da2 Hda c1 c2 Hc. unfold active. induction Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da1 id c1) eqn:Hstep1, (step da2 id c2) eqn:Hstep2.
  - apply IHl.
  - assert (Hcompat := step_da_compat Hda (reflexivity id) Hc).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - assert (Hcompat := step_da_compat Hda (reflexivity id) Hc).
    rewrite Hstep1, Hstep2 in Hcompat. elim Hcompat.
  - rewrite IHl. reflexivity.
Qed.

Lemma moving_spec : forall da id config, List.In id (moving da config) <-> 
                                         exists r, step da id config = Moving r.
Proof.
intros da id config. unfold moving. rewrite List.filter_In.
destruct (step da id config); intuition; try discriminate. exists dist; auto.
apply Names.In_names. apply Names.In_names. destruct H. discriminate.
Qed.

Lemma active_spec : forall da id config,
  List.In id (active da config) <-> exists sim, step da id config = Active sim.
Proof.
intros da id config. unfold active. rewrite List.filter_In.
destruct (step da id config); intuition; try discriminate.
apply Names.In_names. exfalso. destruct H. discriminate. exists sim. auto.
apply Names.In_names.
Qed.


(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

Definition deq (d1 d2 : demon) : Prop := Stream.eq da_eq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. apply Stream.eq_equiv. apply da_eq_equiv. Qed.
(*
Instance deq_bisim : Bisimulation demon.
Proof. exists deq. apply deq_equiv. Qed.
 *)


Instance demon_hd_compat : Proper (deq ==> da_eq) (@Stream.hd _) := Stream.hd_compat _.
Instance demon_tl_compat : Proper (deq ==> deq) (@Stream.tl _) := Stream.tl_compat _.

(** ** Fairness *)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne g (d : demon) : Prop :=
  | NowFair : forall rconf, is_Active (step (Stream.hd d) g rconf) = true → LocallyFairForOne g d
  | LaterFair : forall rconf, is_Active (step (Stream.hd d) g rconf) = false → LocallyFairForOne g (Stream.tl d) → LocallyFairForOne g d.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ g, LocallyFairForOne g d).

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k rconf, is_Active (step (Stream.hd d) g rconf) = true -> Between g h d k(* faire une replace demon_head with Stream.hd *)
| kReduce : forall k rconf, is_Active (step (Stream.hd d) g rconf) = false ->
                            is_Active (step (Stream.hd d) h rconf) = true ->
                      Between g h (Stream.tl d) k -> Between g h d (S k)
| kStall : forall k rconf, is_Active (step (Stream.hd d) g rconf) = false ->
                           is_Active (step (Stream.hd d) h rconf) = false ->
                     Between g h (Stream.tl d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
(* CoInductive kFair k (d : demon) : Prop := *)
(*   AlwayskFair : (forall g h, Between g h d k) -> kFair k (Stream.tl d) -> *)
(*                 kFair k d. *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall g h, Between g h d k).

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
  intros g da1 da2 Hda Hfair. revert da2 Hda. induction Hfair; intros da2 Hda.
  + assert (Heq : is_Active (step (Stream.hd da2) g rconf) = true) by now rewrite <- Hda, H.
   destruct (step (Stream.hd da2) g) eqn:?; simpl in Heq.
   - easy.
   - constructor 1 with rconf.
     unfold is_Active.
     rewrite Heqa; auto.
 + assert (Heq : is_Active (step (Stream.hd da2) g rconf) = false) by now rewrite <- Hda, H.
   destruct (step (Stream.hd da2) g) eqn:?; simpl in Heq.
   - constructor 2 with rconf.
     unfold is_Active.
     rewrite Heqa.
     assumption.
     apply IHHfair.
     now f_equiv.
   - apply IHHfair.
     assert (Hneq:= Bool.diff_true_false).
     exfalso; auto.
Qed.

Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall g h k d1 d2, deq d1 d2 -> Between g h d1 k -> Between g h d2 k.
Proof.
intros g h k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
+ destruct (step (Stream.hd d) g rconf) eqn : Hstep.
  - easy.
  - constructor 1 with rconf.
    now rewrite <- Heq, Hstep.    
+ destruct (step (Stream.hd d) g rconf) eqn : Hstep.
  - constructor 2 with rconf.
    * now rewrite <- Heq, Hstep.
    * now rewrite <- Heq.
    * apply IHbet; now f_equiv.
  - easy.
+ destruct (step (Stream.hd d) g rconf) eqn : Hstep.
  - constructor 3 with rconf.
    * now rewrite <- Heq, Hstep.
    * now rewrite <- Heq.
    * apply IHbet; now f_equiv.
  - easy.
Qed.

Instance Between_compat : Proper (eq ==> eq ==> deq ==> eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Instance kFair_compat : Proper (eq ==> deq ==> iff) kFair.
Proof. intros k ? ?. subst. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof.
  intros g d h k Hg.
  induction Hg;
    destruct (step (Stream.hd d) g rconf) eqn : Hstep; try easy.
  - constructor 1 with rconf. now rewrite Hstep.
  - constructor 2 with rconf; try (now rewrite Hstep); try assumption.
  - constructor 2 with rconf; try (now rewrite Hstep); try assumption.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof. intros g d k Hd. induction Hd; try now constructor.
       now constructor 1 with rconf.
       now constructor 3 with rconf.
Qed.       
(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros. eauto using (@Between_LocallyFair g _ g). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
  intros g h d k Hd. induction Hd; intros k' Hk.
  now constructor 1 with rconf.
  destruct k'.
  now inversion Hk.
  constructor 2 with rconf; assumption || now (apply IHHd; omega).
  constructor 3 with rconf; assumption || now (apply IHHd; omega).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; destruct H.
- intros. now apply Between_mon with k.
- now apply (fair k).
Qed.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the step function
  of the demon never returns None. *)


(** A demon is fully synchronous at the first step. *)

Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2: forall rconf,
    is_Active (step (Stream.hd d) g rconf) = true → 
                      FullySynchronousForOne g d.

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    (∀ g, FullySynchronousForOne g d)
    → FullySynchronous (Stream.tl d)
    → FullySynchronous d.


(** A locally synchronous demon is fair *)
Lemma local_fully_synchronous_implies_fair:
  ∀ g d, FullySynchronousForOne g d → LocallyFairForOne g d.
Proof. induction 1. now (constructor 1 with rconf). Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof.
  coinduction fully_fair.
  - intro. apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
Qed.


(** ** One step executions *)

(* TODO: apply sim to info? *)
Definition apply_sim (sim : Sim.t) (rconf : Config.RobotConf) :=
  {| Config.loc := sim rconf; Config.state := Config.state rconf |}.

Instance apply_sim_compat : 
        Proper (Sim.eq ==> Config.eq_RobotConf ==> Config.eq_RobotConf) apply_sim.
Proof.
intros sim sim' Hsim conf conf' Hconf. unfold apply_sim. hnf. split; simpl.
- apply Hsim, Hconf.
- apply Hconf.
Qed.

(** [round r da conf] return the new configuration of robots (that is a function
    giving the configuration of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let conf := config id in
    let pos := conf.(Config.loc) in
    match da.(step) id conf with (** first see whether the robot is activated *)
      | Moving mv_ratio =>
        match id with
        | Good g =>
           let tgt := conf.(Config.state).(Info.target) in
           let new_loc :=  (** If g is not activated, it moves toward its destination *)
              Location.add pos
              (Location.mul mv_ratio (Location.add tgt (Location.opp pos))) in
           {| Config.loc := new_loc ; Config.state := conf.(Config.state) |}
        | Byz b => conf
        end
      | Active sim => (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => (* byzantine robot are relocated by the demon *)
                   {| Config.loc := da.(relocate_byz) b;
                      Config.state := Config.state (config id) |}
        | Good g => 
          let frame_change := sim (Config.loc (config (Good g))) in
          let local_conf := Config.map (apply_sim frame_change) config in
          let target := frame_change⁻¹ (r (Spect.from_config local_conf)) in
           {| Config.loc := pos ; 
              Config.state := {| Info.source := pos ; Info.target := target|} |}
        end
    end.


Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold req in Hr.
unfold round.
assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
apply Hconf.
assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
assert (Hsim: Aom_eq (step da1 id (conf1 id)) (step da1 id (conf2 id))).
apply step_da_compat; try reflexivity.
apply Hrconf.
destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2,
(step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
+ unfold Aom_eq in *.
  rewrite Hstep.
  f_equiv.
  f_equiv.
  apply Hrconf.
  do 2 f_equiv.
  apply Hrconf.
  f_equiv; apply Hrconf.
  unfold Info.eq.
  split; apply Hrconf.
+ unfold Aom_eq in *. exfalso; auto.
+ unfold Aom_eq in *. exfalso; auto.
+ f_equiv; try (now apply Hconf); [].
  split; cbn; try (now apply Hconf); [].
  simpl in Hstep. f_equiv.
  - f_equiv. apply Hstep, Hrconf.
  - apply Hr. do 3 f_equiv; trivial; []. apply Hstep, Hconf.
+ rewrite Hda. destruct (Hconf (Byz b)) as [? Heq]. split; simpl in *; try easy. 
Qed.


(** A third subset of robots, moving ones *)
Definition moving_sup_0 r da config := List.filter
  (fun id => if Location.eq_dec (round r da config id) (config id) then false else true)
  Names.names.

Instance moving_sup_0_compat : Proper (req ==> da_eq ==> Config.eq ==> eq) moving_sup_0.
Proof.
intros r1 r2 Hr da1 da2 Hda c1 c2 Hc. unfold moving_sup_0.
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

Lemma moving_sup_0_spec : forall r da config id,
  List.In id (moving_sup_0 r da config) <-> ~Location.eq (round r da config id) (config id).
Proof.
intros r da config id. unfold moving_sup_0. rewrite List.filter_In.
split; intro H.
+ destruct H as [_ H].
  destruct (Location.eq_dec (round r da config id) (config id)) as [_ | Hneq]; intuition.
+ split.
  - apply Names.In_names.
  - destruct (Location.eq_dec (round r da config id) (config id)) as [Heq | _]; intuition.
Qed.

(* un Lemme qui dit que si personne n'a bougé de 0 ni été activé, alors on a la même conf? 

faux car si jamais on a un ratio qui revient au point de départ c'est pas vrai*)

(* Lemma moving_no_sup_0_same_conf : forall r da conf id ratio g, id = Good g -> moving_sup_0 r da conf = Datatypes.nil 
-> step da id (conf id) = Moving ratio -> (ratio = 0)%R.
Proof.
intros r da conf id ratio g Hgood Hmoving Hratio. destruct (Rdec ratio 0%R).
auto. exfalso. assert (~Location.eq (round r da conf id) (conf id)).
Focus 2. apply moving_sup_0_spec in H. rewrite Hmoving in H. auto.
unfold round. rewrite Hratio, Hgood.


(* elim Hmoving.
simpl in *. destruct (step da id (conf id)) in Hmoving. rewrite Hratio in Hmoving.
specialize (moving_sup_0 r da conf id). in Hmoving.
unfold moving_sup_0, round in Hmoving. specialize (Hmoving id). rewrite Hratio in Hmoving.

 *)
Qed.


Lemma no_active_no_moving_same_conf : forall r da conf rconf, active da rconf = List.nil
      -> moving_sup_0 r da conf = List.nil -> Config.eq (round r da conf) conf.
Proof.
intros r da conf rconf Hactive Hmoving.
unfold round, Config.eq, Config.eq_RobotConf; split;
destruct (step da id (conf id)) eqn : Heq. apply moving_no_sup_0_same_conf with (r:=r) in Heq; trivial.
rewrite Heq.
assert (Location.eq (Location.mul 0 (Location.add 
        (Config.target (Config.info (conf id))) (Location.opp (conf id))))
        Location.origin). apply Location.mul_0. destruct id as [g |b]. simpl.
        rewrite H. apply Location.add_origin. reflexivity.
        unfold active in Hactive.
 *)
(* this Lemmas are not true anymore now that we change the definition of a step and a round.*)
(* Lemma moving_sup_0_active : forall r da config rconf, List.incl (moving_sup_0 r da config) (moving da rconf).
Proof.
intros r config da rconf id. rewrite moving_sup_0_spec, active_spec. intro Hmove.
unfold round in Hmove. destruct (step config id).
- now elim Hmove.
- discriminate.
Qed.
 *)
(** Some results *)

(* Lemma no_active_same_conf :
  forall δ r da conf, active da = List.nil -> Config.eq (round δ r da conf) conf.
Proof.
intros δ r da conf Hactive.
unfold round, Config.eq, Config.eq_RobotConf; split;
destruct (step da id) eqn : Heq. reflexivity.
 assert (Heq': step da id <> Idle r0).
 intro. rewrite H in Heq. discriminate. rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
 reflexivity.
 assert (Heq': step da id <> None). intro. rewrite H in Heq. discriminate.
 rewrite <- active_spec, Hactive in Heq'. inversion Heq'.
 reflexivity. 
Qed. *)


(** [execute r d conf] returns an (infinite) execution from an initial global
    configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)

Definition execute (r : robogram): demon → Config.t → execution :=
  cofix execute d conf :=
  Stream.cons conf (execute (Stream.tl d) (round r (Stream.hd d) conf)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
  Stream.tl (execute r d conf) = execute r (Stream.tl d) (round r (Stream.hd d) conf).
Proof. intros. destruct d. reflexivity. Qed.

Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
intros r1 r2 Hr. subst.
cofix proof. constructor.
+ simpl. assumption.
+ apply proof; clear proof.
  - now inversion H.
  - apply round_compat; try easy. now destruct H.
Qed.

End Make.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
