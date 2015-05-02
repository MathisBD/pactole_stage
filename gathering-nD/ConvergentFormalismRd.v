(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, X. Urbain, L. Rieg                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import Reals.
Require Import Robots.
Require Import Positions.


Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


Module ConvergentFormalism (Location : MetricSpace)(N : Size)(Spec : Spectrum(Location)(N)).

Module Names := Spec.Names.
Module Pos := Spec.Pos.

(** ** Programs for good robots *)


Record bijection (T : Type) eqT (Heq : @Equivalence T eqT) := {
  section :> T → T;
  retraction : T → T;
  section_compat : Proper (eqT ==> eqT) section;
  Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.

Notation "s ⁻¹" := (s.(retraction)) (at level 99).

Definition bij_eq (bij1 bij2 : bijection Location.eq_equiv) :=
  (Location.eq ==> Location.eq)%signature bij1.(section) bij2.

Instance bij_eq_equiv : Equivalence bij_eq.
Proof. split.
+ intros f x y Hxy. apply section_compat. assumption.
+ intros f g Heq x y Hxy. symmetry. apply Heq. symmetry. assumption.
+ intros f g h Hfg Hgh x y Hxy. rewrite (Hfg _ _ Hxy). apply Hgh. reflexivity.
Qed.

Instance retraction_compat : Proper (bij_eq ==> (Location.eq ==> Location.eq)) (@retraction _ _ Location.eq_equiv).
Proof.
intros f g Hfg x y Hxy. rewrite <- f.(Inversion), (Hfg _ _ (reflexivity _)), Hxy, g.(Inversion). reflexivity.
Qed.

(** Similarities are functions that multiply distance by a constant ratio.
    For convenience, we also add their center, that is the location from which robots locally observe. *)
(* I assume that similarities are bijections but it is probably provable, provided k <> 0. *)
Record similarity := {
  f :> @bijection Location.t _ _;
  ratio : R;
  center : Location.t;
  center_prop : f center = Location.origin;
  dist_prop : forall x y, Location.dist (f x) (f y) = (ratio * Location.dist x y)%R}.

Definition sim_eq sim1 sim2 := bij_eq sim1.(f) sim2.(f).

Instance similarity_f_compat : forall sim, Proper bij_eq sim.(f).
Proof.
intros sim ? ? Heq. rewrite <- Location.dist_defined in Heq |- *.
rewrite <- (Rmult_0_r sim.(ratio)), <- Heq. now apply dist_prop.
Qed.

Instance sim_eq_equiv : Equivalence sim_eq.
Proof. unfold sim_eq. split.
+ intros [f k c Hc Hk]. simpl. reflexivity.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] Hfg. simpl in *. now symmetry.
+ intros [f kf cf Hcf Hkf] [g kg cg Hcg Hkg] [h kh ch Hch Hkh] ? ?. simpl in *. etransitivity; eassumption.
Qed.


Unset Implicit Arguments.

(** ** Good robots have a common program, which we call a robogram *)

Record robogram := {
  pgm :> Spec.t → Location.t;
  pgm_compat : Proper (Spec.eq ==> Location.eq) pgm}.

Definition req (r1 r2 : robogram) := (Spec.eq ==> Location.eq)%signature r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
+ intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
+ intros r1 r2 r3 H1 H2 x y Heq.
  rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
Qed.

(** ** Demonic schedulers *)

(** Lifting an equivalence relation to an option type. *)
Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
  match xo, yo with
    | None, None => True
    | None, Some _ | Some _, None => False
    | Some x, Some y => eqT x y
  end.

Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
Proof. split.
+ intros [x |]; simpl; reflexivity || auto.
+ intros [x |] [y |]; simpl; trivial; now symmetry.
+ intros [x |] [y |] [z |]; simpl; tauto || etransitivity; eassumption.
Qed.

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : Names.B → Location.t;
  step : Names.ident → option (Location.t → similarity);
  step_compat : Proper (eq ==> opt_eq (Location.eq ==> sim_eq)) step;
  step_ratio :  forall id sim c, step id = Some sim -> (sim c).(ratio) <> R0;
  step_center : forall id sim c, step id = Some sim -> Location.eq (sim c).(center) c}.
(*  spectrum_of : Names.G → (Pos.t → Spec.t);
  spectrum_ok : forall g, forall pos : Pos.t, Spec.is_ok (spectrum_of g pos) pos;
  spectrum_exteq : Proper (eq ==> Pos.eq ==> Spec.eq) spectrum_of}. *)
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id, opt_eq (Location.eq ==> sim_eq)%signature (da1.(step) id) (da2.(step) id)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).
(* /\
  (forall g, (Pos.eq ==> Spec.eq)%signature (da1.(spectrum_of) g) (da2.(spectrum_of) g)). *)

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

Instance step_da_compat : Proper (da_eq ==> eq ==> opt_eq (Location.eq ==> sim_eq)) step.
Proof. intros da1 da2 [Hd1 Hd2] p1 p2 Hp. subst. apply Hd1. Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.
(*
Instance spectrum_of_compat : Proper (da_eq ==> Logic.eq ==> Pos.eq ==> Spec.eq) spectrum_of. 
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
CoInductive kFair k (d : demon) :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

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
  - intro. apply local_fully_synchronous_implies_fair. apply H.
  - now inversion H.
Qed.

(** ** Executions *)

(** Now we can [execute] some robogram from a given position with a [demon] *)
CoInductive execution :=
  NextExecution : Pos.t → execution → execution.


(** *** Destructors for demons *)

Definition execution_head (e : execution) : Pos.t :=
  match e with NextExecution pos _ => pos end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

CoInductive eeq (e1 e2 : execution) : Prop :=
  | Ceeq : Pos.eq (execution_head e1) (execution_head e2) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. split.
+ coinduction eeq_refl. reflexivity.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. intro.
  - inversion H. inversion H0. now transitivity (execution_head y id).
  - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
    now inversion H. now inversion H0.
Qed.

Instance eeq_bisim : Bisimulation execution.
Proof. exists eeq. apply eeq_equiv. Qed.

Instance execution_head_compat : Proper (eeq ==> Pos.eq) execution_head.
Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.

Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
Proof. intros e1 e2 He. now inversion He. Qed.

(** [round r da pos] return the new position of robots (that is a function
    giving the position of each robot) from the previous one [pos] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (r : robogram) (da : demonic_action) (pos : Pos.t) : Pos.t :=
  (** for a given robot, we compute the new position *)
  fun id =>
    let t := pos id in (** t is the current position of g seen by the demon *)
    match da.(step) id with (** first see whether the robot is activated *)
      | None => t (** If g is not activated, do nothing *)
      | Some sim => (** g is activated and [sim (pos g)] is its similarity *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
        | Good g => (* position expressed in the frame of g *)
          let pos_seen_by_g := Pos.map (sim (pos (Good g))) pos in
          (* apply r on spectrum + back to demon ref. *)
          (sim (pos (Good g)))⁻¹ (r (Spec.from_config pos_seen_by_g))
        end
    end.

Instance round_compat : Proper (req ==> da_eq ==> Pos.eq ==> Pos.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hd pos1 pos2 Hpos id.
unfold req in Hr. unfold round.
assert (Hstep := step_da_compat Hd (reflexivity id)). assert (Hda1 := da1.(step_compat) _ _ (reflexivity id)).
destruct (step da1 id), (step da2 id), id; try now elim Hstep.
+ simpl in Hstep. f_equiv.
  - apply Hstep, Hpos.
  - apply Hr, Spec.from_config_compat, Pos.map_compat; trivial. apply Hstep, Hpos.
+ rewrite Hd. reflexivity.
Qed.

(** A third subset of robots, moving ones *)
Definition moving r da config := List.filter
  (fun id => if Location.eq_dec (round r da config id) (config id) then false else true)
  Names.names.

Lemma moving_active : forall r config da id, List.In id (moving r da config) -> List.In id (active da).
Proof.
intros r config da id. unfold moving, active. do 2 rewrite List.filter_In.
intros [Hin Hmoving].
destruct (Location.eq_dec (round r da config id) (config id)) as [_ | Hmove]; try discriminate.
clear Hmoving. split; trivial.
unfold round in Hmove. destruct (step da id).
- reflexivity.
- now elim Hmove.
Qed.


(** [execute r d pos] returns an (infinite) execution from an initial global
    position [pos], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon → Pos.t → execution :=
  cofix execute d pos :=
  NextExecution pos (execute (demon_tail d) (round r (demon_head d) pos)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (pos : Pos.t),
  execution_tail (execute r d pos) = execute r (demon_tail d) (round r (demon_head d) pos).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

Theorem execute_compat : Proper (req ==> deq ==> Pos.eq ==> eeq) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. assumption.
apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.


(** ** Properties of executions  *)

Open Scope R_scope.
(** Expressing that all good robots are confined in a small disk. *)
CoInductive imprisonned (center : Location.t) (radius : R) (e : execution) : Prop
:= InDisk : (∀ g : Names.G, Rabs (Location.dist center (execution_head e (Good g))) <= radius)
            → imprisonned center radius (execution_tail e)
            → imprisonned center radius e.

(** The execution will end in a small disk. *)
Inductive attracted (center : Location.t) (radius : R) (e : execution) : Prop :=
  | Captured : imprisonned center radius e → attracted center radius e
  | WillBeCaptured : attracted center radius (execution_tail e) → attracted center radius e.

(** [solution r] means that robogram [r] is a solution, i.e. is convergent
    ([attracted]) for any demon. *)
Definition solution (r : robogram) : Prop :=
  ∀ (pos : Pos.t),
  ∀ (d : demon), Fair d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : Location.t), attracted lim_app epsilon (execute r d pos).


(** Solution restricted to fully synchronous demons. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  ∀ (pos : Pos.t),
  ∀ (d : demon), FullySynchronous d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : Location.t), attracted lim_app epsilon (execute r d pos).


(** A Solution is also a solution restricted to fully synchronous demons. *)
Lemma solution_FAIR_FSYNC : ∀ r, solution r → solution_FSYNC r.
Proof.
  intros r H.
  unfold solution_FSYNC, solution in *.
  intros pos d H0.
  apply H.
  now apply fully_synchronous_implies_fair.
Qed.

End ConvergentFormalism.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
