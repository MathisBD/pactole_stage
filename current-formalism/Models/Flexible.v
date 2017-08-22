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
Require Import RelationPairs.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.


Section FlexibleFormalism.

Context {loc info : Type}.
Context {Sloc : Setoid loc}.
Context {Eloc : EqDec Sloc}.
Context {Sinfo : Setoid info}.
Context {Einfo : EqDec Sinfo}.
Context {RMS : @RealMetricSpace loc Sloc Eloc}.
Context {N : Names}.
Context {Info : Information loc info}.
Context {Spect : Spectrum loc info}.

(* Notations to avoid typeclass resolution taking forever. *)
Notation configuration := (@configuration loc info _ _ _ _ _ _ _).
Notation robogram := (@robogram loc info _ _ _ _ _ _ _).
Notation execution := (@execution loc info _ _ _ _ _ _).
Notation map_config := (@map_config loc info _ _ _ _ _ _ _).
Notation app := (@app _ _ _ _ _ _ Info).


(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it wishes,
    and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : B -> loc * info;
  step : ident → option ((loc → similarity loc) (* change of referential *)
                               * R); (* travel ratio (rigid or flexible moves) *)
  step_compat : Proper (Logic.eq ==> opt_eq ((equiv ==> equiv) * (@eq R))) step;
(* FIXME: Use Proper (Logic.eq ==> opt_eq ((eq ==> equiv) * (@eq R))) instead? *)
  step_zoom :  forall id sim c, step id = Some sim -> (fst sim c).(zoom) <> 0%R;
  step_center : forall id sim c, step id = Some sim -> (fst sim c).(center) == c;
  step_flexibility : forall id sim, step id = Some sim -> (0 <= snd sim <= 1)%R}.

Global Instance da_Setoid : Setoid demonic_action := {|
  equiv := fun (da1 da2 : demonic_action) =>
           (forall id, opt_eq ((equiv ==> equiv) * eq)%signature (da1.(step) id) (da2.(step) id)) /\
           (forall b : B, da1.(relocate_byz) b == da2.(relocate_byz) b) |}.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros da1 da2 [Hda1 Hda2]. split; intros; try symmetry; auto; [].
  repeat intro; auto.
  specialize (Hda1 id). destruct (step da1 id), (step da2 id); trivial; [].
  destruct Hda1 as [Hda1 ?]. split; auto.
  intros x y Hxy. simpl in Hda1. symmetry in Hxy |- *. now apply Hda1 in Hxy.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4]. split; intros; try etransitivity; eauto; [].
  specialize (Hda1 id). specialize (Hda3 id).
  destruct (step da1 id), (step da2 id), (step da3 id); simpl in *; trivial; [|].
  - destruct Hda1 as [Hda1 Hda1']. split.
    * intros x y Hxy z. cbn. rewrite (Hda1 _ _ (reflexivity x) z). now apply Hda3.
    * rewrite Hda1'. now destruct Hda3.
  - elim Hda1.
Defined.

Global Instance step_da_compat : Proper (equiv ==> Logic.eq ==> opt_eq ((equiv ==> equiv) * eq)) step.
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
Lemma Between_mon : forall id id' (d : demon) k,
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
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; destruct H.
- intros. now apply Between_mon with k.
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
Definition FullySynchronousInstant : demon -> Prop := Stream.instant (fun da => forall g, step da g ≠ None).

(** A demon is fully synchronous if it is fully synchronous at all step. *)
Definition FullySynchronous : demon -> Prop := Stream.forever FullySynchronousInstant.

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
    is used for byzantine robots.
    
    As similarities preserve distance ratios, we can perform the multiplication by [mv_ratio]
    either in the local frame or in the global one. *)
Definition round (δ : R) (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let loc_info := config id in  (** loc is the current location of id seen by the demon *)
    match da.(step) id with          (** first see whether the robot is activated *)
      | None => loc_info          (** If id is not activated, do nothing *)
      | Some (sim, mv_ratio) =>      (** id is activated with similarity [sim (config id)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robots are relocated by the demon *)
        | Good g => (* configuration expressed in the frame of g *)
          let frame_change := sim (fst (config (Good g))) in
          let local_config := map_config frame_change config in
          (* apply r on spectrum *)
          let local_target := r (spect_from_config local_config) in
          (* the demon chooses a point on the line from the target by mv_ratio *)
          let chosen_target := mul mv_ratio local_target in
          (* back to demon ref *)
          (frame_change⁻¹ (if Rle_bool δ (dist (frame_change⁻¹ chosen_target) (fst loc_info))
                           then chosen_target else local_target),
           app frame_change (snd loc_info))
        end
    end.


Global Instance round_compat : Proper (Logic.eq ==> equiv ==> equiv ==> equiv ==> equiv) round.
Proof.
intros ? δ ? r1 r2 Hr da1 da2 Hda config1 config2 Hconfig id.
subst. unfold round.
assert (Hstep := step_da_compat Hda (reflexivity id)).
destruct (step da1 id) as [[sim1 ratio1] |], (step da2 id) as [[sim2 ratio2] |], id; try (now elim Hstep); [|].
* destruct Hstep as [Hstep Hratio]. unfold RelCompFun in Hstep, Hratio. cbn [fst snd] in Hstep, Hratio.
  assert (Htest :
      Rle_bool δ
       (dist ((sim1 (fst (config1 (Good g))) ⁻¹)
                (mul ratio1 (r1 (spect_from_config (map_config (sim1 (fst (config1 (Good g)))) config1)))))
             (fst (config1 (Good g))))
    = Rle_bool δ
        (dist ((sim2 (fst (config2 (Good g))) ⁻¹)
                 (mul ratio2 (r2 (spect_from_config (map_config (sim2 (fst (config2 (Good g)))) config2)))))
              (fst (config2 (Good g))))).
  { assert (Heq : fst (config1 (Good g)) == fst (config2 (Good g))) by now f_equiv; apply Hconfig.
    f_equal. apply dist_compat; trivial; [].
    apply Hstep in Heq. rewrite Heq. f_equiv. apply mul_compat; trivial; [].
    etransitivity; try apply Hr; []. apply pgm_compat. f_equiv.
    apply map_config_compat; trivial; []. apply Bijection.section_compat. }
  split; cbn [fst snd].
  + f_equiv.
    - do 2 f_equiv. apply Hstep. f_equiv. apply Hconfig.
    - rewrite Htest. destruct_match_eq Hcase.
      ++ apply mul_compat; trivial; [].
         etransitivity; try apply Hr; [].
         apply pgm_compat. f_equiv. apply map_config_compat; trivial; [].
         intros x y Hxy. f_equiv; trivial; []. intro z. apply Hstep, Hconfig.
      ++ etransitivity; try apply Hr; [].
         apply pgm_compat. f_equiv. apply map_config_compat; trivial; [].
         intros x y Hxy. f_equiv; trivial; []. intro z. apply Hstep, Hconfig.
  + apply app_compat.
    - do 2 f_equiv. apply Hstep. f_equiv. apply Hconfig.
    - f_equiv. apply Hconfig.
* now rewrite Hda.
Qed.

(** A third subset of robots, moving ones *)
Definition moving δ r da config := List.filter
  (fun id => if equiv_dec (round δ r da config id) (config id) then false else true)
  names.

Global Instance moving_compat : Proper (Logic.eq ==> equiv ==> equiv ==> equiv ==> equiv) moving.
Proof.
intros ? δ ? r1 r2 Hr da1 da2 Hda c1 c2 Hc. subst. unfold moving.
induction names as [| id l]; simpl.
* reflexivity.
* destruct (equiv_dec (round δ r1 da1 c1 id) (c1 id)) as [Heq1 | Heq1],
           (equiv_dec (round δ r2 da2 c2 id) (c2 id)) as [Heq2 | Heq2].
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
  List.In id (moving δ r da config) <-> round δ r da config id =/= config id.
Proof.
intros δ r da config id. unfold moving. rewrite List.filter_In.
split; intro H.
+ destruct H as [_ H].
  destruct (equiv_dec (round δ r da config id) (config id)) as [_ | Hneq]; intuition.
+ split.
  - apply In_names.
  - destruct (equiv_dec (round δ r da config id) (config id)) as [Heq | _]; intuition.
Qed.

Lemma moving_active : forall δ r da config, List.incl (moving δ r da config) (active da).
Proof.
intros δ r config da id. rewrite moving_spec, active_spec. intro Hmove.
unfold round in Hmove. destruct (step config id).
- discriminate.
- now elim Hmove.
Qed.

(** Some results *)

Lemma no_active_same_config : forall δ r da conf,
  active da = List.nil -> round δ r da conf == conf.
Proof.
intros δ r da conf Hactive.
assert (Hnone : forall id, step da id = None).
{ intro id. destruct (step da id) eqn:Heq; trivial; []. exfalso.
  assert (Hin : step da id <> None) by (rewrite Heq; discriminate).
  rewrite <- active_spec, Hactive in Hin. intuition. }
intro id. unfold round. now rewrite (Hnone id).
Qed.


(** [execute r d config] returns an (infinite) execution from an initial global
    configuration [config], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute δ (r : robogram) : demon -> configuration -> execution :=
  cofix execute d config :=
  Stream.cons config (execute (Stream.tl d) (round δ r (Stream.hd d) config)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall δ (r : robogram) (d : demon) (config : configuration),
  Stream.tl (execute δ r d config) = execute δ r (Stream.tl d) (round δ r (Stream.hd d) config).
Proof. intros. destruct d. reflexivity. Qed.

Global Instance execute_compat : Proper (Logic.eq ==> equiv ==> equiv ==> equiv ==> equiv) execute.
Proof.
intros ? δ ? r1 r2 Hr. subst.
cofix proof. constructor.
+ simpl. assumption.
+ apply proof; clear proof.
  - now inversion H.
  - apply round_compat; trivial. now inversion H.
Qed.

End FlexibleFormalism.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
