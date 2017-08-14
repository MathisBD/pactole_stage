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

Instance Info2 : Information V (V * info) := @pair_Information V V info _ _ _ _ (Target V) _ _ Info.

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
  | Moving (dist : bool)                  (* moving ratio, the model equivalence uses the "false" case *)
  | Active (iso : @isomorphism V E G).    (* change of referential *)

Instance Active_or_Moving_Setoid : Setoid Active_or_Moving := {
  equiv := fun a1 a2 =>
    match a1, a2 with
      | Moving d1, Moving d2 => d1 = d2
      | Active sim1, Active sim2 => sim1 == sim2
      | _, _ => False
    end }.

Instance Active_compat : Proper (Iso.eq ==> Aom_eq) Active.
Proof. intros ? ? ?. auto. Qed.

Instance Aom_eq_equiv : Equivalence Aom_eq.
Proof. split.
+ now intros [].
+ intros x y H. unfold Aom_eq in *. destruct x, y; auto. now symmetry.
+ intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
  now rewrite H12, H23.
Qed.

(* on a besoin de Rconfig car ça permet de faire la conversion d'un modèle à l'autre *)

Record demonic_action :=
  {
    relocate_byz : Names.B -> Config.RobotConf;
    step : Names.ident -> Config.RobotConf -> Active_or_Moving;
    step_delta : forall g Rconfig sim,
        Aom_eq (step (Good g) Rconfig) (Active sim) ->
        Location.eq Rconfig.(Config.loc) Rconfig.(Config.state).(Info.target);
    step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step
  }.
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
  (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof.
  split.
  + now split.
  + intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto.
  + intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
    split; intros; try etransitivity; eauto.
Qed.

Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
Proof.
  intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
  etransitivity.
  - apply Hd1.
  - apply (step_compat da2); auto.
Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_Moving : forall da1 da2,
    da_eq da1 da2 -> 
    forall id config r,
      Aom_eq (step da1 id config) (Moving r) <-> 
      Aom_eq (step da2 id config) (Moving r).
Proof.
  intros da1 da2 Hda id config r.
  assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
  split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; now auto.
Qed.

Lemma da_eq_step_Active : forall da1 da2,
    da_eq da1 da2 -> 
    forall id config sim,
      Aom_eq (step da1 id config) (Active sim) <-> 
      Aom_eq (step da2 id config) (Active sim).
Proof.
  intros da1 da2 Hda id config sim.
  assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
  split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step;
    reflexivity || elim Hopt_eq; now intros; simpl.
Qed.

(** A [demon] is just a stream of [demonic_action]s. *)
Definition demon := Stream.t demonic_action.

Definition deq (d1 d2 : demon) : Prop := Stream.eq da_eq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. apply Stream.eq_equiv, da_eq_equiv. Qed.

Instance demon_hd_compat : Proper (deq ==> da_eq) (@Stream.hd _) :=
Stream.hd_compat _.

Instance demon_tl_compat : Proper (deq ==> deq) (@Stream.tl _) :=
  Stream.tl_compat _.

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

Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let rconf := config id in
    let pos := rconf.(Config.loc) in
    match da.(step) id rconf with (** first see whether the robot is activated *)
    | Moving false => rconf
    | Moving true =>
      match id with
      | Good g =>
        let tgt := rconf.(Config.state).(Info.target) in
        {| Config.loc := tgt ; Config.state := rconf.(Config.state) |}
      | Byz b => rconf
      end
    | Active sim => (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
      match id with
      | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
      | Good g =>
        let local_config := Config.map (Config.app sim) config in
        let local_target := (r (Spect.from_config local_config) (Config.loc (local_config (Good g)))) in
        let target := (sim⁻¹).(Iso.sim_V) local_target in
(* This if is unnecessary: with the invariant on da: inside rconf, loc = target *)
(*           if (Location.eq_dec (target) pos) then rconf else *)
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
  destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2;
    destruct (step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
  + unfold Aom_eq in *.
    rewrite Hstep.
    destruct dist0.
    f_equiv;
      apply Hrconf.
    apply Hrconf.
  + unfold Aom_eq in *.
    rewrite Hstep.
    destruct dist0; apply Hrconf.
  + assert (Location.eq (((Iso.sim_V (sim ⁻¹))
          (r1 (Spect.from_config (Config.map (Config.app sim) conf1))
              (Config.loc (Config.map (Config.app sim) conf1 (Good g))))))
                        (((Iso.sim_V (sim0 ⁻¹))
          (r2 (Spect.from_config (Config.map (Config.app sim0) conf2))
              (Config.loc (Config.map (Config.app sim0) conf2 (Good g))))))).
    f_equiv.
    simpl in Hstep.
    f_equiv.
    f_equiv.
    apply Hstep.
    apply Hr. now repeat f_equiv.
    apply Config.map_compat.
    apply Config.app_compat.
    apply Hstep.
    apply Hconf.
    repeat split; simpl; f_equiv; try apply Hconf; [|].
    - now f_equiv.
    - apply Hr. repeat (f_equiv; trivial). now do 2 f_equiv.
  + rewrite Hda. now destruct (Hconf (Byz b)).
Qed.


(** [execute r d conf] returns an (infinite) execution from an initial global
  configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon -> Config.t -> execution :=
  cofix execute d conf :=
    Stream.cons conf (execute (Stream.tl d) (round r (Stream.hd d) conf)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
    Stream.tl (execute r d conf) = execute r (Stream.tl d) (round r (Stream.hd d) conf).
Proof. intros. destruct d. reflexivity. Qed.

Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
  intros r1 r2 Hr.
  cofix proof. constructor. simpl. assumption.
  apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.

(** ** Fairness *)

(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     changer execution en un (execute r d config) 
   !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne g (d : demon) r e : Prop :=
| ImmediatelyFair :
    (exists conf,
      eeq (execute r d conf) e) -> 
    (exists sim,
        Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                (Good g))) (Active sim))
    → LocallyFairForOne g d r e
| LaterFair :
    (exists conf,
      eeq (execute r d conf) e) -> 
    (exists dist,
        Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)))
               (Moving dist))
    → LocallyFairForOne g (Stream.tl d) r (Stream.tl e)
    → LocallyFairForOne g d r e.

CoInductive Fair (d : demon) r e : Prop :=
  AlwaysFair : (∀ g, LocallyFairForOne g d r e) →
               Fair (Stream.tl d) r (Stream.tl e) →
               Fair d r e.

(** [Between g h d] means that [g] will be activated before at most [k]
  steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) r e: nat -> Prop :=
| kReset : forall k,
    (exists conf,
      eeq (execute r d conf) e) -> 
    (exists sim, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)))
                        (Active sim))
    -> Between g h d r e k 
| kReduce : forall k,
    (exists conf,
      eeq (execute r d conf) e) -> 
    (exists dist, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                          (Good g)))
                         (Moving dist))
    -> (exists sim, Aom_eq (step (Stream.hd d) (Good h) ((Stream.hd e)
                                                            (Good h)))
                           (Active sim))
    -> Between g h (Stream.tl d) r (Stream.tl e) k -> Between g h d r e (S k)
| kStall : forall k,
    (exists conf,
      eeq (execute r d conf) e) -> 
    (exists dist, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                          (Good g)))
                         (Moving dist)) -> 
    (exists dist, Aom_eq (step (Stream.hd d) (Good h) ((Stream.hd e)
                                                          (Good h)))
                         (Moving dist)) ->
    Between g h (Stream.tl d) r (Stream.tl e) k -> Between g h d r e k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) r e: Prop :=
  AlwayskFair : (forall g h, Between g h d r e k) ->
                kFair k (Stream.tl d)r  (Stream.tl e) ->
                kFair k d r e.

Lemma LocallyFairForOne_compat_aux : forall g d1 d2 e1 e2 r1 r2,
    deq d1 d2 -> eeq e1 e2 -> req r1 r2 -> 
    LocallyFairForOne g d1 r1 e1 -> LocallyFairForOne g d2 r2 e2.
Proof.
  intros g da1 da2 e1 e2 r1 r2 Hda He Hr Hfair.
  revert da2 Hda e2 He r2 Hr. induction Hfair; intros da2 Hda.
  + constructor 1.
    destruct H.
    exists x.
    now rewrite <- He, <- Hr, <- Hda.
    destruct H0.
    exists x.
    rewrite <- He.
    rewrite da_eq_step_Active; try eassumption. now f_equiv.
  + constructor 2.
    destruct H.
    exists x.
    now rewrite <- He, <- Hr, <- Hda.
    destruct H0.
    exists x.
    rewrite <- He.
    rewrite da_eq_step_Moving; try eassumption. now f_equiv.
    apply IHHfair;
    now f_equiv.
Qed.

Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> req ==> eeq ==> iff) LocallyFairForOne.
Proof.
  repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Lemma Fair_compat_aux : forall d1 d2 e1 e2 r1 r2,
    deq d1 d2 -> eeq e1 e2 -> req r1 r2 -> Fair d1 r1 e1 -> Fair d2 r2 e2.
Proof.
  cofix be_fair. intros d1 d2 e1 e2 r1 r2 Hdeq Heeq Hreq Hfair.
  destruct Hfair as [Hnow Hlater]. constructor.
  + intros. now rewrite <- Hdeq, <- Heeq, <- Hreq.
  + eapply be_fair; try eassumption; now f_equiv.
Qed.

Instance Fair_compat : Proper (deq ==> req ==> eeq ==> iff) Fair.
Proof. repeat intro. split; intro; now eapply Fair_compat_aux; eauto. Qed.

Lemma Between_compat_aux : forall g h k d1 d2 r1 r2 e1 e2,
    deq d1 d2 -> eeq e1 e2 -> req r1 r2 ->
    Between g h d1 r1 e1 k -> Between g h d2 r2 e2 k.
Proof.
  intros g h k d1 d2 r1 r2 e1 e2 Hdeq Heeq Hreq bet.
  revert d2 Hdeq e2 Heeq r2 Hreq. induction bet; intros d2 Hdeq e2 Heeq.
  + constructor 1.
    destruct H.
    exists x.
    now rewrite <- Heeq, <- Hreq, <- Hdeq.
    destruct H0.
    exists x.
    rewrite <- Heeq.
    rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
  + constructor 2.
  - destruct H; exists x; now rewrite <- Heeq, <- Hreq, <- Hdeq.
  - destruct H0; exists x; rewrite <- Heeq;
      rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - destruct H1; exists x; rewrite <- Heeq;
      rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
  - apply IHbet; now f_equiv.
  + constructor 3.
  - destruct H; exists x; now rewrite <- Heeq, <- Hreq, <- Hdeq.
  - destruct H0; exists x; rewrite <- Heeq;
      rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - destruct H1; exists x; rewrite <- Heeq;
      rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
  - apply IHbet; now f_equiv.
Qed.

Instance Between_compat : Proper (eq ==> eq ==> deq ==> req ==> eeq ==> eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Lemma kFair_compat_aux : forall k d1 d2 r1 r2 e1 e2,
    deq d1 d2 -> req r1 r2 -> eeq e1 e2 -> kFair k d1 r1 e1 -> kFair k d2 r2 e2.
Proof.
  cofix be_fair. intros k d1 d2 e1 e2 r1 r2 Hdeq Hreq Heeq Hkfair.
  destruct Hkfair as [Hnow Hlater]. constructor.
  + intros. now rewrite <- Hdeq, <- Heeq, <- Hreq.
  + eapply be_fair; try eassumption; now f_equiv.
Qed.

Instance kFair_compat : Proper (eq ==> deq ==> req ==> eeq ==> iff) kFair.
Proof. repeat intro. subst. split; intro; now eapply kFair_compat_aux; eauto. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h r e k,
    Between g h d r e k -> LocallyFairForOne g d r e.
Proof.
  intros g h d r e k Hg. induction Hg.
  now constructor 1.
  now constructor 2.
  now constructor 2.
Qed.

(** A robot is never activated before itself with a fair demon! The
  fairness hypothesis is necessary, otherwise the robot may never be
  activated. *)
Lemma Between_same :
  forall g (d : demon) k r e, LocallyFairForOne g d r e -> Between g g d r e k.
Proof.
  intros g d r e k Hd. induction Hd.
  now constructor 1.
  now constructor 3.
Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon) r e, kFair k d r e -> Fair d r e.
Proof.
  coinduction kfair_is_fair.
  destruct H as [Hbetween H]. intro. apply Between_LocallyFair with g k.
  now apply Hbetween.
  apply (kfair_is_fair k). now destruct H.
Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) r e k,
    Between g h d r e k -> forall k', (k <= k')%nat -> Between g h d r e k'.
Proof.
  intros g h d r e k Hd. induction Hd; intros k' Hk.
  now constructor 1.
  destruct k'.
  now inversion Hk.
  constructor 2; assumption || now (apply IHHd; omega).
  constructor 3; assumption || now (apply IHHd; omega).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon) r e,
    kFair k d r e -> forall k', (k <= k')%nat -> kFair k' d r e.
Proof.
  coinduction fair; destruct H.
  - intros. now apply Between_mon with k.
  - now apply (fair k).
Qed.

Theorem Fair0 : forall d r e,
    (exists conf,
        eeq (execute r d conf) e) -> 
    kFair 0 d r e->
    forall g h,
      (exists dist,
          Aom_eq ((Stream.hd d).(step) (Good g) ((Stream.hd e) (Good g))) (Moving dist))
      <-> exists dist,
        Aom_eq ((Stream.hd d).(step) (Good h) ((Stream.hd e) (Good h))) (Moving dist).
Proof.
  intros d r e Hconf Hd g h. destruct Hd as [Hd _]. split; intro H.
  assert (Hg := Hd g h). inversion Hg. destruct H1, H.
  rewrite H in H1; now simpl in *.
  destruct H2; exists x. assumption.
  assert (Hh := Hd h g). inversion Hh. destruct H1, H.
  rewrite H in H1; now simpl in *.
  destruct H2; exists x. assumption.
Qed.

(** ** Full synchronicity

A fully synchronous demon is a particular case of fair demon: all good robots
are activated at each round. In our setting this means that the demon never
return a null reference. *)


(* (** A demon is fully synchronous for one particular good robot g at the first *)
(*     step. *) *)
(*   Inductive FullySynchronousForOne g d:Prop := *)
(*     ImmediatelyFair2: *)
(*       (step (Stream.hd d) g) ≠ None →  *)
(*       FullySynchronousForOne g d. *)

Definition StepSynchronism d e r : Prop := forall g,
    (exists conf,
        eeq (execute r d conf) e) -> 
    exists aom,
      ((exists sim, Aom_eq aom (Active sim)) \/ Aom_eq aom (Moving true)) /\
      step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)) = aom .

(** A demon is fully synchronous if it is fully synchronous for all good robots
  at all step. *)
CoInductive FullySynchronous d r e := 
  NextfullySynch:
    StepSynchronism d e r
    → FullySynchronous (Stream.tl d) r (Stream.tl e)
    → FullySynchronous d r e.

End DGF.
