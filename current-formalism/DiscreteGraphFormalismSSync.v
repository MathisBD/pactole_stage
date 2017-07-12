(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
(* Require Import Pactole.CommonFormalism. *)
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.Isomorphism.
Require Import Pactole.CommonIsoGraphFormalism.
Require MMapWeakList. (* to build an actual implementation of multisets *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import SetoidList.
Require MMultisetInterface.
Require MMultisetExtraOps.
Require MMultisetWMap.
Require Import MMaps.MMapInterface.
Require Import MMultiset.MMultisetInterface.
Require Import MMultiset.MMultisetExtraOps.
Require Pactole.MMultiset.MMultisetFacts.
Require Stream.
(* Record graph_iso :=  *)


Module DGF (Graph : GraphDef)
           (N : Size)
           (Names : Robots(N))
           (LocationA : LocationADef(Graph))
           (MkInfoA : InfoSig(Graph)(LocationA))
           (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA.Info))
           (SpectA : Spectrum(LocationA)(N)(Names)(MkInfoA.Info)(ConfigA))
           (Import Iso : Iso(Graph) (LocationA)).
           
  
  (** For spectra *)
  Module View : DecidableType with Definition t := ConfigA.t with Definition eq := ConfigA.eq.
    Definition t := ConfigA.t.
    Definition eq := ConfigA.eq.
    Definition eq_equiv := ConfigA.eq_equiv.
    Definition eq_dec := ConfigA.eq_dec.
  End View.



  (* They come from the common part as they are shared by AGF and DGF. *)
  Module InfoA := MkInfoA.Info.
  Module Location := LocationA.
  Module Info := InfoA.
  Module Config := ConfigA.
  Module Spect :=  SpectA.
  
 


  Record robogram :=
    {
      pgm :> Spect.t -> Location.t -> Location.t;
      pgm_compat : Proper (Spect.eq ==> Location.eq ==> Location.eq) pgm;
      pgm_range : forall spect lpre,
          exists lpost e, pgm spect lpre = lpost
                          /\ (opt_eq Graph.Eeq (Graph.find_edge lpre lpost) (Some e))
    }.

  (* pgm s l a du dens si l est dans dans s (s[l] > 0)
     si l n'est pas occupée par un robot, on doit revoyer un voisin (à cause de pgm_range). *)
  
  Global Existing Instance pgm_compat.

  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq ==> Location.eq)%signature r1 r2.
  
  Instance req_equiv : Equivalence req.
  Proof.
    split.
    + intros [robogram Hrobogram] x y Heq g1 g2 Hg; simpl. rewrite Hg, Heq. reflexivity.
    + intros r1 r2 H x y Heq g1 g2 Hg. rewrite Hg, Heq.
      unfold req in H.
      now specialize (H y y (reflexivity y) g2 g2 (reflexivity g2)).
    + intros r1 r2 r3 H1 H2 x y Heq g1 g2 Hg.
      specialize (H1 x y Heq g1 g2 Hg). 
      specialize (H2 y y (reflexivity y) g2 g2 (reflexivity g2)).
      now rewrite H1.
  Qed.
  
  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  Definition execution := Stream.t Config.t.
 
  Definition eeq : execution -> execution -> Prop := Stream.eq Config.eq.

  Instance eeq_equiv : Equivalence eeq.
  Proof.
    split.
    + coinduction eeq_refl. reflexivity.
    + coinduction eeq_sym. symmetry. now inversion H. now inversion H.
    + coinduction eeq_trans. 
    - inversion H. inversion H0. now transitivity (Stream.hd y).
    - apply (eeq_trans (Stream.tl x) (Stream.tl y) (Stream.tl z)).
      now inversion H. now inversion H0.
  Qed.
  
  Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@Stream.hd _ ).
  Proof. apply Stream.hd_compat. Qed.
  
  Instance eeq_tl_compat : Proper (eeq ==> eeq) (@Stream.tl _).
  Proof. apply Stream.tl_compat. Qed.
  
  (** ** Demonic schedulers *)
  
  (** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
 
  
  Record demonic_action :=
    {
      relocate_byz : Names.B -> Config.RobotConf;
      step : Names.ident → Config.RobotConf -> option (Iso.t);
      step_compat : Proper (eq ==> Config.eq_RobotConf ==> opt_eq (Iso.eq)) step
    }.
  Set Implicit Arguments.
  
  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id rc, opt_eq (Iso.eq)%signature (da1.(step) id rc) (da2.(step) id rc)) /\
  (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).
  
  Instance da_eq_equiv : Equivalence da_eq.
  Proof.
    split.
    + split; intuition.
    + intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto.
    + intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
      split; intros; try etransitivity; eauto.
  Qed.
  
  Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> (opt_eq (Iso.eq))) step.
  Proof.
    intros da1 da2 [Hstep Hrel] id1 id2 Hid x y Hxy. subst.
    specialize (Hstep id2 x).    
    unfold opt_eq in *.
    destruct (step da1 id2 x) eqn : Hs1, (step da2 id2 x) eqn : Hs2; try easy.
    assert (opt_eq (Iso.eq)%signature (step da2 id2 x) (Some t0)).
    rewrite <- Hs2; try apply da_eq_equiv.
    assert (Hc :=  (step_compat da2 _ _ (reflexivity id2) x y Hxy)).
    rewrite Hs2 in Hc.
    destruct (step da2 id2 y).
    simpl in *.
    now rewrite Hstep, Hc.
    now simpl in *.
    destruct (step da2 id2 y) eqn : Hs.
    assert (Hc := step_compat da2 _ _ (reflexivity id2) x  y Hxy).
    now rewrite Hs, Hs2 in Hc.
    auto.
  Qed.
  
  Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
  Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.
  
  Lemma da_eq_step_Idle : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config,
        opt_eq (Iso.eq)%signature (step da1 id config) None <-> 
        opt_eq (Iso.eq)%signature (step da2 id config) None.
  Proof.
    intros da1 da2 Hda id config.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle; simpl in *.
    unfold opt_eq in *;
    destruct (step da1 id config), (step da2 id config); try easy.
    unfold opt_eq in *;
    destruct (step da1 id config), (step da2 id config); try easy.
  Qed.

  Lemma da_eq_step_Active : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config sim,
        opt_eq (Iso.eq)%signature
               (step da1 id config) (Some sim) <-> 
        opt_eq (Iso.eq)%signature
               (step da2 id config) (Some sim).
  Proof.
    intros da1 da2 Hda id config sim.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle.
    unfold opt_eq in *.
    destruct (step da1 id config), (step da2 id config); try easy.
    now rewrite Hidle in Hopt_eq; symmetry.
    unfold opt_eq in *.
    destruct (step da1 id config), (step da2 id config); try easy.
    now rewrite Hidle in Hopt_eq.
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
  
  Definition apply_sim (sim : Iso.t) (infoR : Config.RobotConf) :=
    {| Config.loc := (Iso.sim_V sim) (Config.loc infoR);
       Config.info :=
         {| Info.source := (Iso.sim_V sim) (Info.source (Config.info infoR));
            Info.target := (Iso.sim_V sim) (Info.target (Config.info infoR))
         |}
    |}.
  
  Instance apply_sim_compat : Proper (Iso.eq ==> Config.eq_RobotConf ==> Config.eq_RobotConf) apply_sim.
  Proof.
    intros sim sim' Hsim conf conf' Hconf. unfold apply_sim. hnf. split; simpl.
    - apply Hsim, Hconf.
    - split; apply Hsim, Hconf.
  Qed.
  Global Notation "s ⁻¹" := (Iso.inverse s) (at level 99).
  
  Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
    (** for a given robot, we compute the new configuration *)
    fun id =>
      let rconf := config id in
      let pos := rconf.(Config.loc) in
    match da.(step) id rconf with (** first see whether the robot is activated *)
      | None => rconf (** If g is not activated, do nothing *)
      | Some sim => (** g is activated and [sim (conf g)] is its similarity *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robots are relocated by the demon *)
        | Good g =>
          let local_config := Config.map (apply_sim sim) config in
          let local_target := (r (Spect.from_config local_config) (Config.loc (local_config (Good g)))) in
          let target := (sim⁻¹).(Iso.sim_V) local_target in (* configuration expressed in the frame of g *)
          {| Config.loc := target;
             Config.info := {| Info.source := pos ; Info.target := target|} |}
        end
    end. (** for a given robot, we compute the new configuration *)
  
  Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
  Proof.
    intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
    unfold req in Hr.
    unfold round.
    assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
    { apply Hconf. }
    assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
    assert (Hsim: opt_eq Iso.eq  (step da1 id (conf1 id)) (step da1 id (conf2 id))).
    { apply step_da_compat; try reflexivity.
      apply Hrconf.
    }
    destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2;
      destruct (step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
    + simpl in *. 
      assert (Hasc := apply_sim_compat Hstep).
      assert (Hsfcc := Spect.from_config_compat
                         (Config.map (apply_sim t) conf1)
                         (Config.map (apply_sim t0) conf2)
                         (Config.map_compat (apply_sim t) (apply_sim t0) Hasc
                                            conf1 conf2 Hconf)).
      repeat split; simpl.
      - f_equiv.
        apply Hstep.
        apply Hr.
        apply Hsfcc.
        apply Hstep.
        apply Hconf.
      - apply Hconf.
      - f_equiv.
        apply Hstep.
        apply Hr.
        apply Hsfcc.
        apply Hstep.
        apply Hconf.
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
(* Inductive LocallyFairForOne g (d : demon) config : Prop :=
  | NowFair : step (Stream.hd d) g (config (Good g)) ≠ None → LocallyFairForOne g d config
  | LaterFair : step (Stream.hd d) g (conig (Good g)) = None → LocallyFairForOne g (Stream.tl d) (Stream.hd (Stream.tl (execute r d config))) → LocallyFairForOne g d config.

Definition Fair : demon -> Prop := Stream.forever (fun d => ∀ g, LocallyFairForOne g d).

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k, step (Stream.hd d) g <> None -> Between g h d k
| kReduce : forall k, step (Stream.hd d) g = None -> step (Stream.hd d) h <> None ->
                      Between g h (Stream.tl d) k -> Between g h d (S k)
| kStall : forall k, step (Stream.hd d) g = None -> step (Stream.hd d) h = None ->
                     Between g h (Stream.tl d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
Definition kFair k : demon -> Prop := Stream.forever (fun d => forall g h, Between g h d k).

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

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

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

Instance kFair_compat : Proper (eq ==> deq ==> iff) kFair.
Proof. intros k ? ?. subst. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof. intros g h d k Hg. induction Hg; now constructor. Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof. intros g d k Hd. induction Hd; now constructor. Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof. intro. apply Stream.forever_impl_compat. intros. eauto using (@Between_LocallyFair g _ g). Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
intros g h d k Hd. induction Hd; intros k' Hk.
+ now constructor 1.
+ destruct k'.
  - now inversion Hk.
  - constructor 2; assumption || now (apply IHHd; omega).
+ constructor 3; assumption || now (apply IHHd; omega).
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
  forall g h, (Stream.hd d).(step) g = None <-> (Stream.hd d).(step) h = None.
Proof.
intros d Hd g h. destruct Hd as [Hd _]. split; intro H.
- assert (Hg := Hd g h). inversion Hg. contradiction. assumption.
- assert (Hh := Hd h g). inversion Hh. contradiction. assumption.
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
*)  
End DGF.
