(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
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
Require Import Pactole.PointedMultisetSpectrum.
Require Stream.
(* Record graph_iso :=  *)


       
Module DGF (Graph : GraphDef)
           (N : Size)
           (Names : Robots(N))
           (LocationA : LocationADef(Graph))
           (MkInfoA : UnitSig(Graph)(LocationA))
           (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA.Info))
           (SpectA : PointedSpectrum(LocationA)(N)(Names)(MkInfoA.Info)(ConfigA))
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
  Module Info := Unit.
  Module Config := ConfigA.
  Module Spect :=  SpectA.
 


  Record robogram :=
    {
      pgm :> Spect.t -> Location.t;
      pgm_compat : Proper (Spect.eq ==> Location.eq) pgm;
      pgm_range : forall (spect: Spect.t),
          exists lpost e, pgm spect = lpost
                          /\ (opt_eq Graph.Eeq (Graph.find_edge (Spect.get_current spect)
                                                                lpost)
                                     (Some e)) }.

  (* pgm s l a du dens si l est dans dans s (s[l] > 0)
     si l n'est pas occupée par un robot, on doit revoyer un voisin (à cause de pgm_range). *)
  
  Global Existing Instance pgm_compat.

  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  
  Instance req_equiv : Equivalence req.
  Proof.
    split.
    + intros [robogram Hrobogram] g1 g2 Hg; simpl. rewrite Hg. reflexivity.
    + intros r1 r2 Hr g1 g2 Hg. rewrite Hg.
      unfold req in Hr.
      now specialize (Hr g2 g2 (reflexivity g2)).
    + intros r1 r2 r3 H1 H2 g1 g2 Hg.
      specialize (H1 g1 g2 Hg). 
      specialize (H2 g2 g2 (reflexivity g2)).
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
      step : Names.ident → option (Config.RobotConf -> Iso.t);
      step_compat : Proper (eq ==> opt_eq (Config.eq_RobotConf ==> Iso.eq)) step
    }.
  Set Implicit Arguments.
  
  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id, opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature
                       (da1.(step) id) (da2.(step) id)) /\
  (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).
  
  Instance da_eq_equiv : Equivalence da_eq.
  Proof.
    split.
    + split. intros id.
      simpl. apply step_compat. easy. intuition.
    + intros d1 d2 [H1 H2]. split; repeat intro; try symmetry; auto; [].
      specialize (H1 id). destruct (step d1 id), (step d2 id); trivial.
      intros x y Hxy. simpl in H1. symmetry. apply H1. now symmetry.
    + intros d1 d2 d3 [H1 H2] [H3 H4]. split; intros; try etransitivity; eauto; [].
      specialize (H1 id). specialize (H3 id). destruct (step d1 id), (step d2 id), (step d3 id); simpl in *; trivial.
    - simpl in *. intros x y Hxy. rewrite (H1 _ _ (reflexivity x)). now apply H3.
    - elim H1.
Qed.

  
  Instance step_da_compat : Proper (da_eq ==> eq ==> (opt_eq (Config.eq_RobotConf ==> Iso.eq))) step.
  Proof. intros da1 da2 [Hd1 Hd2] p1 p2 Hp. subst. apply Hd1. Qed.
  
  Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
  Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.
  
  Lemma da_eq_step_Idle : forall da1 da2,
      da_eq da1 da2 -> 
      forall id,
        opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature (step da1 id) None <-> 
        opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature (step da2 id) None.
  Proof.
    intros da1 da2 Hda id.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
    split; intro Hidle; simpl in *.
    unfold opt_eq in *;
    destruct (step da1 id), (step da2 id); try easy.
    unfold opt_eq in *;
    destruct (step da1 id), (step da2 id); try easy.
  Qed.

  Lemma da_eq_step_Active : forall da1 da2,
      da_eq da1 da2 -> 
      forall id sim,
        opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature
               (step da1 id) (Some sim) <-> 
        opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature
               (step da2 id) (Some sim).
  Proof.
    intros da1 da2 Hda id sim.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id)).
    split; intro Hidle.
    unfold opt_eq in *.
    destruct (step da1 id), (step da2 id); try easy.
    intros x y Hxy.
    specialize (Hopt_eq y x (symmetry Hxy)); specialize (Hidle y y (reflexivity _)).
    rewrite <- Hidle. now symmetry.
    unfold opt_eq in *.
    destruct (step da1 id), (step da2 id); try easy.
    intros x y Hxy.
    specialize (Hopt_eq x y Hxy); specialize (Hidle y y (reflexivity _)).
    now rewrite <- Hidle.
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
       Config.state := Config.state infoR
    |}.
  
  Instance apply_sim_compat : Proper (Iso.eq ==> Config.eq_RobotConf ==> Config.eq_RobotConf) apply_sim.
  Proof.
    intros sim sim' Hsim conf conf' Hconf. unfold apply_sim. hnf. split; simpl.
    - apply Hsim, Hconf.
    - apply Hconf.
  Qed.
  Global Notation "s ⁻¹" := (Iso.inverse s) (at level 99).
  
  Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
    (** for a given robot, we compute the new configuration *)
    fun id =>
      let rconf := config id in
      let pos := rconf.(Config.loc) in
    match da.(step) id with (** first see whether the robot is activated *)
      | None => rconf (** If g is not activated, do nothing *)
      | Some sim => (** g is activated and [sim (conf g)] is its similarity *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robots are relocated by the demon *)
        | Good g =>
          let local_config := Config.map (apply_sim (sim rconf)) config in
          let local_target := (r ((Spect.from_config local_config) (Config.loc (local_config (Good g))))) in
          let target := ((sim rconf)⁻¹).(Iso.sim_V) local_target in (* configuration expressed in the frame of g *)
          {| Config.loc := target;
             Config.state := Config.state rconf |}
        end
    end. (** for a given robot, we compute the new configuration *)
  
  Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
  Proof.
    intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
    unfold req in Hr.
    unfold round.
    assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
    { apply Hconf. }
    assert (Hstep := step_da_compat Hda (reflexivity id)).
    assert (Hsim: opt_eq (Config.eq_RobotConf ==> Iso.eq)%signature
                         (step da1 id) (step da1 id)).
    { apply step_da_compat; try reflexivity.
    }
    destruct (step da1 id ) eqn : He1, (step da2 id) eqn:He2;
      destruct (step da1 id) eqn:He3, id as [ g| b]; try now elim Hstep.
    + simpl in *. 
      assert (Hasc := apply_sim_compat (Hstep _ _ Hrconf)).
      assert (Hsfcc := Spect.from_config_compat
                         (Config.map (apply_sim (t (conf1 (Good g)))) conf1)
                         (Config.map (apply_sim (t0 (conf2 (Good g)))) conf2)
                         (Config.map_compat (apply_sim (t (conf1 (Good g))))
                                            (apply_sim (t0 (conf2 (Good g))))
                                            Hasc
                                            conf1 conf2 Hconf)).
      repeat split; simpl.
      - f_equiv.
        apply Hstep.
        apply Hrconf.
        apply Hr.
        apply Hsfcc.
        apply Hstep.
        apply Hconf.
        apply Hrconf.
      - apply Hconf.
    + rewrite Hda. now destruct (Hconf (Byz b)).
    + simpl in *. 
      assert (Hasc := apply_sim_compat (Hstep _ _ Hrconf)).
      assert (Hsfcc := Spect.from_config_compat
                         (Config.map (apply_sim (t (conf1 (Good g)))) conf1)
                         (Config.map (apply_sim (t0 (conf2 (Good g)))) conf2)
                         (Config.map_compat (apply_sim (t (conf1 (Good g))))
                                            (apply_sim (t0 (conf2 (Good g))))
                                            Hasc
                                            conf1 conf2 Hconf)).
      repeat split; simpl.
      - f_equiv.
        apply Hstep.
        apply Hrconf.
        apply Hr.
        apply Hsfcc.
        apply Hstep.
        apply Hconf.
        apply Hrconf.
      - apply Hconf.
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
  
(** A [demon] is [Fair] if at any time it will later activate any robot. *)
(* RMK: This is a stronger version of eventually because P is negated in the Later clause *)
Inductive LocallyFairForOne g (d : demon) : Prop :=
  | NowFair : step (Stream.hd d) g ≠ None → LocallyFairForOne g d
  | LaterFair : step (Stream.hd d) g = None → LocallyFairForOne g (Stream.tl d) → LocallyFairForOne g d.

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
+ constructor 1.
  destruct Hda.
  assert (HdaI := da_eq_step_Idle H0 g).
  unfold opt_eq in *.
  destruct (step (Stream.hd d) g), (step (Stream.hd da2) g); try easy.
  intuition.
+ constructor 2.
  - destruct Hda.
    assert (HdaI := da_eq_step_Idle H0 g).
    unfold opt_eq in *.
    destruct (step (Stream.hd d) g), (step (Stream.hd da2) g); try easy.
    intuition.
  - apply IHHfair. now f_equiv.
Qed.

Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. apply Stream.forever_compat. intros ? ? Heq. now setoid_rewrite Heq. Qed.

Lemma Between_compat_aux : forall g h k d1 d2, deq d1 d2 -> Between g h d1 k -> Between g h d2 k.
Proof.
intros g h k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
+ constructor 1.
  destruct Heq.
  assert (HdaI := da_eq_step_Idle H0 g).
  unfold opt_eq in *.
  destruct (step (Stream.hd d) g), (step (Stream.hd d2) g); try easy.
  intuition.
+ constructor 2.
  - destruct Heq.
    assert (HdaI := da_eq_step_Idle H1 g).
    unfold opt_eq in *.
    destruct (step (Stream.hd d) g), (step (Stream.hd d2) g); try easy.
    intuition.
  - destruct Heq.
    assert (HdaI := da_eq_step_Idle H1 h).
    unfold opt_eq in *.
    destruct (step (Stream.hd d) h), (step (Stream.hd d2) h); try easy.
    intuition. 
  - apply IHbet. now f_equiv.
+ constructor 3.
  - destruct Heq.
    assert (HdaI := da_eq_step_Idle H1 g).
    unfold opt_eq in *.
    destruct (step (Stream.hd d) g), (step (Stream.hd d2) g); try easy.
    intuition.
  - destruct Heq.
    assert (HdaI := da_eq_step_Idle H1 h).
    unfold opt_eq in *.
    destruct (step (Stream.hd d) h), (step (Stream.hd d2) h); try easy.
    intuition. 
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
    
End DGF.
