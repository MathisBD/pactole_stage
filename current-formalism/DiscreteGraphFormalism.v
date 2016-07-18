Require Import Reals.
Require Import Omega.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
(* Require Import Pactole.CommonFormalism. *)
Require Import Pactole.CommonGraphFormalism.


(* Record graph_iso :=  *)


Module DGF.

Inductive location :=
  | Loc (l : V)
  | Mvt (e : E) (p : R) (* (Hp : (0 < p < 1)%R) *).

(* Axiom mvt0_1 : forall e p loc, loc = Mvt e p -> 0 < p < 1. *)

Parameter project_p : R -> R.
Axiom project_p_image : forall p, (0 < project_p p < 1)%R.
Parameter project_p_inv : R -> R.
Axiom inv_pro : forall p, (0 < p < 1)%R -> p = project_p (project_p_inv p).
Axiom pro_inv : forall p, p = project_p_inv (project_p p).
Axiom project_p_inv_image : forall p q, p = project_p_inv q -> (0 < q < 1)%R.
Axiom subj_proj : forall p q, p = project_p q <-> project_p_inv p = q.
Axiom proj_comm : forall p q, (project_p (p + q) = (project_p p) + (project_p q))%R.


(*Definition project_p (p : R) : R := p. fonction de R vers ]0;1[, par exemple utiliser arctan.*)

(* Lemma *)

Definition loc_eq l l' :=
  match l, l' with
    | Loc l, Loc l' => Veq l l'
    | Mvt e p, Mvt e' p' => Eeq e e' /\ p = p'
    | _, _ => False
  end.

Axiom e_default : E.

Module Location : DecidableType with Definition t := location with Definition eq := loc_eq.
  Definition t := location.
  Definition eq := loc_eq.
  
  Lemma eq_equiv : Equivalence eq.
  Proof.
  split.
  + intros x. unfold eq, loc_eq. destruct x. reflexivity. split; reflexivity.
  + intros x y Hxy. unfold eq, loc_eq in *. destruct x, y;
    try auto. now symmetry. split; now symmetry.
  + intros x y z Hxy Hyz. destruct x, y, z; unfold eq, loc_eq in *; try auto.
    now transitivity l0. exfalso; auto. exfalso; auto. 
    split. now transitivity e0. now transitivity (p0).
  Qed.
  
  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
  intros l l'.
  destruct l, l'; unfold eq, loc_eq; auto. apply Veq_dec.
  destruct (Eeq_dec e e0), (Rdec (p) (p0));
  intuition.
  Qed.
End Location.



  Module Config := Configurations.Make (Location)(N)(Names).

  Definition project (config : Config.t) : Config.t :=
    fun id =>
      match Config.loc (config id) with
        | Loc l => config id
        | Mvt e p => {| Config.loc := Loc (if Rle_dec (project_p p) (threshold e) 
                                               then src e else tgt e);
                           Config.robot_info := Config.robot_info (config id) |}
      end.
      
  Instance project_compat : Proper (Config.eq ==> Config.eq) project.
  Proof.
  intros c1 c2 Hc id. unfold project. repeat try (split; simpl);
  destruct (Hc id) as (Hloc, (Hsrc, Htgt)); unfold loc_eq in *;
  destruct (Config.loc (c1 id)) eqn : Hloc1, (Config.loc (c2 id)) eqn : Hloc2,
  (Config.source (Config.robot_info (c1 id))) eqn : Hsrc1,
  (Config.source (Config.robot_info (c2 id))) eqn : Hsrc2,
  (Config.target (Config.robot_info (c1 id))) eqn : Htgt1,
  (Config.target (Config.robot_info (c2 id))) eqn : Htgt2; simpl;
  try rewrite Hloc1 in *; try rewrite Hloc2 in *; try rewrite Hsrc1 in *;
  try rewrite Hsrc2 in *; try rewrite Htgt1 in *; try rewrite Htgt2 in *;
  unfold loc_eq in *; try (now exfalso); try assumption;
  destruct Hloc;
  destruct (Rle_dec (project_p p) (threshold e)),(Rle_dec (project_p p0) (threshold e0));
  try (apply (src_compat e e0 H)); (try now rewrite H ,H0 in r); (try now rewrite H, H0 in n);
  try now apply tgt_compat.
  Qed.

  Axiom ri_Loc : forall (rc : Config.RobotConf), exists l1 l2, (
                    Config.source (Config.robot_info rc) = Loc l1 /\
                    Config.target (Config.robot_info rc) = Loc l2)
                    /\ exists e, find_edge l1 l2 = Some e.

  Axiom ax_cont : forall rc e p, Config.loc rc = Mvt e p ->
                               exists l1 l2, (
                    Config.source (Config.robot_info rc) = Loc l1 /\
                    Config.target (Config.robot_info rc) = Loc l2) /\
                    find_edge l1 l2 = Some e.

   Definition projectS_loc (loc : Location.t) : V :=
      match loc with
        | Loc l =>  l
        | Mvt e p => 
          (if Rle_dec (project_p p) (CommonGraphFormalism.threshold e)
             then CommonGraphFormalism.src e 
             else CommonGraphFormalism.tgt e)
      end.

    Instance projectS_loc_compat : Proper (Location.eq ==> Veq) projectS_loc.
    Proof.
    intros x y Hxy. simpl in *. unfold Location.eq, loc_eq in *.
    unfold projectS_loc. destruct x,y.
     - assumption.
     - exfalso; assumption.
     - exfalso; assumption.
     - destruct Hxy as (Hexy, Hpxy), (Rle_dec (project_p p) (threshold e)) eqn : Hx,
       (Rle_dec (project_p p0) (threshold e0)) eqn:Hy.
       + now apply src_compat.
       + assert (Ht := threshold_compat e e0 Hexy).
         assert (Hr : ((project_p p) <= threshold e)%R) by assumption.
         now rewrite Ht, Hpxy in Hr.
       + assert (Hr : ((project_p p0) <= threshold e0)%R) by assumption.
         assert (Ht := threshold_compat e e0 Hexy).
         now rewrite <- Ht, <- Hpxy in Hr.
       + now apply tgt_compat.
    Qed.

    Definition projectS (config : Config.t) : View.t :=
      fun id =>
        {| ConfigA.loc := (projectS_loc (Config.loc (config id)));
           ConfigA.robot_info := 
        {| ConfigA.source := (projectS_loc (Config.source (Config.robot_info (config id))));
           ConfigA.target := (projectS_loc (Config.target (Config.robot_info (config id)))) |} |}.

    Instance projectS_compat : Proper (Config.eq ==> ConfigA.eq) projectS.
    Proof.
    intros c1 c2 Hc id. destruct (Hc id) as (Hl, (Hs, Ht)). unfold projectS.
    split; simpl. now apply projectS_loc_compat. split; simpl; now apply projectS_loc_compat.
    Qed.

  Module Spect : Spectrum(Location)(N)(Names)(Config) with Definition t := View.t 
  with Definition from_config := (fun x => projectS x) with Definition eq := View.eq.

    Definition t := ConfigA.t.
    Definition eq := ConfigA.eq.
    Definition eq_equiv := ConfigA.eq_equiv.
    Definition eq_dec := ConfigA.eq_dec.

   

    Definition from_config := fun x => (projectS x).
    Instance from_config_compat : Proper (Config.eq ==> View.eq) from_config.
    Proof.
    intros x y Hxy. unfold from_config. now apply projectS_compat.
    Defined.
    Definition is_ok : t -> Config.t -> Prop := fun t c => if (eq_dec t (projectS c)) 
                                                then True else False.
    Definition from_config_spec : forall config, is_ok (from_config config) config.
    Proof.
    intro.
    unfold is_ok, from_config. destruct (eq_dec (projectS config) (projectS config)); auto.
    destruct n. reflexivity.
    Defined.

  End Spect.

  Record robogram := {
    pgm :> Spect.t -> Location.t;
    pgm_compat : Proper (Spect.eq ==> Location.eq) pgm;
    pgm_loc : forall spect, exists l, pgm spect = Loc l;
    pgm_range : forall (spect: Spect.t) g sloc,
              Veq (ConfigA.source (ConfigA.robot_info (spect (Good g)))) sloc ->
              exists l e, pgm spect = Loc l /\ find_edge sloc l = Some e }.
  
  Global Existing Instance pgm_compat.
  
    Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  
  Instance req_equiv : Equivalence req.
  Proof. split.
  + intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
  + intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
  + intros r1 r2 r3 H1 H2 x y Heq.
    rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
  Qed.
  
  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  CoInductive execution :=
    NextExecution : Config.t -> execution -> execution.
  
  
  (** *** Destructors for demons *)
  
  Definition execution_head (e : execution) : Config.t :=
    match e with NextExecution conf _ => conf end.
  
  Definition execution_tail (e : execution) : execution :=
    match e with NextExecution _ e => e end.
  
  CoInductive eeq (e1 e2 : execution) : Prop :=
    | Ceeq : Config.eq (execution_head e1) (execution_head e2) ->
             eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.
  
  Instance eeq_equiv : Equivalence eeq.
  Proof. split.
  + coinduction eeq_refl. reflexivity.
  + coinduction eeq_sym. symmetry. now inversion H. now inversion H.
  + coinduction eeq_trans. 
    - inversion H. inversion H0. now transitivity (execution_head y).
    - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
      now inversion H. now inversion H0.
  Qed.
  
  Instance eeq_bisim : Bisimulation execution.
  Proof. exists eeq. apply eeq_equiv. Qed.
  
  Instance execution_head_compat : Proper (eeq ==> Config.eq) execution_head.
  Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.
  
  Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
  Proof. intros e1 e2 He. now inversion He. Qed.

  (** ** Demonic schedulers *)

  (** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
  Inductive Active_or_Moving := 
    | Moving (dist :R)                   (* moving ratio *)
    | Active (sim : unit). (* change of referential *)

  Definition Aom_eq (a1 a2: Active_or_Moving) :=
    match a1, a2 with
      | Moving d1, Moving d2 => d1 = d2
      | Active sim1, Active sim2 => (Logic.eq)%signature sim1 sim2
      | _, _ => False
    end.


  Instance Active_compat : Proper (Logic.eq ==> Aom_eq) Active.
  Proof. intros ? ? ?. auto. Qed.

  Instance Aom_eq_reflexive : Reflexive Aom_eq.
  Proof. intros x. unfold Aom_eq. now destruct x. Qed.

  (* as Active give a function, Aom_eq is not reflexive. It's still symmetric and transitive.*)
  Instance Aom_eq_Symmetric : Symmetric Aom_eq.
  Proof.
  intros x y H. unfold Aom_eq in *. destruct x, y; auto.
  Qed.

  Instance Aom_eq_Transitive : Transitive Aom_eq.
  Proof.
  intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
  Qed.


  Record demonic_action := {
    relocate_byz : Names.B -> Location.t;
    step : Names.ident -> Config.RobotConf -> Active_or_Moving;
    step_delta : forall g Rconfig sim, (step (Good g) Rconfig) = (Active sim) ->
         ((exists l, Location.eq Rconfig.(Config.loc) (Loc l)) /\
         Location.eq Rconfig.(Config.loc) Rconfig.(Config.robot_info).(Config.target));
    step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step;
    step_flexibility : forall id config r,(step id config) = (Moving r) -> (0 <= r <= 1)%R}.
  Set Implicit Arguments.

(*   Axiom a : forall (e : E) (p : R) (c : Config.t) (da : demonic_action) (id : Names.ident),
          Config.loc (c id) = Mvt e p ->
          let l := if Rle_dec (project_p p) (threshold e)
            then (src e)
            else (tgt e)
          in step da id (c id) = step da id
                    {| Config.loc := Loc l; Config.robot_info :=
                      {| Config.source := Config.source (Config.robot_info (c id));
                         Config.target := Config.target (Config.robot_info (c id)) |} |} . *)

  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
    (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

  Instance da_eq_equiv : Equivalence da_eq.
  Proof. split.
  + split; intuition. (* now apply step_compat. *)
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

  (** A [demon] is just a stream of [demonic_action]s. *)
  CoInductive demon :=
    NextDemon : demonic_action -> demon -> demon.

  (** Destructors for demons, getting the head demonic action or the
      tail of the demon. *)

  Definition demon_head (d : demon) : demonic_action :=
    match d with NextDemon da _ => da end.

  Definition demon_tail (d : demon) : demon :=
    match d with NextDemon _ d => d end.

  CoInductive deq (d1 d2 : demon) : Prop :=
    | Cdeq : da_eq (demon_head d1) (demon_head d2) ->
             deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

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

  Instance demon_head_compat : Proper (deq ==> da_eq) demon_head.
  Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

  Instance demon_tail_compat : Proper (deq ==> deq) demon_tail.
  Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.
  
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

Inductive LocallyFairForOne id (d : demon) : Prop :=
  | ImmediatelyFair : forall config, is_Active (step (demon_head d) id (config id)) = true -> 
                                      LocallyFairForOne id d
  | LaterFair : forall config, is_Active (step (demon_head d) id (config id)) = false ->
                                 LocallyFairForOne id (demon_tail d) -> LocallyFairForOne id d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (forall g, LocallyFairForOne g d) -> Fair (demon_tail d) ->
               Fair d.

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k conf, is_Active (step (demon_head d) g (conf g)) = true -> Between g h d k
| kReduce : forall k conf, is_Active (step (demon_head d) g (conf g)) = false ->
                            is_Active (step (demon_head d) h (conf g)) = true ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k conf, is_Active (step (demon_head d) g (conf g)) = false ->
                           is_Active (step (demon_head d) h (conf g)) = false ->
                     Between g h (demon_tail d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) : Prop :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> 
                                     LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
intros g d1 d2 Hd Hfair. revert d2 Hd. induction Hfair; intros d2 Hd.
 + assert (Heq : is_Active (step (demon_head d2) g (config g)) = true) by now rewrite <- Hd, H.
   destruct (step (demon_head d2) g) eqn:?; simpl in Heq.
   - easy.
   - constructor 1 with config.
     unfold is_Active.
     rewrite Heqa; auto.
 + assert (Heq : is_Active (step (demon_head d2) g (config g)) = false) by now rewrite <- Hd, H.
   destruct (step (demon_head d2) g) eqn:?; simpl in Heq.
   - constructor 2 with config.
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
+ assert (Heqa : is_Active (step (demon_head d2) g (conf g)) = true) by now rewrite <- Heq, H.
  destruct (step (demon_head d2) g (conf g)) eqn:?; simpl in Heqa.
   - easy.
   - constructor 1 with conf. unfold is_Active. rewrite Heqa0; auto.
+ assert (Heqa : is_Active (step (demon_head d2) h (conf g)) = true) by now rewrite <- Heq, H0.
  destruct (step (demon_head d2) h (conf g)) eqn:?; simpl in Heq.
  - easy.
  - constructor 2 with conf.
    * unfold is_Active in *. destruct (step (demon_head d2) g (conf g)) eqn:?,
      (step (demon_head d) g (conf g)) eqn:?; intuition.
      rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *. 
      rewrite Heqa1 in Heqa2. discriminate.
      symmetry.
      apply Heq.
    * rewrite Heqa0; assumption.
    * apply IHbet; now f_equiv.
+ constructor 3 with conf.
  - unfold is_Active in *.
    destruct (step (demon_head d2) g (conf g)) eqn:?, (step (demon_head d) g (conf g)) eqn:?; intuition.
    rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *.
    rewrite Heqa in Heqa0; discriminate.
    symmetry; apply Heq.
  - unfold is_Active in *.
    destruct (step (demon_head d2) h (conf g)) eqn:?, (step (demon_head d) h (conf g)) eqn:?; intuition.
    rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *.
    rewrite Heqa in Heqa0; discriminate. symmetry; apply Heq.
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
  now constructor 1 with conf.
  constructor 2 with conf. apply H. apply IHHg.
  constructor 2 with conf. apply H. apply IHHg.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof.
  intros g d k Hd. induction Hd.
  now constructor 1 with config.
  now constructor 3 with config.
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
  now constructor 1 with conf.
  destruct k'.
    now inversion Hk.
    constructor 2 with conf; assumption || now (apply IHHd; omega).
  constructor 3 with conf; assumption || now (apply IHHd; omega).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
  coinduction fair; destruct H.
  - intros. now apply Between_mon with k.
  - now apply (fair k).
Qed.

(* difficult to prove now tha step take a Rconf *)
(* Theorem Fair0 : forall d, kFair 0 d ->
  forall g h, (forall rconf, is_Active ((demon_head d).(step) g rconf) = false)
             <-> (forall rconf, is_Active ((demon_head d).(step) h rconf) = false).
Proof.

Qed.  *)

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2: forall conf,
    is_Active (step (demon_head d) g (conf g)) = true -> 
                      FullySynchronousForOne g d.

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    (forall g, FullySynchronousForOne g d)
    -> FullySynchronous (demon_tail d)
    -> FullySynchronous d.


(** A locally synchronous demon is fair *)
Lemma local_fully_synchronous_implies_fair:
  forall g d, FullySynchronousForOne g d -> LocallyFairForOne g d.
Proof. induction 1. now (constructor 1 with conf). Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: forall d, FullySynchronous d -> Fair d.
Proof.
  coinduction fully_fair.
  - intro. apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
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
          match pos, id with
            | Mvt e p, Good g => if Rle_dec 1%R ((project_p p) + mv_ratio)
                then {| Config.loc := Loc (tgt e); Config.robot_info := Config.robot_info conf |}
                else {| Config.loc := if Rdec mv_ratio 0 
                                      then Mvt e p
                                      else Mvt e (p + (project_p_inv mv_ratio));
                        Config.robot_info := Config.robot_info conf |}
            | Loc l, Good g =>
                if Rdec mv_ratio 0%R then conf else
                if Rdec mv_ratio 1%R then {| Config.loc := Config.target (Config.robot_info conf);
                                             Config.robot_info := Config.robot_info conf |} else
                let new_pos := match Config.target (Config.robot_info conf) with
                                 | Loc l => l
                                 | Mvt e _ => src e
                               end in
                if Veq_dec l new_pos then conf
                else 
                let e := match find_edge l new_pos with
                           | Some e => e
                           | None => e_default (* ici *)
                         end in
                         {| Config.loc := Mvt e (project_p_inv mv_ratio);
                            Config.robot_info := Config.robot_info conf |}
           | _, Byz b => conf
          end
        | Active sim => 
        (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
          match id with 
          | Byz b => {| Config.loc := da.(relocate_byz) b ; 
                        Config.robot_info := Config.robot_info conf |}
          | Good g =>
            let local_conf := project config in
            let target := r (Spect.from_config local_conf)
            in
             {| Config.loc := pos ; 
                Config.robot_info := {| Config.source := pos ; Config.target := target|} |}
        end
      end.
 
Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
assert (Haxiom := ri_Loc).
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
  destruct (Config.loc (conf1 (Good g))) eqn: Hloc1, (Config.loc (conf2 (Good g))) eqn : Hloc2.
  * destruct (Rdec dist 0), (Rdec dist0 0).
    - apply Hrconf.
    - now rewrite Hstep in e.
    - now rewrite Hstep in n.
    - destruct (Rdec dist 1), (Rdec dist0 1).
      -- f_equiv; apply Hrconf.
      -- now rewrite Hstep in e.
      -- now rewrite Hstep in n1.
      -- destruct (Config.target (Config.robot_info (conf1 (Good g)))) eqn : Htgt1,
         (Config.target (Config.robot_info (conf2 (Good g)))) eqn : Htgt2,
         (Config.source (Config.robot_info (conf1 (Good g)))) eqn : Hsrc1,
         (Config.source (Config.robot_info (conf2 (Good g)))) eqn : Hsrc2;
         destruct Hrconf as (Hloc, (Hsrc, Htgt)); rewrite Htgt1, Htgt2 in Htgt;
         rewrite Hloc1, Hloc2 in Hloc; rewrite Hsrc1, Hsrc2 in Hsrc; unfold loc_eq in *;
         try (now exfalso).
         ++ destruct (Veq_dec l l1), (Veq_dec l0 l2).
            ** apply Hconf.
            ** now rewrite Hloc, Htgt in v.
            ** now rewrite Hloc, Htgt in n3.
            ** repeat try (split; simpl); try apply Hconf.
               assert (Hcp := CommonGraphFormalism.find_edge_compat l l0 Hloc l1 l2 Htgt).
               now destruct (find_edge l l1), (find_edge l0 l2).
               now rewrite Hstep.
         ++ destruct (Veq_dec l l1), (Veq_dec l0 l2).
            ** apply Hconf.
            ** now rewrite Hloc, Htgt in v.
            ** now rewrite Hloc, Htgt in n3.
            ** repeat try (split; simpl); try apply Hconf.
               assert (Hcp := CommonGraphFormalism.find_edge_compat l l0 Hloc l1 l2 Htgt).
               now destruct (find_edge l l1), (find_edge l0 l2).
               now rewrite Hstep.
         ++ specialize (Haxiom (conf1 (Good g))).
            destruct Haxiom as (la1, (la2, ((Haxiom1, Haxiom2), (eD, Hed)))).
            rewrite Haxiom2 in Htgt1. discriminate.
         ++ specialize (Haxiom (conf1 (Good g))).
            destruct Haxiom as (la1, (la2, ((Haxiom1, Haxiom2), (eD, Hed)))).
            rewrite Haxiom2 in Htgt1. discriminate.
 * destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in *; now exfalso.
 * destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in *; now exfalso.
 * rewrite Hstep. 
   destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in Hloc. destruct Hloc as (He, Hp).
   rewrite Hp.
   destruct (Rle_dec 1 (project_p p0 + dist0)); 
   repeat try (split;simpl); try apply Hconf.
   - now apply CommonGraphFormalism.tgt_compat.
   - destruct (Rdec dist0 0); unfold loc_eq; now split.
+ destruct (Config.loc (conf1 (Byz b))) eqn : HconfB1,
  (Config.loc (conf2 (Byz b))) eqn : HconfB2;
  try apply Hconf.
+ try repeat (split; simpl); try apply Hrconf. apply Hr. f_equiv. apply project_compat, Hconf.
+ try repeat (split; simpl); try apply Hrconf. now rewrite Hda.
  Qed.
  
  Definition execute (r : robogram): demon -> Config.t -> execution :=
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

Definition Conf_init (conf: Config.t) : Prop := forall id, exists l, conf id = 
{| Config.loc := Loc l;
Config.robot_info := {| Config.source := Loc l; Config.target := Loc l|} |}.

Lemma round_flow : forall rbg da g conf e p,
         loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) -> 
         (exists l, loc_eq (Config.loc (conf (Good g))) (Loc l)) \/
         (exists p', (project_p p' <= project_p p)%R /\
                     loc_eq (Config.loc (conf (Good g))) (Mvt e p')).
Proof.
intros rbg da g conf e p Hl.
unfold round in *.
destruct (step da (Good g) (conf (Good g))) eqn : Hstep. simpl in *.
destruct (Config.loc (conf (Good g))). left; now exists l.
destruct (Rle_dec 1 (project_p p0 + dist)); simpl in *; try now exfalso.
destruct (Rdec dist 0). right. exists p0. unfold loc_eq in Hl; destruct Hl.
repeat split. now rewrite H0. auto. right. exists p0.
unfold loc_eq in *. destruct Hl.
repeat split. rewrite <- H0, proj_comm, <- inv_pro;
assert (Hdist := step_flexibility da (Good g) (conf (Good g)) dist Hstep).
lra. assert (Hp := project_p_image p0). lra. auto.
simpl in *. right. exists p. now split.
Qed.

Definition is_not_loc loc := forall l, ~Location.eq (Loc l) loc.

CoInductive HasNeverBeenLoc (e : execution) g : Prop :=
  isLoc : is_not_loc (Config.loc ((execution_head e) (Good g))) -> 
            HasNeverBeenLoc (execution_tail e) g ->
            HasNeverBeenLoc e g.

Inductive WillNeverBeNode  rbg d conf g: Prop :=
  | Now : HasNeverBeenLoc (execute rbg d conf) g->
          WillNeverBeNode rbg d conf g
  | Later : WillNeverBeNode rbg (demon_tail d) (round rbg (demon_head d) conf) g -> 
          WillNeverBeNode rbg d conf g.




Lemma ri_loc' : forall (conf : Config.t) g v0 rbg da,
   loc_eq (Config.loc ((round rbg da conf) (Good g))) (Loc v0) -> 
   loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0) \/
   loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0).
Proof.
intros conf g v0 rbg da Hl.
unfold round in *.
destruct (step da (Good g) (conf (Good g))) eqn : Hstep.
Focus 2.
simpl in *. now left.
simpl in *.
destruct (Config.loc (conf (Good g))) as [l| e p ] eqn : Hloc.
Focus 2.
destruct (Rle_dec 1 (project_p p + dist)).
simpl in *.
Qed.

Lemma ri_loc_round : forall conf v0 v1 v2 da rbg g,
      loc_eq (Config.loc (conf (Good g))) (Loc v0) ->
      loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
      loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
exists v1' v2',
      loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1')
   /\ loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2').
Proof.
intros conf v0 v1 v2 da rbg g Hl Hs Ht.
unfold round. simpl in *.
destruct (step da (Good g) (conf (Good g))), (Config.loc (conf (Good g))) eqn : Hloc.
destruct (Rdec dist 0). exists v1, v2. split;assumption.
destruct (Rdec dist 1). simpl. exists v1, v2. split; assumption.
destruct (Veq_dec l
              match Config.target (Config.robot_info (conf (Good g))) with
              | Loc l0 => l0
              | Mvt e _ => src e
              end);
exists v1, v2; split;assumption.
destruct (Rle_dec 1 (project_p p + dist)); 
exists v1, v2; split;assumption.
simpl in *. exists l.
assert (Hrbg := pgm_loc rbg (Spect.from_config (project conf))).
destruct Hrbg as (lspect, Hrbg).
assert
(Hsp : Veq (ConfigA.source (ConfigA.robot_info (Spect.from_config (project conf) (Good g)))) v1).
unfold Spect.from_config, projectS, projectS_loc, project. simpl in *.
rewrite Hloc.
destruct (Config.source (Config.robot_info (conf (Good g)))) eqn : Hs'; try now exfalso.
now unfold loc_eq in Hs.
assert (Hrange := pgm_range rbg (Spect.from_config (project conf)) g v1 Hsp).
destruct Hrange as (spl, (e, (Hlocs,Hrange))). exists spl. split. reflexivity.
rewrite Hlocs. reflexivity.
simpl in *. now exfalso.
Qed.

Lemma ri_loc_eq1 : forall conf v0 v1 v2 v1' v2' da rbg g,
   loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1') ->
   loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2') ->
   (loc_eq (Config.loc (conf (Good g))) (Config.source (Config.robot_info (conf (Good g)))) \/
    loc_eq (Config.loc (conf (Good g))) (Config.target (Config.robot_info (conf (Good g))))) ->
   loc_eq (Config.loc ((round da rbg conf) (Good g))) (Loc v0) ->
   loc_eq (Config.source (Config.robot_info ((round da rbg conf) (Good g)))) (Loc v1) ->
   loc_eq (Config.target (Config.robot_info ((round da rbg conf) (Good g)))) (Loc v2) ->
   Veq v0 v1 \/ Veq v0 v2.
Proof.
intros conf v0 v1 v2 v1' v2' da rbg g Hs' Ht' Hbefore Hl Hs Ht.
unfold round in *.
destruct (step rbg (Good g) (conf (Good g))) eqn : Hstep, (Config.loc (conf (Good g))) eqn : Hloc,
Hbefore as [Hbs | Hbt].
destruct (Rdec dist 0). rewrite Hloc in Hl.
rewrite Hs in Hbs. unfold loc_eq in *. left. now rewrite Hl in Hbs.
destruct (Rdec dist 1). simpl in *. unfold loc_eq in *.
destruct (Config.target (Config.robot_info (conf (Good g)))); try now exfalso.
rewrite Hl in Ht. now right.
destruct (Veq_dec l
                 match Config.target (Config.robot_info (conf (Good g))) with
                 | Loc l => l
                 | Mvt e _ => src e
                 end). rewrite Hloc in Hl.
rewrite Hs in Hbs. unfold loc_eq in *. left. now rewrite Hl in Hbs.
simpl in *. now exfalso.
destruct (Rdec dist 0). rewrite Hloc in Hl.
rewrite Ht in Hbt. unfold loc_eq in *. right. now rewrite Hl in Hbt.
destruct (Rdec dist 1). simpl in *. unfold loc_eq in *.
destruct (Config.target (Config.robot_info (conf (Good g)))); try now exfalso.
rewrite Hl in Ht. now right.
destruct (Veq_dec l
                 match Config.target (Config.robot_info (conf (Good g))) with
                 | Loc l => l
                 | Mvt e _ => src e
                 end). rewrite Hloc in Hl.
rewrite Ht in Hbt. unfold loc_eq in *. right. now rewrite Hl in Hbt.
simpl in *. now exfalso.
destruct (Config.source (Config.robot_info (conf (Good g)))); now unfold loc_eq.
destruct (Config.target (Config.robot_info (conf (Good g)))); now unfold loc_eq.
simpl in *. rewrite Hl in Hs. now left.
simpl in *.
unfold loc_eq in *; try now exfalso.
rewrite <- Hs. now left.
simpl in *. now exfalso.
simpl in *. now exfalso.
Qed.



Axiom ri_loc_eq' : forall (rc : Config.RobotConf) v0 v1 v2,
                   loc_eq (Config.loc rc) (Loc v0) ->
                   loc_eq (Config.source (Config.robot_info rc)) (Loc v1) ->
                   loc_eq (Config.target (Config.robot_info rc)) (Loc v2) ->
                   (v0 = v1) \/ (v0 = v2).

(*  Axiom ax_cont : forall rc e p, Config.loc rc = Mvt e p ->
                               exists l1 l2, (
                    Config.source (Config.robot_info rc) = Loc l1 /\
                    Config.target (Config.robot_info rc) = Loc l2) /\
                    find_edge l1 l2 = Some e.*)

Lemma ax_cont_loc1 : forall conf v0 v1 v2 da (rbg : robogram) g e p,
       loc_eq (Config.target (Config.robot_info (conf (Good g))))
              (rbg (Spect.from_config (project conf))) ->
       loc_eq (Config.loc (conf (Good g))) (Loc v0) ->
       loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1) ->
       loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2) ->
       loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) ->
       opt_eq Eeq (find_edge v1 v2) (Some e).
Proof.
intros conf v0 v1 v2 da rbg g e p Htr Hl0 Hs Ht Hl.
assert (Hrbg := pgm_range rbg (Spect.from_config (project conf)) g
((ConfigA.source (ConfigA.robot_info (Spect.from_config (project conf) (Good g)))))
(reflexivity (ConfigA.source (ConfigA.robot_info (Spect.from_config (project conf) (Good g)))))).
destruct Hrbg as (l', (e',(Hsp, Hedge))).
assert (Hss := Hs).
destruct (Config.source (Config.robot_info (round rbg da conf (Good g)))) as [ls'| ms'] eqn : Hs';
unfold loc_eq in Hs; try now exfalso. rewrite <- Hs' in Hss;
unfold round in *; simpl in *.
destruct (step da (Good g) (conf (Good g)))as [dist|sim] eqn : Hstep,
(Config.loc (conf (Good g))) as [ll'|edge pl'] eqn : Hloc; try discriminate.
+ destruct (Rdec dist 0). rewrite Hloc in Hl; now unfold loc_eq.
  destruct (Rdec dist 1).
  simpl in *. rewrite Ht in Hl; now unfold loc_eq.
  simpl in *.
  destruct (Config.target (Config.robot_info (conf (Good g))))as [lt'| mt'] eqn : Ht'.
  destruct (Veq_dec ll' lt'). rewrite Hloc in Hl. now unfold loc_eq in Hl.
  simpl in *.
  assert (Veq ll' (ConfigA.loc (Spect.from_config (project conf) (Good g)))).
  simpl in *. unfold projectS_loc, project in *.
  now do 2 rewrite Hloc in *. unfold projectS_loc, project in Hedge.
  rewrite Hloc in Hedge. simpl in *.
  assert (Hloc' : loc_eq (Config.loc (conf (Good g))) (Loc ll')) by now rewrite Hloc.
  rewrite Hsp in Htr.
  assert (Hax := ri_loc_eq' (conf (Good g)) ll' v1 v2 Hloc' Hss Ht).
  destruct Hax as [Hleft| Hright].
  rewrite <- find_edge_Some;
  apply find_edge_compat; rewrite Ht' in Ht.
  destruct (find_edge ll' lt') eqn : Hedge'; destruct Hl as (He, Hp).
  rewrite Hs' in Hedge.
  assert (Haide : Veq (src e) (src e0)) by now apply src_compat.
  rewrite Haide.
  assert (Hedge'' : opt_eq Eeq (find_edge ll' lt') (Some e0)) by now rewrite Hedge'.
  apply find2st in Hedge''. destruct Hedge''. now rewrite Hleft in H0.
  destruct (Config.source (Config.robot_info (conf (Good g)))); try discriminate.
  assert (Hfalse : opt_eq Eeq (find_edge l l') (find_edge ll' lt')). apply find_edge_compat.
  unfold loc_eq in Hss. rewrite Hss. now rewrite Hleft. now symmetry.
  now rewrite Hedge', Hedge in Hfalse.
  destruct (find_edge ll' lt') eqn : Hedge'; destruct Hl as (He, Hp).
  rewrite Hs' in Hedge.
  assert (Haide : Veq (tgt e) (tgt e0)) by now apply tgt_compat.
  rewrite Haide.
  assert (Hedge'' : opt_eq Eeq (find_edge ll' lt') (Some e0)) by now rewrite Hedge'.
  apply find2st in Hedge''. destruct Hedge''. unfold loc_eq in Ht. now rewrite Ht in H1.
  destruct (Config.source (Config.robot_info (conf (Good g)))); try discriminate.
  assert (Hfalse : opt_eq Eeq (find_edge l l') (find_edge ll' lt')). apply find_edge_compat.
  unfold loc_eq in Hss. rewrite Hss. now rewrite Hleft. now symmetry.
  now rewrite Hedge', Hedge in Hfalse.
  rewrite Ht' in Ht. rewrite <- Hright in Ht. unfold loc_eq in Ht. now symmetry in Ht.
  rewrite Hsp in Htr. now unfold loc_eq in Htr.
+ now unfold loc_eq in Hl0.
+ now simpl in *.
Qed.


Lemma ax_cont_loc2 : forall conf e0 p0 v1 v2 da (rbg : robogram) g e p,
       loc_eq (Config.target (Config.robot_info (conf (Good g))))
              (rbg (Spect.from_config (project conf))) ->
       loc_eq (Config.loc (conf (Good g))) (Mvt e0 p0) ->
       loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc (src e0)) ->
       loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc (tgt e0)) ->
       loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1) ->
       loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2) ->
       loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) ->
       opt_eq Eeq (find_edge v1 v2) (Some e).
Proof.
intros conf e0 p0 v1 v2 da rbg g e p Htr Hl0 Hs0 Ht0 Hs Ht Hl.
(* assert (Hrbg := pgm_range rbg (Spect.from_config (project conf)) g
((ConfigA.source (ConfigA.robot_info (Spect.from_config (project conf) (Good g)))))
(reflexivity (ConfigA.source (ConfigA.robot_info (Spect.from_config (project conf) (Good g)))))).
destruct Hrbg as (l', (e',(Hsp, Hedge'))).
assert (Hss := Hs).
destruct (Config.source (Config.robot_info (round rbg da conf (Good g)))) as [ls'| ms'] eqn : Hs';
unfold loc_eq in Hs;try now exfalso. *)
unfold round in *.

destruct (step da (Good g) (conf (Good g)))as [dist|sim] eqn : Hstep,
(Config.loc (conf (Good g))) as [ll'|edge pl'] eqn : Hloc; try discriminate.
+ now unfold loc_eq in Hl0.
+ destruct (Rle_dec 1 (project_p pl' + dist)). now simpl in *.
  simpl in *. destruct (Rdec dist 0).
  - unfold loc_eq in Hl.
    destruct Hl as (He, Hp), Hl0 as (He0, Hp0).
    assert (Hedge : opt_eq Eeq (Some e0) (Some e)).
    { assert (Hedge'' : opt_eq Eeq (Some edge) (Some e)) by apply He.
    rewrite <- Hedge''. symmetry; apply He0. }
    rewrite <- Hedge.
    rewrite <- find_edge_Some. apply find_edge_compat.
    * rewrite Hs in Hs0. now unfold loc_eq in Hs0.
    * rewrite Ht in Ht0; now unfold loc_eq in Ht0.
  - unfold loc_eq in Hl.
    destruct Hl as (He, Hp), Hl0 as (He0, Hp0).
    assert (Hedge : opt_eq Eeq (Some e0) (Some e)).
    { assert (Hedge'' : opt_eq Eeq (Some edge) (Some e)) by apply He.
    rewrite <- Hedge''. symmetry; apply He0. }
    rewrite <- Hedge.
    rewrite <- find_edge_Some. apply find_edge_compat.
    * rewrite Hs in Hs0. now unfold loc_eq in Hs0.
    * rewrite Ht in Ht0; now unfold loc_eq in Ht0.
+ now simpl in *.
+ now simpl in *.
Qed.


Lemma round_flow : forall rbg da g conf e p,
         loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) -> 
         (exists l, loc_eq (Config.loc (conf (Good g))) (Loc l)) \/
         (exists p', (project_p p' <= project_p p)%R /\
                     loc_eq (Config.loc (conf (Good g))) (Mvt e p')).
Proof.
intros rbg da g conf e p Hl.
unfold round in *.
destruct (step da (Good g) (conf (Good g))) eqn : Hstep. simpl in *.
destruct (Config.loc (conf (Good g))). left; now exists l.
destruct (Rle_dec 1 (project_p p0 + dist)); simpl in *; try now exfalso.
destruct (Rdec dist 0). right. exists p0. unfold loc_eq in Hl; destruct Hl.
repeat split. now rewrite H0. auto. right. exists p0.
unfold loc_eq in *. destruct Hl.
repeat split. rewrite <- H0, proj_comm, <- inv_pro;
assert (Hdist := step_flexibility da (Good g) (conf (Good g)) dist Hstep).
lra. assert (Hp := project_p_image p0). lra. auto.
simpl in *. right. exists p. now split.
Qed.

Lemma ri_loc_eq2 : forall conf v0 v1 v2 e0 p0 v1' v2' da rbg g,
   loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1') ->
   loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2') ->
   loc_eq (Config.loc (conf (Good g))) (Mvt e0 p0) ->
   loc_eq (Config.loc ((round rbg da conf) (Good g))) (Loc v0) ->
   loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1) ->
   loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2) ->
   Veq v0 v1 \/ Veq v0 v2.
Proof.
intros conf v0 v1 v2 e0 p0 v1' v2' da rbg g Hs' Ht' Hl' Hl Hs Ht.
unfold round in *; simpl in *.
destruct (step da (Good g) (conf (Good g))) as [dist|sim] eqn : Hstep,
(Config.loc (conf (Good g))) as [ l | e' p'] eqn : Hl0; try (now unfold loc_eq in Hl').
destruct (Rle_dec 1 (project_p p' + dist)); simpl in *.
+ right. unfold loc_eq in *.
  destruct (Config.target (Config.robot_info (conf (Good g))));
  try discriminate; try (now exfalso).
  assert (opt_eq Eeq (find_edge v1 v2) (Some e')).
  admit.
  apply find2st in H. destruct H.
  rewrite <- Hl. now symmetry.
+ destruct (Rdec dist 0); now unfold loc_eq in *.
Qed.
  (* Lemma compat_helper1 : Aom_eq (da.(step) id conf) (Moving mv_r) ->  *)

  (** [execute r d conf] returns an (infinite) execution from an initial global
      configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)


End DGF.


