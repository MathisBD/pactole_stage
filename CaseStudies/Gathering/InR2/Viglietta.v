(** Formalization of the algorithm to solve rendezvous in R² with 1 bit
    from "Rendezvous of two robots with visible bits", G. Viglietta, ALGOSENSORS 2013

    2 full lights: A and B

    Robogram:
    - me=A, you=A: move to middle location, light goes to B
    - me=A, you=B: move to the other location
    - me=B, you=A: stay
    - me=B, you=B: stay, light goes to A *)

Require Import Lia.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.R.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Models.Similarity.
Require Import Pactole.CaseStudies.Gathering.Definitions.

(* Helping typeclass resolution avoid infinite loops. *)
Typeclasses eauto := (bfs).

(* Avoid problems with previous instances. *)
Remove Hints eq_setoid : typeclass_instances.

Local Existing Instance R2.R2_VS.
Local Existing Instance R2.R2_ES.

Section RDV.

(** There are only 2 robots: r0 and r1. *)
Instance N : Names := Robots 2 0.

Notation lt2 := (fun x => x < 2)%nat.
Definition lt02 : (0 < 2)%nat := ltac:(abstract lia).
Definition lt12 : (1 < 2)%nat := ltac:(abstract lia).
Definition r0 : G := exist lt2 0%nat lt02.
Definition r1 : G := exist lt2 1%nat lt12.

Lemma id_case : forall id, id = Good r0 \/ id = Good r1.
Proof using .
intros [[[| [| ?]] ?] | []]; simpl;
solve [ exfalso; lia
      | now left + right; f_equal; apply eq_proj1 ].
Qed.

(** The space is R², so that we can define similarities and they respect middle points. *)
Instance Loc : Location := make_Location R2.

(** State: location + light *)
Inductive light := A | B.

Instance light_Setoid : Setoid light := eq_setoid light.

Instance light_EqDec : EqDec light_Setoid.
refine (fun x y => match x, y with A, A | B, B => left _ | A, B | B, A => right _ end).
Proof. all:abstract (auto; discriminate). Defined.

Definition info := (location * light)%type.

Instance St : State info := AddInfo light
   (OnlyLocation (fun f => sigT (fun sim : similarity location => Bijection.section sim == f))).

(** Since there are none, we can ignore Byzantine robots. *)
Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, config1 (Good g) == config2 (Good g)) -> config1 == config2.
Proof using .
intros config1 config2 Heq id. destruct id as [g | b].
+ apply Heq.
+ destruct b. exfalso. lia.
Qed.

(** The robot have access to the full state of all robots, that is, their locations and lights. *)
Instance Obs : @Observation info Loc St N.
simple refine {| observation := info * info;   (* self & other robot's state *)
                 observation_Setoid := prod_Setoid state_Setoid state_Setoid;
                 obs_from_config config st :=
                   let st0 := config (Good r0) in
                   let st1 := config (Good r1) in
                   if st0 =?= st then (st0, st1) else (st1, st0);
                 obs_is_ok obs config st :=
                   let st0 := config (Good r0) in
                   let st1 := config (Good r1) in
                   obs == if st0 =?= st then (st0, st1) else ( st1, st0) |}; autoclass; [|].
Proof.
+ Time abstract (intros ? ? Hconfig ? ? Hpt; cbn zeta;
                 repeat destruct_match;
                 solve [ split; apply Hconfig
                       | rewrite Hconfig, Hpt in *; now exfalso ]).
+ intros. cbn -[equiv]. reflexivity.
Defined.

(** Robot choices *)
(* TODO: use [light * ratio] to get exactly the algorithms from the class L *)
Instance RC2 : robot_choice info := {|
  robot_choice_Setoid := prod_Setoid location_Setoid light_Setoid |}.

(** Demon choices:
    - the frame change is a similarity
    - no choice for update for both active and inactive robots. *)
Instance FC2 : frame_choice (similarity location) := FrameChoiceSimilarity.
Instance UC2 : update_choice unit := {| update_choice_EqDec := unit_EqDec |}.
Instance IC2 : inactive_choice unit := {| inactive_choice_EqDec := unit_EqDec |}.

(** Update functions: the robot gets to its target, and nothing happne ot inactive robots. *)
Instance UF : update_function _ _ _.
refine {| update := fun _ _ _ pt _ => pt;
          update_compat := _ |}.
Proof. now repeat intro. Defined.
Instance IF2 : inactive_function _.
refine {| inactive := fun config id _ => config id;
          inactive_compat := _ |}.
Proof. now repeat intro; subst. Defined.

(** In this setting, only SSYNC demons can be defined (the inactive choice is ignored). *)
Lemma SSYNC_setting : forall da, SSYNC_da da.
Proof using . repeat intro. reflexivity. Qed.

(** The robogram in both the local and global frames of reference. *)
Definition rendezvous_pgm : observation -> info :=
  fun '((pt1, l1), (pt2, l2)) =>
    match l1, l2 with
      | A, A => (middle pt1 pt2, B)
      | B, A => (pt1, l1)
      | A, B => (pt2, l1)
      | B, B => (pt1, A)
    end.

Instance rdv_compat : Proper (equiv ==> equiv) rendezvous_pgm.
Proof using .
intros [[] []] [[] []] [[] []]. simpl in *.
repeat destruct_match; simpl; repeat split; congruence.
Qed.

Definition rendezvous : robogram := {| pgm := rendezvous_pgm |}.

Notation "!! config § st " := (obs_from_config (Observation := Obs) config st) (at level 60).

(** Express the algorithm in the global frame of reference. *)
Definition map_spect f : observation -> observation :=
  fun s => (f (fst s), f (snd s)).

Lemma obs_from_config_map : forall (f : sigT precondition),
  Proper ((equiv ==> equiv)%signature) (projT1 f) ->
  forall config st,
    !! map_config (lift f) config § lift f st == map_spect (lift f) (!! config § st).
Proof using .
intros f Hf config st.
unfold obs_from_config. cbn -[equiv_dec equiv].
repeat destruct_match.
+ now repeat split.
+ exfalso. cut (config (Good r0) == st); auto; [].
  match goal with H : _ == _ |- _ => revert H end.
  intros [Hfst Hsnd]. destruct f as [f [sim Hsim]].
  cbn -[equiv] in *. rewrite <- Hsim in *.
  apply Similarity.injective in Hfst. now split.
+ exfalso. cut (lift f (config (Good r0)) == lift f st); auto; [].
  now apply (lift_compat Hf).
+ now repeat split.
Qed.

Lemma rendezvous_pgm_map : forall f s,
  rendezvous_pgm (map_spect (lift (State := St) f) s) == lift f (rendezvous_pgm s).
Proof using .
intros [f Pf] [[pt1 l1] [pt2 l2]].
unfold rendezvous_pgm. cbn -[equiv middle].
destruct l1, l2; cbn -[equiv middle] in *; repeat split; auto; [].
cbn [fst]. destruct Pf as [sim Hsim]. rewrite <- Hsim. apply R2_middle_morph.
Qed.

Lemma round_simplify : forall da config,
  similarity_da_prop da -> (* the frame of the observing robot is centered on itself *)
  round rendezvous da config
  == fun id => if activate da id
               then rendezvous (!! config § config id)
               else config id.
Proof using .
intros da config Hda. apply no_byz_eq. intro g. unfold round.
cbn -[location_Setoid location inverse equiv get_location lift frame_choice_bijection].
destruct_match; try reflexivity; [].
change (rendezvous_pgm (!! config § config (Good g)))
  with (Datatypes.id (rendezvous_pgm (!! config § config (Good g)))).
pose (f_state := existT (fun f => {sim : similarity location & Bijection.section sim == f})
                        (frame_choice_bijection (change_frame da config g))
                        (precondition_satisfied da config g)).
pose (f_state_inv := existT (fun f => {sim : similarity location & Bijection.section sim == f})
                            (frame_choice_bijection (change_frame da config g) ⁻¹)
                            (precondition_satisfied_inv da config g)).
change (@equiv info _
        (lift f_state_inv (rendezvous_pgm
           (!! map_config (lift f_state) config § lift f_state (config (Good g)))))
        (rendezvous (!! config § config (Good g)))).
assert (Hrel : Proper
  (RelationPairs.RelCompFun (equiv ==> equiv)%signature (projT1 (P:=precondition))) f_state_inv).
{ intros x y Hxy. cbn -[equiv]. now rewrite Hxy. }
transitivity (lift f_state_inv
  (rendezvous_pgm (map_spect (lift f_state)
       (!! config § config (Good g))))).
+ apply (lift_compat Hrel), (pgm_compat rendezvous), obs_from_config_map.
  intros x y Hxy. destruct f_state as [f [sim Hsim]]. cbn -[equiv]. rewrite <- Hsim. now f_equiv.
+ rewrite rendezvous_pgm_map.
  cbn -[equiv]. split; cbn -[equiv]; try reflexivity; []. apply Bijection.retraction_section.
Qed.

(** Correctness: if the program terminates, it is correct *)

(** Once we are gathered, everything is good. *)
Lemma gathered_at_forever : forall da config pt, similarity_da_prop da ->
  gathered_at pt config -> gathered_at pt (round rendezvous da config).
Proof using .
intros da config pt Hsim Hgather.
rewrite round_simplify; trivial; [].
intro g. destruct (da.(activate) (Good g)); [| now apply Hgather].
unfold rendezvous, rendezvous_pgm, obs_from_config, Obs.
destruct (config (Good r0)) as [pt1 l1] eqn:Hr0,
         (config (Good r1)) as [pt2 l2] eqn:Hr1.
assert (Hpt1 : pt1 == pt) by now rewrite <- Hgather, Hr0.
assert (Hpt2 : pt2 == pt) by now rewrite <- Hgather, Hr1.
assert (Hg : g = r0 \/ g = r1).
{ destruct g as [[| [| ?]] ?].
  - left. unfold r0. f_equal. apply le_unique.
  - right. unfold r1. f_equal. apply le_unique.
  - exfalso. lia. }
destruct Hg; subst g.
* rewrite Hr0. rewrite equiv_dec_refl.
  destruct l1, l2; cbn -[equiv middle]; trivial;
  try match goal with H : lt _ _, H' : lt _ _ |- _ => clear -H H'; exfalso; lia end; [].
  now rewrite Hpt1, middle_eq.
* rewrite Hr1. destruct_match.
  + match goal with H : (_, _) == _ |- _ => destruct H as [Hpt Hl] end.
    simpl in Hpt, Hl. subst. cbn -[equiv middle].
    repeat destruct_match; cbn -[equiv middle]; trivial; [].
    now rewrite Hpt1, middle_eq.
  + assert (Hl : l1 =/= l2).
    { intro Habs. cut ((pt1, l1) == (pt2, l2)); trivial; []. now split; rewrite Hpt1, Hpt2, Habs. }
    simpl in Hl.
  destruct l1, l2; cbn -[equiv middle]; trivial;
  try match goal with H : lt _ _, H' : lt _ _ |- _ => clear -H H'; exfalso; lia end; [].
  now rewrite Hpt2, middle_eq.
Qed.

Lemma gathered_at_over : forall d,
  Stream.forever (Stream.instant similarity_da_prop) d ->
  forall pt (config : configuration),
    gathered_at pt config -> Gather pt (execute rendezvous d config).
Proof using .
cofix Hind. intros d Hsim pt config Hgather. constructor.
+ clear Hind. simpl. assumption.
+ apply Hind; try apply gathered_at_forever; trivial; apply Hd || apply Hsim.
Qed.

(** Termination measure *)
Definition measure (config : configuration) : nat :=
  match snd (config (Good r0)), snd (config (Good r1)) with
    | A, A => 2
    | B, A | A, B => 1
    | B, B => 3
  end.

Instance measure_compat : Proper (equiv ==> eq) measure.
Proof using .
intros config1 config2 Hconfig. unfold measure.
assert (Hr0 := Hconfig (Good r0)). assert (Hr1 := Hconfig (Good r1)).
destruct (config1 (Good r0)) as [pt1 l1], (config1 (Good r1)) as [pt2 l2].
symmetry in Hr0, Hr1. destruct Hr0 as [Hpt1 Hl1], Hr1 as [Hpt2 Hl2].
cbn -[location] in Hl1, Hl2. rewrite Hl1, Hl2.
destruct l1, l2; simpl; reflexivity.
Qed.

(* A result ensuring that the measure strictly decreases after each round. *)
Lemma round_measure : forall da config, similarity_da_prop da ->
  moving rendezvous da config <> nil ->
  (exists pt, gathered_at pt (round rendezvous da config))
  \/ measure (round rendezvous da config) < measure config.
Proof using .
intros da config Hda Hmove.
destruct (gathered_at_dec config (get_location (config (Good r0)))) as [| Hgather];
[| destruct (gathered_at_dec (round rendezvous da config)
              (get_location (round rendezvous da config (Good r0)))) as [| Hgather']].
* left. eexists. now apply gathered_at_forever.
* left. now eexists.
* right. rewrite round_simplify; trivial; [].
  assert (Hone_active : activate da (Good r0) = true \/ activate da (Good r1) = true).
  { destruct (activate da (Good r0)) eqn:Hr0, (activate da (Good r1)) eqn:Hr1; auto; [].
    elim Hmove. apply incl_nil. cut (active da = nil).
    - intro Hactive. rewrite <- Hactive. apply moving_active.
      intros id Hid config'. reflexivity.
    - unfold active, names. simpl.
      assert (Hid : forall id, activate da id = false).
      { intro id. now destruct (id_case id); subst id. }
      now rewrite 2 Hid. }
  assert (Hneq : config (Good r0) =/= config (Good r1)).
  { intro Habs. apply Hgather. intro g.
    now destruct (id_case (Good g)) as [Hg | Hg]; rewrite Hg, ?Habs. }
  assert (Hobs1 : !! config § config (Good r0) = (config (Good r0), config (Good r1))).
  { unfold obs_from_config, Obs. now rewrite equiv_dec_refl. }
  assert (Hobs2 : !! config § config (Good r1) = (config (Good r1), config (Good r0))).
  { unfold obs_from_config, Obs. destruct_match; trivial; contradiction. }
    unfold measure. unfold obs_from_config, Obs, Datatypes.id.
    rewrite equiv_dec_refl.
    destruct (config (Good r0) =?= config (Good r1)); try contradiction; [].
  destruct (config (Good r0)) as [pt1 []] eqn:Hr0,
           (config (Good r1)) as [pt2 []] eqn:Hr1;
  cbn -[location location_Setoid location_EqDec middle].
  + (* both robots have color A, hence measure config = 2 *)
    destruct (activate da (Good r0)) eqn:Hactive1,
             (activate da (Good r1)) eqn:Hactive2; simpl.
    - (* both robots are active so they gather in one step *)
      exfalso. apply Hgather'. intro g.
      rewrite (round_simplify da config Hda (Good g)),
              (round_simplify da config Hda (Good r0)).
      destruct (id_case (Good g)) as [Hid | Hid]; inv Hid; try reflexivity; [].
      rewrite Hactive1, Hactive2. apply get_location_compat.
      rewrite Hr0, Hr1, Hobs1, Hobs2. cbn -[equiv middle].
      split; try reflexivity; []. apply middle_comm.
    - lia.
    - lia.
    - destruct Hone_active; discriminate.
  + (* one robot has color A, the other B, hence measure config = 1;
       since one robot moves, A is activated and they gather in one step *)
    assert (Hactive1 : activate da (Good r0) = true).
    { destruct (activate da (Good r0)) eqn:Hactive1; trivial; [].
      exfalso. apply Hmove.
      assert (Hmove1 : round rendezvous da config (Good r0) == config (Good r0)).
      { unfold round. rewrite Hactive1. reflexivity. }
      assert (Hmove2 : round rendezvous da config (Good r1) == config (Good r1)).
      { rewrite (round_simplify da config Hda (Good r1)).
        destruct_match; reflexivity || now rewrite Hr1, Hobs2. }
      assert (Hmoving := moving_spec rendezvous da config).
      destruct (moving rendezvous da config) as [| id ?]; trivial; exfalso; [].
      specialize (Hmoving id). apply proj1 in Hmoving. specialize (Hmoving ltac:(now left)).
      destruct (id_case id); subst id; contradiction. }
    exfalso. apply Hgather'. intro g.
    destruct (id_case (Good g)) as [Hid | Hid]; inv Hid; try reflexivity; [].
    rewrite (round_simplify da config Hda (Good r0)),
            (round_simplify da config Hda (Good r1)).
    rewrite Hactive1, Hr0, Hr1, Hobs1, Hobs2. cbn -[equiv].
    now destruct_match.
  + (* by symmetry, idem *)
    assert (Hactive2 : activate da (Good r1) = true).
    { destruct (activate da (Good r1)) eqn:Hactive2; trivial; [].
      exfalso. apply Hmove.
      assert (Hmove1 : round rendezvous da config (Good r0) == config (Good r0)).
      { rewrite (round_simplify da config Hda (Good r0)).
        destruct_match; reflexivity || now rewrite Hr0, Hobs1. }
      assert (Hmove2 : round rendezvous da config (Good r1) == config (Good r1)).
      { unfold round. rewrite Hactive2. reflexivity. }
      assert (Hmoving := moving_spec rendezvous da config).
      destruct (moving rendezvous da config) as [| id ?]; trivial; exfalso; [].
      specialize (Hmoving id). apply proj1 in Hmoving. specialize (Hmoving ltac:(now left)).
      destruct (id_case id); subst id; contradiction. }
    exfalso. apply Hgather'. intro g.
    destruct (id_case (Good g)) as [Hid | Hid]; inv Hid; try reflexivity; [].
    rewrite (round_simplify da config Hda (Good r0)),
            (round_simplify da config Hda (Good r1)).
    rewrite Hactive2, Hr0, Hr1, Hobs1, Hobs2. cbn -[equiv].
    now destruct_match.
  + (* both robots have color B, hence measure config = 3 *)
    destruct (activate da (Good r0)) eqn:Hactive1,
             (activate da (Good r1)) eqn:Hactive2; simpl.
    -- try lia.
    -- try lia.
    -- try lia.
    -- (* in coq8.13 lia also solves this. *)
      destruct Hone_active; discriminate.
Qed.

(** Fairness entails progress. *)
Lemma OneMustMove : forall config, ~(exists pt, gathered_at pt config) ->
  exists r, forall da, similarity_da_prop da -> activate da r = true ->
                       round rendezvous da config r =/= config r.
Proof using .
intros config Hnotgather.
destruct (config (Good r0)) as [pt1 l1] eqn:Hr0,
         (config (Good r1)) as [pt2 l2] eqn:Hr1.
assert (Hpt : pt1 =/= pt2).
{ intro Habs. rewrite Habs in Hr0. apply Hnotgather.
  exists (get_location (config (Good r0))). intros [[| [| ?]] ?]; simpl.
  + unfold r0. do 4 f_equal. now apply eq_proj1.
  + transitivity (Datatypes.id (fst (config (Good r1)))).
    - unfold r1. simpl. do 4 f_equal. now apply eq_proj1.
    - now rewrite Hr0, Hr1.
  + exfalso. lia. }
destruct l1 eqn:Hl1; [| destruct l2 eqn:Hl2].
+ (* if r0's color is A, it changes its location *)
  exists (Good r0). intros da Hda Hactivate.
  rewrite (round_simplify da config Hda (Good r0)).
  rewrite Hactivate. rewrite Hr0. unfold rendezvous, rendezvous_pgm, obs_from_config.
  cbn -[equiv equiv_dec middle]. rewrite Hr0, Hr1.
  destruct_match; try (now intuition); [].
  destruct_match.
  - intros [_ Habs]. simpl in Habs. congruence.
  - intros []. cbn -[equiv] in *. congruence.
+ (* if r1's color is A, it changes its location *)
  exists (Good r1). intros da Hda Hactivate.
  rewrite (round_simplify da config Hda (Good r1)).
  rewrite Hactivate. rewrite Hr1. unfold rendezvous, rendezvous_pgm, obs_from_config.
  cbn -[equiv equiv_dec middle]. rewrite Hr0, Hr1.
  assert ((pt1, B) =/= (pt2, A)) by (intros []; contradiction).
  destruct_match; try (now intuition); [].
  intros []; contradiction.
+ (* when both robots have color B, they change color. *) 
  exists (Good r0). intros da Hda Hactivate.
  rewrite (round_simplify da config Hda (Good r0)).
  rewrite Hactivate. rewrite Hr0. unfold rendezvous, rendezvous_pgm, obs_from_config.
  cbn -[equiv equiv_dec middle]. rewrite Hr0, Hr1.
  destruct_match; try (now intuition); [].
  intros [_ Habs]. simpl in Habs. congruence.
Qed.

Lemma Fair_FirstMove : forall d, Fair d -> Stream.forever (Stream.instant similarity_da_prop) d ->
  forall config, ~(exists pt, gathered_at pt config) -> FirstMove rendezvous d config.
Proof using .
intros d Hfair Hsim config Hgather.
destruct (OneMustMove config Hgather) as [idmove Hmove].
destruct Hfair as [locallyfair Hfair].
specialize (locallyfair idmove).
revert config Hgather Hmove.
induction locallyfair as [d Hnow | d]; intros config Hgather Hmove.
* apply MoveNow. apply Hmove in Hnow.
  + rewrite <- (moving_spec rendezvous (Stream.hd d) config idmove) in Hnow.
    intro Habs. rewrite Habs in Hnow. tauto.
  + apply Hsim.
* destruct (moving rendezvous (Stream.hd d) config) as [| id mov] eqn:Hmoving.
  + apply MoveLater; trivial; [].
    apply IHlocallyfair.
    - now destruct Hfair.
    - apply Hsim.
    - apply no_moving_same_config in Hmoving. now setoid_rewrite Hmoving.
    - intros da Hda Hactive. apply no_moving_same_config in Hmoving.
      rewrite (Hmoving idmove).
      apply (round_compat (reflexivity rendezvous) (reflexivity da)) in Hmoving; trivial; [].
      rewrite (Hmoving idmove).
      now apply Hmove.
  + apply MoveNow. rewrite Hmoving. discriminate.
Qed.

(** Final result: correctness of the Viglietta algorithm *)
Theorem Viglietta_correct : forall d, Fair d ->
  Stream.forever (Stream.instant similarity_da_prop) d ->
  forall config, WillGather (execute rendezvous d config).
Proof using .
intros d Hfair Hsim config.
generalize (eq_refl (measure config)). generalize (measure config) at -1.
intro n. revert d Hfair Hsim config. pattern n. apply (well_founded_ind lt_wf). clear n.
intros n Hind d Hfair Hsim config Hmeasure.
(* are we already gathered? *)
destruct (gathered_at_dec config (get_location (config (Good r0)))) as [Hgather | Hgather].
* (* if so, nothing to do *)
  apply Stream.Now.
  exists (get_location (config (Good r0))).
  now apply gathered_at_over.
* (* otherwise, we wait until one robot moves *)
  induction (Fair_FirstMove _ Hfair Hsim config) as [ | d config Hmove Hfirst IHf].
  + apply Stream.Later. rewrite (execute_tail rendezvous).
    change (WillGather (execute rendezvous (Stream.tl d) (round rendezvous (Stream.hd d) config))).
    (* are we gathered at the next step? *)
    destruct (gathered_at_dec (round rendezvous (Stream.hd d) config)
                                (get_location (round rendezvous (Stream.hd d) config (Good r0))))
      as [Hgather' | Hgather'].
    - (* if so, OK in one round *)
      apply Stream.Now. eexists. apply gathered_at_over; eauto; apply Hsim.
    - (* otherwise, we can use the induction hypothesis as the measure is smaller *)
      apply (Hind (measure (round rendezvous (Stream.hd d) config))).
      ++ subst n. destruct (round_measure (Stream.hd d) config) as [[pt Hpt] | ?]; trivial; [|].
         -- apply Hsim.
         -- elim Hgather'. now rewrite (Hpt r0).
      ++ apply Hfair.
      ++ apply Hsim.
      ++ reflexivity.
+ apply Stream.Later. apply IHf.
  - apply Hfair.
  - apply Hsim.
  - apply no_moving_same_config in Hmove. now rewrite Hmove.
  - apply no_moving_same_config in Hmove. now rewrite Hmove, (Hmove (Good r0)).
+ intros [pt Hpt]. apply Hgather. now rewrite (Hpt r0).
Qed.

End RDV.
