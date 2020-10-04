 (**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Implicit Arguments.
Require Import Utf8.
Require Import Lia.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.

Require Import Pactole.Setting.
Require Import Pactole.Spaces.Graph.
Require Import Pactole.Spaces.Isomorphism.
Require Import Pactole.Models.ContinuousGraph.
Require Import Pactole.Models.DiscreteGraph.


Typeclasses eauto := (bfs).
Open Scope R_scope.


Section GraphEquivalence.

Context (V E : Type).
Context {NN : Names}.
Context {G : Graph V E}.

(** We assume that the graph contains loops from each node to itself. *)
Variable self_loop : V -> E.
Hypothesis self_loop_spec : forall v, src (self_loop v) == v /\ tgt (self_loop v) == v.

(** Small dedicated decision tactic for reals handling 1<>0 and and r=r. *)
Ltac Rdec := repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] =>
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | |- context[Rdec 0 1] =>
        let Heq := fresh "Heq" in destruct (Rdec 0 1) as [Heq | Heq];
        [now symmetry in Heq; elim R1_neq_R0 | clear Heq]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ?x <> ?x |- _ => elim H; reflexivity
  end.

Existing Instance InfoV.
Existing Instance InfoG.

(** Notations to avoid typeclass resolution issues. *)
Notation locV := (@location LocationV).
Notation locG := (@location LocationG).

Notation DGF_config := (@configuration LocationV _ InfoV NN).
Notation CGF_config := (@configuration LocationG _ InfoG NN).

Notation DGF_da :=
  (@demonic_action _ _ InfoV _ _ _ _ _ _ FrameChoiceIsomorphismV graph_update_bool graph_inactive_bool).
Notation CGF_da :=
  (@demonic_action _ _ InfoG _ _ _ _ _ _ FrameChoiceIsomorphismG graph_update_ratio graph_inactive_ratio).

(** ** Translations of demonic actions **)

Definition relocate_byz_D2C (rel_byz : DGF_config -> B -> stateV) : CGF_config -> B -> stateG.
refine (fun (config : CGF_config) (b : B) =>
  SOnVertex (fst (proj1_sig (rel_byz (config_G2V config) b)))
            (snd (proj1_sig (rel_byz (config_G2V config) b))) _).
Proof.
abstract (destruct (rel_byz (config_G2V config) b) as [[] []];
          simpl in *; unfold valid_stateV; tauto).
Defined.

Instance relocate_byz_D2C_compat :
  Proper ((equiv ==> eq ==> equiv) ==> (equiv ==> eq ==> equiv)) relocate_byz_D2C.
Proof using .
intros f g Hfg config1 config2 Hconfig bb b ?. subst bb.
simpl. repeat split; apply Hfg; now f_equiv.
Qed.

Definition relocate_byz_C2D (rel_byz : CGF_config -> B -> stateG) : DGF_config -> B -> stateV :=
  fun (config : DGF_config) (b : B) => state_G2V (rel_byz (config_V2G config) b).

Instance relocate_byz_C2D_compat :
  Proper ((equiv ==> eq ==> equiv) ==> (equiv ==> eq ==> equiv)) relocate_byz_C2D.
Proof using .
intros f g Hfg config1 config2 Hconfig bb b ?. subst bb.
unfold relocate_byz_C2D. now apply state_G2V_compat, Hfg; f_equiv.
Qed.

Definition da_D2C (da : DGF_da) : CGF_da.
simple refine {|
  activate := da.(activate);
  relocate_byz := relocate_byz_D2C da.(relocate_byz);
  change_frame := fun config g => da.(change_frame) (config_G2V config) g;
  choose_update := fun config g target => if da.(choose_update) (config_G2V config) g target
                                          then ratio_1 else ratio_0;
  choose_inactive := fun config id =>
                       if da.(choose_inactive) (config_G2V config) id then ratio_1 else ratio_0 |}.
Proof.
+ intros config g. exists (proj1_sig (change_frame da (config_G2V config) g)).
  split; try reflexivity; []. apply (@proj2_sig _ stable_threshold).
+ intros config g.
  exists (inverse (proj1_sig (change_frame da (config_G2V config) g))).
  split; try reflexivity; []. cbn -[equiv]. apply stable_threshold_inverse, proj2_sig.
+ intros config1 config2 Hconfig gg g ?. subst gg. now rewrite Hconfig.
+ intros config1 config2 Hconfig gg g ? traj1 traj2 Htraj. subst gg. now rewrite Hconfig, Htraj.
+ intros config1 config2 Hconfig id1 id2 Hid. simpl in Hid. subst id1.
  now rewrite Hconfig.
Defined.

Instance da_D2C_compat : Proper (equiv ==> equiv) da_D2C.
Proof using .
intros da1 da2 Hda. split; [| split; [| split; [| split]]]; cbn -[equiv].
+ intro. now apply activate_da_compat.
+ intros. apply relocate_byz_D2C_compat; reflexivity || now apply relocate_byz_da_compat.
+ intros config g. apply (change_frame_da_compat Hda); auto.
+ intros id rc traj. erewrite (choose_update_da_compat Hda); auto.
+ intros config id. erewrite (choose_inactive_da_compat Hda); auto.
Qed.

(* We need to know the continuous config for [choose_inactive]
   to account for the position on the edge. *)
Definition da_C2D (da : CGF_da) (Cconfig : CGF_config) : DGF_da.
simple refine {|
  activate := da.(activate);
  relocate_byz := relocate_byz_C2D da.(relocate_byz);
  change_frame := fun config g => da.(change_frame) (config_V2G config) g;
  choose_update := fun config g target =>
    Rle_bool (threshold target) (da.(choose_update) (config_V2G config) g target);
  choose_inactive := fun config id =>
    let current_ratio :=
      match Cconfig id with (* we use the continuous config here *)
        | SOnVertex v e proof => ratio_0
        | SOnEdge e p => p
      end in
    let e := snd (proj1_sig (config id)) in
    Rle_bool (threshold e) (current_ratio + da.(choose_inactive) (config_V2G config) id) |};
try exact G; autoclass.
Proof.
+ intros config g. exists (proj1_sig (change_frame da (config_V2G config) g)).
  split; try reflexivity; []. apply proj2_sig.
+ intros config g. exists (inverse (proj1_sig (change_frame da (config_V2G config) g))).
  split; try reflexivity; []. apply stable_threshold_inverse, proj2_sig.
+ intros config1 config2 Hconfig gg g ?. subst gg. now rewrite Hconfig.
+ intros config1 config2 Hconfig gg g ? pt1 pt2 Hpt.
  f_equiv; try apply Hpt; [].
  f_equiv. now apply (choose_update_compat da); f_equiv.
+ intros config1 config2 Hconfig id1 id2 Hid. simpl in Hid. subst id1.
  assert (Hpt := Hconfig id2).
  destruct Hpt as [Hpt [[Hsrc Htgt] Hthd]],
           (proj1_sig (config1 id2)) as [pt1 e1],
           (proj1_sig (config2 id2)) as [pt2 e2].
  simpl in Hpt, Hsrc, Htgt, Hthd.
  destruct_match; simpl; rewrite Hthd; do 3 f_equiv;
  apply (choose_inactive_compat da); trivial; reflexivity.
Defined.

Instance da_C2D_compat : Proper (equiv ==> equiv ==> equiv) da_C2D.
Proof using .
intros da1 da2 Hda Cconfig1 Cconfig2 HCconfig.
split; [| split; [| split; [| split]]]; cbn -[equiv].
+ intro. now apply activate_da_compat.
+ intros. apply relocate_byz_C2D_compat; try reflexivity; [].
  apply (relocate_byz_da_compat Hda).
+ intros config g. apply (change_frame_da_compat Hda); auto.
+ intros config g target. erewrite (choose_update_da_compat Hda); auto.
+ intros config id. erewrite (choose_inactive_da_compat Hda); auto; [].
  specialize (HCconfig id).
  destruct (Cconfig1 id) as [| ? []], (Cconfig2 id) as [| ? []];
  try destruct HCconfig as [_ Hp]; simpl in *; subst; tauto.
Qed.

(** ** Final results: the translations commute with [round]. **)

Context {Obs : @Observation _ _ InfoV _}.
Notation robogramV := (@robogram _ _ InfoV _ Obs E _).
Notation robogramG := (@robogram _ _ InfoG _ (obs_V2G Obs) E _).

(** ***  Setting for discrete graphs  **)

Existing Instance graph_update_bool.
Existing Instance graph_inactive_bool.

Instance InactiveV : @inactive_function stateV LocationV InfoV NN bool _.
simple refine {| inactive := fun (config : DGF_config) id (b : bool) =>
                               if b then let '(exist _ (v, e) proof) := config id in
                                         exist _ (tgt e, e) (or_intror (reflexivity _))
                                    else config id |}; auto; [].
Proof.
intros config1 config2 Hconfig ? id ? ? ? Hb. simpl in Hb. subst.
specialize (Hconfig id).
destruct_match; trivial; [].
repeat destruct_match; simpl in *. tauto.
Defined.

Instance UpdateV : @update_function stateV LocationV InfoV NN E (sig stable_threshold) bool
   _ (FrameChoiceIsomorphismV) graph_update_bool.
simple refine {|
  update := fun config g (frame : sig stable_threshold) (target : E) (choice : bool) =>
    let pt : locV := get_location (config (Good g)) in
    if pt =?= src target
    then if choice then exist valid_stateV (tgt target, target) (or_intror (reflexivity _))
                   else exist valid_stateV (src target, target) (or_introl (reflexivity _))
    else config (Good g) |}; [| | eassumption | ..]; autoclass; [].
Proof.
intros ? ? Hconfig ? ? ? ? ? Hframe ? ? Htarget ? ? Hchoice.
simpl in Hchoice. subst. cbn zeta.
repeat destruct_match;
solve [ simpl; repeat split; apply Htarget
      | match goal with | H : complement _ _ _ |- _ => elim H end;
        simpl in Htarget; now (rewrite <- Hconfig, <- (proj1 (proj1 Htarget)))
                           || (rewrite Hconfig, (proj1 (proj1 Htarget)))
      | apply Hconfig ].
Defined.

(** ***  Setting for continuous graphs  **)

Existing Instance graph_update_ratio.
Existing Instance graph_inactive_ratio.
Existing Instance FrameChoiceIsomorphismG.

(** Build the state on edge [e] at ratio [ρ1 + ρ2]. *)
Definition add_edge (e : E) (ρ1 ρ2 : ratio) : stateG.
refine (if (ρ1 + ρ2)%R =?= 0%R then SOnVertex (src e) e ltac:(now left) else
        if Rle_dec 1 (ρ1 + ρ2) then SOnVertex (tgt e) e ltac:(now right)
                               else SOnEdge e (exist _ (ρ1 + ρ2)%R _)).
Proof.
abstract (split; try solve [ apply Rle_neq_lt; (apply Rplus_le_le_0_compat; apply ratio_bounds)
                                            || (simpl in *; lra)
                           | now apply Rnot_le_lt ]).
Defined.

Instance add_edge_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) add_edge.
Proof using .
intros ? ? He ρ1 ρ1' Hρ1 ρ2 ρ2' Hρ2. unfold add_edge.
Time repeat destruct_match; solve [ rewrite Hρ1, Hρ2 in *; contradiction
                                  | rewrite <- Hρ1, <- Hρ2 in *; contradiction
                                  | simpl; rewrite ?Hρ1, ?Hρ2; repeat split; apply He ].
Qed.

(** Move by a ratio [ρ] from the state [state]. *)
Definition move (state : stateG) (ρ : ratio) : stateG :=
  match state with
    | SOnVertex v e proof => if v =?= src e then add_edge e ratio_0 ρ
                                            else SOnVertex (tgt e) e ltac:(now right)
    | SOnEdge e p => add_edge e p ρ
  end.

Instance move_compat : Proper (equiv ==> equiv ==> equiv) move.
Proof using .
intros [v1 e1 proof1 | e1 p1] [v2 e2 proof2 | e2 p2] Heq ρ1 ρ2 Hρ; simpl in Heq; try tauto; [|].
+ unfold move. destruct Heq as [Hv [[Hsrc Htgt] Hthd]].
  do 2 destruct_match.
  - now f_equiv.
  - match goal with H : complement _ _ _ |- _ => elim H end.
    now rewrite <- Hv, <- Hsrc.
  - match goal with H : complement _ _ _ |- _ => elim H end.
    now rewrite Hv, Hsrc.
  - simpl. tauto.
+ unfold move. f_equiv; auto; []. now destruct p1, p2.
Qed.

Instance InactiveG : @inactive_function _ _ InfoG _ ratio _.
refine {| inactive := fun config id ρ => move (config id) ρ |}.
Proof. repeat intro. subst. now f_equiv. Defined.

Instance UpdateG : @update_function _ _ _ _ _ (sig stable_threshold) ratio
                                    _ FrameChoiceIsomorphismG _.
refine {|
  update := fun (config : CGF_config) g frame target ρ =>
    match config (Good g) with
      | SOnVertex v e proof =>
        if v =?= src target then move (SOnVertex v target ltac:(now left)) ρ else config (Good g)
      | SOnEdge e p => config (Good g)
    end |}.
Proof.
intros config1 config2 Hconfig gg g ? iso1 iso2 Hframe target1 target2 Htarget ρ1 ρ2 Hρ. subst gg.
assert (Hsrc := src_compat _ _ Htarget).
assert (Htgt := tgt_compat _ _ Htarget).
specialize (Hconfig (Good g)).
destruct (config1 (Good g)) as [v1 e1 proof1 | e1 p1],
         (config2 (Good g)) as [v2 e2 proof2 | e2 p2]; trivial;
try destruct (v1 =?= src target1) as [Hsrc1 | Hsrc1],
             (v2 =?= src target2) as [Hsrc2 | Hsrc2].
+ f_equiv; trivial; []. simpl.
  rewrite Hsrc1, Hsrc2. repeat split; auto; apply Htarget.
+ match goal with H : complement _ _ _ |- _ => elim H end.
  now rewrite <- Hsrc, <- (proj1 Hconfig).
+ match goal with H : complement _ _ _ |- _ => elim H end.
  now rewrite Hsrc, (proj1 Hconfig).
+ assumption.
+ tauto.
+ tauto.
Defined.

Theorem graph_equivD2C : forall (config : DGF_config) (rbg : robogramV) (da : DGF_da),
  config_V2G (round rbg da config) == round (rbg_V2G rbg) (da_D2C da) (config_V2G config).
Proof using All.
intros config rbg da id.
unfold config_V2G at 1. cbv beta delta [round].
simpl activate. destruct_match.
* (* activate = true *)
  destruct id as [g | b].
  + (* id = Good g *)
    cbv zeta.
    (* folding lets for the discrete case *)
    pose (Dstate := config (Good g)). fold Dstate.
    pose (Dframe_choice := change_frame da config g). fold Dframe_choice.
    pose (Dnew_frame := frame_choice_bijection (frame_choice := FrameChoiceIsomorphismV) Dframe_choice).
    fold Dnew_frame.
    pose (Dlocal_config := map_config (lift (existT precondition
                     (Bijection.section Dnew_frame) (precondition_satisfied da config g))) config).
    fold (Dlocal_config).
    pose (Dlocal_state := Dlocal_config (Good g)). fold Dlocal_state.
    pose (Dobs := obs_from_config Dlocal_config Dlocal_state). fold Dobs.
    pose (Dlocal_robot_decision := rbg Dobs). fold Dlocal_robot_decision.
    pose (Dchoice := choose_update da Dlocal_config g Dlocal_robot_decision). fold Dchoice.
    pose (Dnew_local_state := update Dlocal_config g Dframe_choice Dlocal_robot_decision Dchoice).
    fold Dnew_local_state.
    (* folding lets for the continuous case *)
    pose (Cstate := config_V2G config (Good g)). fold Cstate.
    pose (Cframe_choice := change_frame (da_D2C da) (config_V2G config) g). fold Cframe_choice.
    pose (Cnew_frame := frame_choice_bijection (frame_choice := FrameChoiceIsomorphismG) Cframe_choice).
    fold Cnew_frame.
    pose (Clocal_config := map_config (lift (existT precondition
                     (Bijection.section Cnew_frame) (precondition_satisfied (da_D2C da)
                                                      (config_V2G config) g))) (config_V2G config)).
    fold (Clocal_config).
    pose (Clocal_state := Clocal_config (Good g)). fold Clocal_state.
    pose (Cobs := obs_from_config Clocal_config Clocal_state). fold Cobs.
    pose (Clocal_robot_decision := (rbg_V2G rbg) Cobs). fold Clocal_robot_decision.
    pose (Cchoice := choose_update (da_D2C da) Clocal_config g Clocal_robot_decision). fold Cchoice.
    pose (Cnew_local_state := update Clocal_config g Cframe_choice Clocal_robot_decision Cchoice).
    fold Cnew_local_state.
    (* proving the relation between both side for each intermediate value *)
    assert (Hstate : Cstate == state_V2G Dstate) by reflexivity.
    assert (Hframe_choice : Cframe_choice == Dframe_choice).
    { unfold Cframe_choice, Dframe_choice. simpl change_frame. rewrite config_V2G2V. reflexivity. }
    assert (Hframe : forall v, Cnew_frame (OnVertex v) == OnVertex (Dnew_frame v)).
    { intro. unfold Dnew_frame. simpl. apply (proj1 Hframe_choice). }
    pose (Ciso := proj1_sig Cframe_choice).
    pose (Diso := proj1_sig Dframe_choice).
    assert (Hiso : Ciso == Diso).
    { subst Ciso Diso. apply Hframe_choice. }
    assert (HCiso : projT1 (precondition_satisfied (da_D2C da) (config_V2G config) g) == Ciso).
    { destruct (precondition_satisfied (da_D2C da) (config_V2G config) g)
        as [Ciso' [HCf HCt]] eqn:HCiso. simpl projT1.
      change (projT1 (existT (good_iso_of _) Ciso' (conj HCf HCt)) == proj1_sig Cframe_choice).
      rewrite <- HCiso. cbn -[equiv]. reflexivity. }
    (* We do not have full iso equivalence as we only distinguish edges up to src, tgt and thd *)
    assert (HDiso : forall v, projT1 (precondition_satisfied da config g) v == Diso v).
    { intro x. rewrite <- (proj1 (projT2 (precondition_satisfied da config g)) x). reflexivity. }
    assert (Hlocal_config : Clocal_config == config_V2G Dlocal_config).
    { intro id. unfold Clocal_config, Dlocal_config, map_config.
      destruct (config id) as [[v e] Hv] eqn:Hconfig.
      change lift with liftG at 1. unfold liftG. unfold config_V2G at 1.
      unfold state_V2G, projT2. split.
      * simpl fst. f_equiv. transitivity Ciso; now f_equiv.
      * cbn -[equiv precondition_satisfied]. rewrite Hconfig. simpl snd.
        transitivity (iso_E Ciso e); [| transitivity (iso_E Diso e)].
        + f_equiv.
        + apply E_subrelation, (Isomorphism.iso_E_compat Hiso e).
        + repeat split.
          - unfold equiv. cbn -[equiv].
            now rewrite <- (proj1 (iso_morphism Diso e)), <- HDiso, (proj1 (iso_morphism _ e)).
          - unfold equiv. cbn -[equiv].
            now rewrite <- (proj2 (iso_morphism Diso e)), <- HDiso, (proj2 (iso_morphism _ e)).
          - unfold equiv. cbn -[equiv].
            rewrite <- 2 iso_threshold. unfold Diso. rewrite (proj2_sig Dframe_choice).
            destruct  (precondition_satisfied da config g) as [? [? Ht]]. simpl. now rewrite Ht. }
    assert (Hlocal_state : Clocal_state == state_V2G Dlocal_state).
    { unfold Clocal_state. rewrite Hlocal_config. reflexivity. }
    assert (Hobs : Cobs == Dobs).
    { unfold Cobs, Dobs. unfold obs_from_config at 1. unfold obs_V2G.
      rewrite Hlocal_config, Hlocal_state. reflexivity. }
    assert (Hlocal_robot_decision : Clocal_robot_decision == Dlocal_robot_decision).
    { unfold Dlocal_robot_decision. cbn -[equiv]. rewrite Hobs. reflexivity. }
    assert (Hchoice : Cchoice == if Dchoice then ratio_1 else ratio_0).
    { cbn -[equiv]. unfold Dchoice.
      rewrite Hlocal_config, config_V2G2V, Hobs. reflexivity. }
    assert (Hnew_local_state : Cnew_local_state == state_V2G Dnew_local_state).
    { unfold Cnew_local_state, Dnew_local_state. unfold update, UpdateG, UpdateV.
      assert (Hlocal_g := Hlocal_config (Good g)). unfold config_V2G in Hlocal_g.
      destruct (Dlocal_config (Good g)) as [[v e] Hvalid] eqn:Hg.
      simpl get_location. unfold state_V2G in Hlocal_g. simpl fst in Hlocal_g.
      simpl snd in Hlocal_g. simpl proj2_sig in Hlocal_g.
      destruct (Clocal_config (Good g)) as [v' e' proof' |] eqn:Hg'; try tauto; [].
      destruct Hlocal_g as [Heqv Heqe].
      destruct (v' =?= src Clocal_robot_decision) as [Hv' | Hv'],
               (v =?= src Dlocal_robot_decision) as [Hv | Hv].
      + (* valid case: the robot chooses an adjacent edge *)
        unfold move. destruct_match; try contradiction; [].
        rewrite Hchoice, Hlocal_robot_decision. destruct Dchoice.
        - (* the demon lets the robot move *)
          unfold add_edge. simpl equiv_dec.
          destruct ((0 + 1)%R =?= 0%R); try (simpl in *; lra); [].
          simpl (Rle_dec 1 (ratio_0 + ratio_1)).
          destruct (Rle_dec 1 (0 + 1)); try (simpl in *; lra); [].
          simpl. repeat split; reflexivity.
        - (* the demon does not let the robot move *)
          unfold add_edge. simpl equiv_dec.
          destruct ((0 + 0)%R =?= 0%R);
          try (match goal with H : complement _ _ _ |- _ => elim H; simpl in *; lra end); [].
          simpl. repeat split; reflexivity.
      + (* absurd case: the robot does not make the same choice *)
        match goal with | H : complement _ _ _ |- _ => elim H end.
        rewrite <- Heqv, Hv'. apply Hlocal_robot_decision.
      + (* absurd case: the robot does not make the same choice *)
        match goal with | H : complement _ _ _ |- _ => elim H end.
        rewrite Heqv, Hv. symmetry. apply Hlocal_robot_decision.
      + (* invalid case: the robot does not choose an adjacent edge *)
        simpl. repeat split; apply Heqv || apply Heqe. }
    (* actual proof *)
    assert (HCiso' : forall x, projT1 (precondition_satisfied_inv
                                         (da_D2C da) (config_V2G config) g) x
                     == inverse Ciso x).
    { destruct (precondition_satisfied_inv (da_D2C da) (config_V2G config) g) as [iso' [Hiso' Ht']].
      destruct (precondition_satisfied (da_D2C da) (config_V2G config) g) as [iso [Hiso'' Ht]].
      simpl projT1 in *. clear -Hiso Hiso'' Hiso' HCiso.
      intro v. change (bijectionG iso' (OnVertex v) == bijectionG (inverse Ciso) (OnVertex v)).
      now rewrite <- (Hiso' (OnVertex v)). }
    assert (HDiso' : forall x, projT1 (precondition_satisfied_inv da config g) x == inverse Diso x).
    { destruct (precondition_satisfied_inv da config g) as [iso' [Hiso' Ht']].
      destruct (precondition_satisfied da config g) as [iso [Hiso'' Ht]].
      simpl projT1 in *. clear -Hiso Hiso'' Hiso' HCiso.
      intro v. rewrite <- (Hiso' v). reflexivity. }
    unfold lift, InfoG, InfoV. simpl projT1.
    Time setoid_rewrite Hnew_local_state.
    destruct Dnew_local_state as [[v e] Hvalid].
    unfold state_V2G. simpl fst. simpl snd. simpl proj2_sig.
    unfold liftG. cbn [projT2]. repeat split.
    - rewrite HCiso'. cbn. f_equiv. symmetry. apply Hiso.
    - unfold equiv. cbn -[equiv precondition_satisfied_inv].
      Time setoid_rewrite <- (proj1 (iso_morphism _ e)).
      Time setoid_rewrite HCiso'.
      transitivity (inverse Diso (src e)); try apply HDiso'; [].
      f_equiv. apply inverse_compat. now symmetry.
    - unfold equiv. cbn -[equiv precondition_satisfied_inv].
      Time setoid_rewrite <- (proj2 (iso_morphism _ e)).
      Time setoid_rewrite HCiso'.
      transitivity (inverse Diso (tgt e)); try apply HDiso'; [].
      f_equiv. apply inverse_compat. now symmetry.
    - hnf. rewrite <- 2 iso_threshold.
      rewrite (proj2 (projT2 (precondition_satisfied_inv da config g))).
      rewrite (proj2 (projT2 (precondition_satisfied_inv (da_D2C da) (config_V2G config) g))).
      reflexivity.
  + (* id = Byz b *)
    cbn zeta. simpl relocate_byz at 2. unfold relocate_byz_D2C. unfold state_V2G.
    assert (Hequiv := relocate_byz_compat da (config_V2G2V config) (eq_refl b)).
    repeat split;
    destruct (relocate_byz da config b), (relocate_byz da (config_G2V (config_V2G config)) b);
    simpl in *; auto; now symmetry.
* (* activate = false *)
  cbv zeta. simpl choose_inactive at 2.
  assert (Heq := choose_inactive_compat da (config_V2G2V config) (eq_refl id)).
  simpl in Heq. rewrite Heq.
  unfold inactive, InactiveV, InactiveG, move, config_V2G. unfold state_V2G at 2.
  destruct (config id) as [[v e] Hvalid] eqn:Hconfig. simpl fst; simpl snd.
  destruct (v =?= src e) as [Hv | Hv].
  + (* valid case: *)
    destruct_match.
    - (* the demon chooses to let the robot move *)
      unfold add_edge. simpl.
      destruct ((0 + 1)%R =?= 0%R); try (simpl in *; lra); [].
      destruct (Rle_dec 1 (0 + 1)); try lra; [].
      repeat split; reflexivity.
    - (* the demon chooses not to let the robot move *)
      unfold add_edge. simpl.
      destruct ((0 + 0)%R =?= 0%R);
      try (match goal with H : complement _ _ _ |- _ => elim H; simpl in *; lra end); [].
      repeat split; assumption || reflexivity.
  + unfold valid_stateV in *. simpl in Hvalid.
    destruct Hvalid as [ | Hvalid]; try contradiction; [].
    destruct_match; simpl; repeat split; assumption || reflexivity.
Time Qed.

(** NB: For the converse result to hold, we need two extra hypotheses:
        1) all the demon choices must only depend on the discrete position of robots,
           otherwise the continuous demon can make more distinctions than the discrete one;
        2) robots can only be activated on vertices, a robot on an edge waits to reach its tgt. *)
Theorem graph_equiv_C2D : forall (config : CGF_config) (rbg : robogramG) (da : CGF_da),
  (** demon choices only depends on the discrete locations of robots *)
  (forall g, change_frame da (config_V2G (config_G2V config)) g  == change_frame da config g) ->
  (forall config g x, (* we need to quantify over [config] as it is the local version that is used *)
     choose_update da (config_V2G (config_G2V config)) g x == choose_update da config g x) ->
  (forall b, relocate_byz da (config_V2G (config_G2V config)) b == relocate_byz da config b) ->
  (forall id, choose_inactive da (config_V2G (config_G2V config)) id == choose_inactive da config id) ->
  (** robots are only activated on vertices *)
  (forall g, activate da (Good g) = true -> forall e p, config (Good g) =/= SOnEdge e p) ->
  config_G2V (round rbg da config) == round (rbg_G2V rbg) (da_C2D da config) (config_G2V config).
Proof using All.
intros config rbg da Hchange_frame Hchoose_update Hrelocate_byz Hchoose_inactive Hactivate id.
unfold config_G2V at 1. cbv beta delta [round].
simpl activate. destruct_match_eq Hactive.
* (* activate = true *)
  destruct id as [g | b].
  + (* id = Good g *)
    cbv zeta.
    (* folding lets for the continuous case *)
    pose (Cstate := config (Good g)). fold Cstate.
    pose (Cframe_choice := change_frame da config g). fold Cframe_choice.
    pose (Cnew_frame := @frame_choice_bijection _ _ FrameChoiceIsomorphismG Cframe_choice).
    fold Cnew_frame.
    pose (Clocal_config := map_config
            (lift (existT precondition Cnew_frame (precondition_satisfied da config g)))
            config). fold Clocal_config.
    pose (Clocal_state := Clocal_config (Good g)). fold Clocal_state.
    pose (Cobs := obs_from_config Clocal_config Clocal_state). fold Cobs.
    pose (Clocal_robot_decision := rbg Cobs). fold Clocal_robot_decision.
    pose (Cchoice := choose_update da Clocal_config g Clocal_robot_decision). fold Cchoice.
    pose (Cnew_local_state := update Clocal_config g Cframe_choice Clocal_robot_decision Cchoice).
    fold Cnew_local_state.
    (* folding lets for the discrete case *)
    pose (Dstate := config_G2V config (Good g)). fold Dstate.
    pose (Dframe_choice := change_frame (da_C2D da config) (config_G2V config) g). fold Dframe_choice.
    pose (Dnew_frame := @frame_choice_bijection _ _ FrameChoiceIsomorphismV Dframe_choice).
    fold Dnew_frame.
    pose (Dlocal_config := map_config
           (lift (existT precondition Dnew_frame
              (precondition_satisfied (da_C2D da config) (config_G2V config) g))) (config_G2V config)).
    fold Dlocal_config.
    pose (Dlocal_state := Dlocal_config (Good g)). fold Dlocal_state.
    pose (Dobs := obs_from_config Dlocal_config Dlocal_state). fold Dobs.
    pose (Dlocal_robot_decision := (rbg_G2V rbg) Dobs). fold Dlocal_robot_decision.
    pose (Dchoice := choose_update (da_C2D da config) Dlocal_config g Dlocal_robot_decision).
    fold Dchoice.
    pose (Dnew_local_state := update Dlocal_config g Dframe_choice Dlocal_robot_decision Dchoice).
    fold Dnew_local_state.
    (* proving the relation between both side for each intermediate value *)
    assert (Hstate : Dstate == state_G2V Cstate) by reflexivity.
    assert (Hframe_choice : Dframe_choice == Cframe_choice).
    { unfold Cframe_choice, Dframe_choice. simpl change_frame. now rewrite Hchange_frame. }
    assert (Hframe : forall v, Dnew_frame v == location_G2V (Cnew_frame (OnVertex v))).
    { intro. unfold Dnew_frame. simpl. apply (proj1 Hframe_choice). }
    pose (Ciso := proj1_sig Cframe_choice).
    pose (Diso := proj1_sig Dframe_choice).
    assert (Hiso : Diso == Ciso).
    { subst Ciso Diso. apply Hframe_choice. }
    assert (HDiso : projT1 (precondition_satisfied (da_C2D da config) (config_G2V config) g) == Diso).
    { destruct (precondition_satisfied (da_C2D da config) (config_G2V config) g)
        as [Diso' [HDf HDt]] eqn:HDiso. simpl projT1.
      pose (iso_OKV := fun f (iso : @isomorphism (@location LocationV) E G) =>
                                  frame_choice_bijection f == iso.(iso_V)
                                  /\ iso_T iso == @Bijection.id R R_Setoid).
      change (projT1 (existT (iso_OKV _) Diso' (conj HDf HDt)) == proj1_sig Dframe_choice).
      fold (iso_OKV (change_frame (da_C2D da config) (config_G2V config) g)) in HDiso.
      change (precondition_satisfied (da_C2D da config) (config_G2V config) g =
        existT (iso_OKV (change_frame (da_C2D da config) (config_G2V config) g)) Diso' (conj HDf HDt))
        in HDiso.
      rewrite <- HDiso. cbn -[equiv]. reflexivity. }
    (* We do not have full iso equivalence as we only distinguish edges up to src, tgt and thd *)
    assert (HCiso :
              forall x, bijectionG (projT1 (precondition_satisfied da config g)) x == bijectionG Ciso x).
    { intro x. rewrite <- (proj1 (projT2 (precondition_satisfied da config g)) x). reflexivity. }
    assert (Hlocal_config : Dlocal_config == config_G2V Clocal_config).
    { intro id. unfold Clocal_config, Dlocal_config, map_config.
      change lift with liftG at 2. unfold lift, InfoV.
      cbn -[equiv precondition_satisfied Cnew_frame Dnew_frame].
      destruct (config id) as [v e proof | e p].
      * (* OnVertex *)
        simpl state_G2V. repeat split.
        + simpl fst. rewrite Hframe. unfold config_G2V.
          transitivity (Ciso v); reflexivity || now symmetry; apply (HCiso (OnVertex v)).
        + cbn -[precondition_satisfied].
          rewrite <- 2 (proj1 (iso_morphism _ _)),
                  (iso_V_compat HDiso (src e)),
                  (iso_V_compat Hiso (src e)).
          symmetry. apply (HCiso (OnVertex (src e))).
        + cbn -[precondition_satisfied].
          rewrite <- 2 (proj2 (iso_morphism _ _)),
                  (iso_V_compat HDiso (tgt e)),
                  (iso_V_compat Hiso (tgt e)).
          symmetry. apply (HCiso (OnVertex (tgt e))).
        + cbn -[precondition_satisfied]. rewrite <- 2 iso_threshold.
          now rewrite (proj2 (projT2 (precondition_satisfied da config g))),
                      (proj2 (projT2 (precondition_satisfied (da_C2D da config) (config_G2V config) g))).
      * (* OnEdge *)
        simpl liftG. simpl state_G2V.
        assert (Heq : threshold ((iso_E (projT1 (precondition_satisfied da config g))) e) = threshold e).
        { now rewrite <- iso_threshold, (proj2 (projT2 (precondition_satisfied da config g))). }
        destruct (Rle_dec (threshold e) p);
        destruct_match; try (rewrite <- Heq in *; contradiction); [|].
        + (* we are after the threshold, g is seen at the target of the edge *)
          cbn -[precondition_satisfied]. repeat split.
          - rewrite <- (proj2 (iso_morphism _ _)).
            transitivity (Ciso (tgt e)); try (symmetry; apply (HCiso (OnVertex (tgt e)))); [].
            transitivity (Diso (tgt e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (proj1 (iso_morphism _ _)).
            transitivity (Ciso (src e)); try (symmetry; apply (HCiso (OnVertex (src e)))); [].
            transitivity (Diso (src e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (proj2 (iso_morphism _ _)).
            transitivity (Ciso (tgt e)); try (symmetry; apply (HCiso (OnVertex (tgt e)))); [].
            transitivity (Diso (tgt e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (iso_threshold _ _).
            rewrite (proj2 (projT2 (precondition_satisfied da config g))),
                    (proj2 (projT2 (precondition_satisfied (da_C2D da config) (config_G2V config) g))).
            reflexivity.
        + (* we are before the threshold, g is seen at the source of the edge *)
          cbn -[precondition_satisfied]. repeat split.
          - rewrite <- (proj1 (iso_morphism _ _)).
            transitivity (Ciso (src e)); try (symmetry; apply (HCiso (OnVertex (src e)))); [].
            transitivity (Diso (src e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (proj1 (iso_morphism _ _)).
            transitivity (Ciso (src e)); try (symmetry; apply (HCiso (OnVertex (src e)))); [].
            transitivity (Diso (src e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (proj2 (iso_morphism _ _)).
            transitivity (Ciso (tgt e)); try (symmetry; apply (HCiso (OnVertex (tgt e)))); [].
            transitivity (Diso (tgt e)); try apply Hiso; [].
            reflexivity.
          - rewrite <- 2 (iso_threshold _ _).
            rewrite (proj2 (projT2 (precondition_satisfied da config g))),
                    (proj2 (projT2 (precondition_satisfied (da_C2D da config) (config_G2V config) g))).
            reflexivity. }
    assert (Hlocal_state : Dlocal_state == state_G2V Clocal_state).
    { unfold Dlocal_state, Clocal_state. rewrite Hlocal_config. reflexivity. }
    assert (Hobs : Dobs == Cobs).
    { unfold Cobs, Dobs. unfold obs_from_config at 2. unfold obs_V2G.
      rewrite Hlocal_config, Hlocal_state. reflexivity. }
    assert (Hlocal_robot_decision : Dlocal_robot_decision == Clocal_robot_decision).
    { unfold Dlocal_robot_decision. cbn -[equiv]. rewrite Hobs. reflexivity. }
    assert (Hchoice : Dchoice == if Rle_dec (threshold Clocal_robot_decision) Cchoice
                                 then true else false).
    { unfold Dchoice, choose_update, da_C2D.
      rewrite Hlocal_config, Hchoose_update. rewrite Hlocal_robot_decision at 2.
      assert (Hthd := proj2 Hlocal_robot_decision). hnf in Hthd. rewrite Hthd.
      destruct (Rle_dec (threshold Clocal_robot_decision) Cchoice) as [Hle | Hlt].
      - rewrite <- Rle_bool_true_iff in Hle. apply Hle.
      - rewrite <- Rle_bool_false_iff in Hlt. apply Hlt. }
    assert (HCiso' : forall v, projT1 (precondition_satisfied_inv da config g) v == inverse Ciso v).
    { destruct (precondition_satisfied_inv da config g)as [Ciso' [HCf HCt]].
      simpl projT1. intro v.
      change (bijectionG Ciso' (OnVertex v) == bijectionG (inverse Ciso) (OnVertex v)).
      rewrite <- (HCf (OnVertex v)). reflexivity. }
    assert (HCisoE : forall e, iso_E (projT1 (precondition_satisfied_inv da config g)) e
                               == iso_E (inverse Ciso) e).
    { destruct (precondition_satisfied_inv da config g)as [Ciso' [HCf HCt]].
      simpl projT1. intro e.
      cut (bijectionG Ciso' (OnEdge e (1 /sr 2)) == bijectionG (inverse Ciso) (OnEdge e (1 /sr 2)));
      try (now intros [Heq _]); [].
      rewrite <- (HCf (OnEdge e (1 /sr 2))). reflexivity. }
    assert (HnotOnEdge : forall e p, Clocal_config (Good g) =/= SOnEdge e p).
    { intros e0 p0 H0.
      destruct (Clocal_config (Good g)) as [| e p] eqn:Habs; try tauto; [].
      clear e0 p0 H0. move Habs at bottom.
      apply Hactivate with _ (iso_E (inverse Ciso) e) p in Hactive. apply Hactive.
      apply (f_equal (lift (existT _ _ (precondition_satisfied_inv da config g)))) in Habs.
      simpl lift in Habs at 2. apply (@eq_subrelation _ equiv _) in Habs.
      rewrite <- (SOnEdge_compat _ _ (HCisoE e) p p eq_refl).
      etransitivity; [| apply Habs].
      unfold Clocal_config, map_config, lift, InfoG in Habs |- *.
      rewrite (liftG_compose _ _ (config (Good g))). unfold compose_precondition.
      change (change_frame da config g) with Cframe_choice.
      change (frame_choice_bijection Cframe_choice) with Cnew_frame.
      destruct (config (Good g)) as [| e' p']; [simpl in Habs |- *; tauto |].
      split; try reflexivity; [].
      cbn -[equiv]. symmetry.
      transitivity (iso_E (inverse Ciso) ((iso_E (projT1 (precondition_satisfied da config g))) e'));
      [| transitivity (iso_E (inverse Ciso) (iso_E Ciso e'))].
      - apply HCisoE.
      - specialize (HCiso (OnEdge e' p)). destruct HCiso as [HCiso _].
        apply iso_E_compat, HCiso.
      - cbn -[equiv]. apply E_subrelation, Bijection.retraction_section. }
    assert (Hnew_local_state : Dnew_local_state == state_G2V Cnew_local_state).
    { unfold Cnew_local_state, Dnew_local_state. unfold update, UpdateG, UpdateV.
      assert (Hlocal_g := Hlocal_config (Good g)). unfold config_G2V in Hlocal_g.
      destruct (Clocal_config (Good g)) as [v e proof | e p] eqn:Hg;
      try (exfalso; apply (HnotOnEdge _ _ (reflexivity _))); [].
      (* the robot is on a vertex *)
      apply get_location_compat in Hlocal_g.
      unfold state_G2V in Hlocal_g.
      simpl get_location in Hlocal_g at 2.
      unfold move. simpl fst. symmetry.
      do 2 destruct_match.
      * (* valid case: the robot chooses an adjacent edge *)
        rewrite Hchoice. unfold add_edge.
        destruct_match; [| destruct_match]; simpl state_G2V.
        + (* the robot will not move so will end up in its starting position *)
          assert (H0 : proj_ratio Cchoice = 0%R).
          { assert (Hbounds := ratio_bounds Cchoice). simpl in *; lra. }
          assert (proj_ratio Cchoice < threshold Clocal_robot_decision)%R.
          { rewrite H0. apply threshold_pos. }
          destruct_match; try lra; []. symmetry. split; apply Hlocal_robot_decision.
        + (* the robot reaches its destination *)
          change (proj_ratio ratio_0) with 0%R in *. rewrite Rplus_0_l in *.
          assert (threshold Clocal_robot_decision <= proj_ratio Cchoice)%R.
          { transitivity 1; trivial; []. apply Rlt_le. apply threshold_pos. }
          destruct_match; try lra; [].
          symmetry. hnf. simpl fst. simpl snd. split; apply Hlocal_robot_decision.
        + (* the robot moves and ends up on the edge *)
          rewrite Rplus_0_l in *.
          destruct_match.
          - (* the ending point is after the edge threshold *)
            symmetry. repeat split; simpl; apply Hlocal_robot_decision.
          - (* the ending point is before the edge threshold *)
            symmetry. repeat split; simpl; apply Hlocal_robot_decision.
      * (* absurd case: the robot does not make the same choice *)
        match goal with | H : complement _ _ _ |- _ => elim H end.
        rewrite Hlocal_g. etransitivity; eauto. symmetry. apply Hlocal_robot_decision.
      * (* absurd case: the robot does not make the same choice *)
        match goal with | H : complement _ _ _ |- _ => elim H end.
        rewrite <- Hlocal_g. etransitivity; eauto. apply Hlocal_robot_decision.
      * (* invalid case: the robot does not choose an adjacent edge *)
        rewrite Hlocal_config, <- Hg. reflexivity. }
    (*  actual proof *)
    unfold lift, InfoG, InfoV. simpl projT1.
    change (proj1_sig (change_frame da (config_V2G (config_G2V config)) g)) with Diso.
    destruct Cnew_local_state as [v e proof | e p] eqn:Hg.
    - (* the robot ends up on a vertex *)
      simpl state_G2V. cbn -[equiv Dnew_local_state] in Hnew_local_state.
      destruct Hnew_local_state as [Hv He].
      simpl fst in Hv at 2. simpl snd in He at 2.
      repeat split.
      -- simpl fst. etransitivity; try apply HCiso'; [].
         rewrite Hv. cbn -[equiv].
         change (proj1_sig (change_frame da (config_V2G (config_G2V config)) g)) with Diso.
         f_equiv. symmetry. apply Hiso.
      -- simpl snd. etransitivity; try apply HCisoE; [].
         change (Bijection.retraction (iso_E Diso)) with (Bijection.section (iso_E (inverse Diso))).
         symmetry. etransitivity; try apply (iso_E_compat (inverse Ciso)), He; [].
         apply E_subrelation. f_equiv.
         apply Isomorphism.iso_E_compat. clear -Hiso. now apply inverse_compat.
      -- simpl snd. etransitivity; try apply HCisoE; [].
         change (Bijection.retraction (iso_E Diso)) with (Bijection.section (iso_E (inverse Diso))).
         symmetry. etransitivity; try apply (iso_E_compat (inverse Ciso)), He; [].
         apply E_subrelation. f_equiv.
         now apply Isomorphism.iso_E_compat, inverse_compat.
      -- unfold equiv. cbn -[equiv Dnew_local_state inverse].
         change (iso_E Diso ⁻¹) with (iso_E (Diso ⁻¹)).
         rewrite <- 2 iso_threshold.
         rewrite (proj2 (projT2 (precondition_satisfied_inv da config g))),
                 (proj2 (projT2 (precondition_satisfied_inv (da_C2D da config) (config_G2V config) g))).
         now rewrite He.
    - (* the robot ends up on an edge *)
      destruct Dnew_local_state as [[v' e'] Hvalid].
      unfold state_G2V in *. simpl liftG. cbn iota beta. simpl snd.
      assert (Htest : threshold
        (Bijection.section (iso_E (projT1 (precondition_satisfied_inv da config g))) e) = threshold e)
        by now rewrite <- iso_threshold, (proj2 (projT2 (precondition_satisfied_inv da config g))).
      Time destruct (Rle_dec (threshold e) p) as [Hle | Hlt].
      ++ destruct Hnew_local_state as [Hv He]. simpl fst in Hv. simpl snd in He.
         (* destruct takes too long... *)
         assert (threshold (Bijection.section (iso_E (projT1 (precondition_satisfied_inv da config g))) e)
                 <= proj_ratio (proj_strict_ratio p)) by now rewrite Htest.

         (* too slow, case is faster *)
         (* Time destruct_match; try contradiction; []. (* 230 sec!!!! *) *)
         Time match goal with
              | |- (match ?x with | _ => _ end) == _ => case x
              end.
         all:swap 1 2.
         { intros notH.
           apply (absurd _ H);assumption. }
         split; simpl fst; simpl snd.
         -- transitivity (tgt (Bijection.section (iso_E (inverse Ciso)) e)); [apply HCisoE |].
            rewrite Hv, <- (proj2 (iso_morphism _ e)). cbn -[equiv].
            f_equiv. symmetry. apply Hiso.
         -- change (Bijection.retraction (iso_E Diso) e')
              with (Bijection.section (iso_E (inverse Diso)) e').
            transitivity (Bijection.section (iso_E (inverse Ciso)) e); [apply HCisoE |].
            rewrite He. apply inverse_compat in Hiso.
            symmetry. apply E_subrelation, Hiso.
      ++ destruct Hnew_local_state as [Hv He]. simpl fst in Hv. simpl snd in He.
         assert (¬ threshold (Bijection.section (iso_E (projT1 (precondition_satisfied_inv da config g))) e)
                   <= proj_ratio (proj_strict_ratio p)) by now rewrite Htest.

         (* too slow, case is faster *)
         (* Time destruct_match; try contradiction; []. (* 230 sec!!!! *) *)
         Time match goal with
              | |- (match ?x with | _ => _ end) == _ => case x
              end.
         { intros notH.
           apply (absurd _ notH);assumption. }
         split; simpl fst; simpl snd.
         -- rewrite <- (proj1 (iso_morphism _ _)), Hv.
            transitivity (Bijection.section (iso_V (inverse Ciso)) (src e)); [apply HCiso' |].
            simpl. f_equiv. symmetry. apply Hiso.
         -- change (Bijection.retraction (iso_E Diso) e')
              with (Bijection.section (iso_E (inverse Diso)) e').
            transitivity (Bijection.section (iso_E (inverse Ciso)) e); [apply HCisoE |].
            rewrite He. apply inverse_compat in Hiso.
            symmetry. apply E_subrelation, Hiso.
  + (* id = Byz b *)
    cbn -[equiv]. unfold relocate_byz_C2D. f_equiv. symmetry. apply Hrelocate_byz.
* (* activate = false *)
  cbn -[equiv equiv_dec]. unfold move.
  destruct (config id) as [v e proof | e p].
  + (* the robot is on a vertex *)
    cbn -[equiv equiv_dec]. destruct_match.
    - (* the robot is at the edge src *)
      unfold add_edge, state_G2V.
      assert (He := threshold_pos e). rewrite Hchoose_inactive.
      change (proj_ratio ratio_0) with 0. rewrite Rplus_0_l at 2.
      destruct (Rle_bool (threshold e) (proj_ratio (choose_inactive da config id))) eqn:Htest;
      rewrite Rle_bool_true_iff in Htest || rewrite Rle_bool_false_iff in Htest;
      repeat destruct_match; try (now split; auto);
      simpl in * |-; try rewrite Rplus_0_l in *; contradiction || lra.
    - (* the robot is at the edge tgt *)
      unfold valid_stateV in proof. simpl in proof.
      destruct_match; now repeat split; simpl; intuition.
  + (* the robot is on an edge *)
    cbn -[equiv]. destruct_match; cbn -[equiv].
    - (* the robot is already past the edge threshold *)
      assert (He := threshold_pos e).
      assert (Hp := ratio_bounds (choose_inactive da config id)).
      transitivity (exist valid_stateV (tgt e, e) (or_intror (reflexivity (tgt e))));
      [| now repeat destruct_match].
      unfold state_G2V, add_edge.
      repeat destruct_match; reflexivity || (simpl in *; lra).
    - (* the robot is before the edge threshold *)
      unfold state_G2V, add_edge.
      assert (H0 : p + choose_inactive da config id =/= 0).
      { assert (Hpos := ratio_bounds (choose_inactive da config id)).
        assert (Hp := strict_ratio_bounds p).
        intro Habs. simpl in Habs. lra. }
      destruct_match; try contradiction; [].
      rewrite Hchoose_inactive.
      destruct (Rle_bool (threshold e) (p + choose_inactive da config id)) eqn:Hcase;
      rewrite Rle_bool_true_iff in Hcase || rewrite Rle_bool_false_iff in Hcase;
      repeat destruct_match; try solve [split; reflexivity | simpl in *; contradiction]; [].
      elim Hcase. transitivity 1; trivial; []. apply Rlt_le. apply threshold_pos.
Qed.

End GraphEquivalence.
