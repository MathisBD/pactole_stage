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
Require Import Omega.
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


Section GraphEquivalence.

Context (V E : Type).
Context {NN : Names}.
Context {G : Graph V E}.

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

Existing Instance InfoV3.
Existing Instance InfoG3.
(*
(** ** Translations of step actions of demonic actions **)

Definition choose_inactive_V2G {T} {inactive_choice T} f : configuration -> ident -> info :=
  fun config g => if f config id =?= config id then ratio_0 else ratio_1.

Instance inactive_update_V2G_compat : Proper (equiv ==> equiv) inactive_update_V2G.
Proof. intros [[|] | ?] [[|] | ?] Heq; try (destruct Heq; reflexivity); now simpl in *. Qed.

Definition actionC2D a rc :=
  match a with
    | CGF.Idle ref_change => DGF.Idle ref_change
    | CGF.Move dist =>
        match (CGF.Config.loc rc) with
          | CGF.OnVertex _ =>
            match (Graph.find_edge (DGF.Config.source (DGF.Config.robot_info (rcC2D rc)))
                             (DGF.Config.target (DGF.Config.robot_info (rcC2D rc)))) with
             | Some e =>
                if Rle_dec dist (Graph.threshold e) then DGF.Move false else DGF.Move true
             | None => DGF.Move false
            end
          | CGF.OnEdge e p => if Rle_dec (CGF.project_p p) (Graph.threshold e)
                              then if Rle_dec (dist + (CGF.project_p p)) (Graph.threshold e) 
                                   then DGF.Move false
                                   else DGF.Move true
                              else DGF.Move false
        end
  end.

Instance actionC2D_compat : Proper (CGF.Aom_eq ==> CGF.Config.eq_RobotConf ==> DGF.Aom_eq) actionC2D.
Proof.
intros [] [] Heq_action [loc1 [src1 tgt1]] [loc2 [src2 tgt2]] [Hloc [Hsrc Htgt]]; simpl in *; try tauto; [].
destruct loc1, loc2; simpl in *; try tauto.
+ (* OnVertex *)
  assert (Heq_e := Graph.find_edge_compat (LocC2D src1) (LocC2D src2) ltac:(now f_equiv)
                                          (LocC2D tgt1) (LocC2D tgt2) ltac:(now f_equiv)).
  destruct (Graph.find_edge (LocC2D src1) (LocC2D tgt1)) eqn:Heq1,
           (Graph.find_edge (LocC2D src2) (LocC2D tgt2)) eqn:Heq2;
  simpl in Heq_e; tauto || reflexivity || idtac; [].
  repeat destruct_match; rewrite Heq_e in *; subst; reflexivity || contradiction.
+ (* OnEdge *)
  destruct Hloc as [He Hp].
  repeat destruct_match; reflexivity || rewrite He in *; subst; contradiction.
Qed.
*)
(** ** Translations of demonic actions **)

Notation locV := (@location LocationV).
Notation locG := (@location LocationG).

Notation DGF_config := (@configuration _ locV3 InfoV3 NN).
Notation CGF_config := (@configuration _ locG3 InfoG3 NN).

Notation DGF_da :=
  (@demonic_action _ _ InfoV3 _ _ _ _ FrameChoiceIsomorphismV graph_update_bool graph_inactive_bool).
Notation CGF_da :=
  (@demonic_action _ _ InfoG3 _ _ _ _ FrameChoiceIsomorphismG graph_update_ratio graph_inactive_ratio).

Definition relocate_byz_D2C (rel_byz : DGF_config -> B -> locV3) : CGF_config -> B -> locG3.
(*   let '(pt, src, tgt) := (da.(relocate_byz) (config_G2V config) b) in (OnVertex pt, src, tgt) *)
refine (fun (config : CGF_config) (b : B) =>
  exist valid_stateG
    (OnVertex (fst (fst (proj1_sig (rel_byz (config_G2V config) b)))),
     snd (fst (proj1_sig (rel_byz (config_G2V config) b))),
     snd (proj1_sig (rel_byz (config_G2V config) b))) _).
Proof. abstract (destruct (rel_byz (config_G2V config) b) as [[[] ?] []]; simpl in *; tauto). Defined.

Instance relocate_byz_D2C_compat : Proper ((equiv ==> eq ==> equiv) ==> (equiv ==> eq ==> equiv)) relocate_byz_D2C.
Proof.
intros f g Hfg config1 config2 Hconfig bb b ?. subst bb.
simpl. repeat split; apply Hfg; now f_equiv.
Qed.

Definition relocate_byz_C2D (rel_byz : CGF_config -> B -> locG3) : DGF_config -> B -> locV3.
(*   let '(pt, src, tgt) := (da.(relocate_byz) (config_V2G config) b) in (location_G2V pt, src, tgt) *)
refine (fun (config : DGF_config) (b : B) =>
  exist valid_stateV
    (location_G2V (fst (fst (proj1_sig (rel_byz (config_V2G config) b)))),
     snd (fst (proj1_sig (rel_byz (config_V2G config) b))),
     snd (proj1_sig (rel_byz (config_V2G config) b))) _).
Proof.
abstract (destruct (rel_byz (config_V2G config) b) as [[[[] ?] ?] ?];
          simpl in *; trivial; []; hnf; destruct_match; simpl; auto).
Defined.

Instance relocate_byz_C2D_compat : Proper ((equiv ==> eq ==> equiv) ==> (equiv ==> eq ==> equiv)) relocate_byz_C2D.
Proof.
intros f g Hfg config1 config2 Hconfig bb b ?. subst bb.
simpl. repeat split; try apply location_G2V_compat; now apply Hfg; f_equiv.
Qed.

Definition da_D2C (da : DGF_da) : CGF_da.
refine {|
  activate := da.(activate);
  relocate_byz := relocate_byz_D2C da.(relocate_byz);
  change_frame := fun config g => da.(change_frame) (config_G2V config) g;
  choose_update := fun config g traj => if da.(choose_update) (config_G2V config) g (lift_path location_G2V traj)
                                        then ratio_1 else ratio_0;
  choose_inactive := fun config id => if da.(choose_inactive) (config_G2V config) id then ratio_1 else ratio_0 |}.
(*   CGF.step := fun id rcD =>
                if CGF.Config.eq_RobotConf_dec rcD (rcD2C (config id))
                then actionD2C ((DGF.step da) id (config id))
                else CGF.Move 0%R |}. *)
Proof.
+ (* precondition_satisfied *)
  intros config g. destruct (precondition_satisfied da (config_G2V config) g) as [_ Hpre].
  unfold precondition in *. simpl in *. split; trivial; [].
  intros [[[] src] tgt] _ Hpt; simpl in *.
  - destruct Hpt as [Heq | Heq]; rewrite Heq; left + right; reflexivity.
  - destruct Hpt as [Hsrc Htgt]; rewrite Hsrc, Htgt. apply iso_morphism.
+ intros config1 config2 Hconfig gg g ?. subst gg. now rewrite Hconfig.
+ intros config1 config2 Hconfig gg g ? traj1 traj2 Htraj. subst gg. now rewrite Hconfig, Htraj.
+ intros config1 config2 Hconfig id1 id2 Hid. simpl in Hid. subst. now rewrite Hconfig.
Defined.

Instance da_D2C_compat : Proper (equiv ==> equiv) da_D2C.
Proof.
intros da1 da2 Hda. split; [| split; [| split; [| split]]]; cbn -[equiv].
+ intro. now apply activate_da_compat.
+ intros. apply relocate_byz_D2C_compat; reflexivity || now apply relocate_byz_da_compat.
+ intros config g. apply (change_frame_da_compat Hda); auto.
+ intros id rc traj. erewrite (choose_update_da_compat Hda); auto.
+ intros config id. erewrite (choose_inactive_da_compat Hda); auto.
Qed.

Definition da_C2D (da : CGF_da) : DGF_da.
refine {|
  activate := da.(activate);
  relocate_byz := relocate_byz_C2D da.(relocate_byz);
  change_frame := fun config g => da.(change_frame) (config_V2G config) g;
  choose_update := fun config g traj =>
    let '(pt, src, tgt) := proj1_sig (config (Good g)) in
    if pt =?= tgt then false (* if we already are at our target, we don't need to move *)
                  else match @find_edge V E G pt tgt with
                         | Some e => Rle_bool (threshold e)
                                       (da.(choose_update) (config_V2G config) g (lift_path location_V2G traj))
                         | None => false
                       end;
  choose_inactive := fun config id =>
    let '(pt, src, tgt) := proj1_sig (config id) in
    if pt =?= tgt then false (* if we already are at our target, we don't need to move *)
                  else match @find_edge V E G pt tgt with
                         | Some e => Rle_bool (threshold e) (da.(choose_inactive) (config_V2G config) id)
                         | None => false
                       end |}.
Proof.
+ (* precondition_satisfied *)
  intros config g. destruct (precondition_satisfied da (config_V2G config) g) as [_ Hpre].
  unfold precondition in *. simpl in *. split; trivial; [].
  intros [[pt src] tgt] _ Hpt; hnf; simpl in *.
  destruct Hpt as [Heq | Heq]; rewrite Heq; left + right; reflexivity.
+ intros config1 config2 Hconfig gg g ?. subst gg. now rewrite Hconfig.
+ intros config1 config2 Hconfig gg g ? traj1 traj2 Htraj. subst gg.
  assert (Hpt := Hconfig (Good g)).
  destruct Hpt as [[Hpt Hsrc] Htgt],
           (proj1_sig (config1 (Good g))) as [[pt1 src1] tgt1],
           (proj1_sig (config2 (Good g))) as [[pt2 src2] tgt2].
  simpl in Hpt, Hsrc, Htgt.
  destruct (pt1 =?= tgt1), (pt2 =?= tgt2).
  - reflexivity.
  - revert_one @complement. intro Hgoal. elim Hgoal.
    etransitivity; [| etransitivity]; [symmetry | |]; eassumption.
  - revert_one @complement. intro Hgoal. elim Hgoal.
    etransitivity; [| etransitivity]; [| | symmetry]; eassumption.
  - generalize (find_edge_compat _ _ Hpt _ _ Htgt). do 2 destruct_match; try (simpl; tauto); [].
    intro Heq. simpl in Heq. now rewrite Heq, Hconfig, Htraj.
+ intros config1 config2 Hconfig id1 id2 Hid. simpl in Hid. subst.
  assert (Hpt := Hconfig id2).
  destruct Hpt as [[Hpt Hsrc] Htgt],
           (proj1_sig (config1 id2)) as [[pt1 src1] tgt1],
           (proj1_sig (config2 id2)) as [[pt2 src2] tgt2].
  simpl in Hpt, Hsrc, Htgt.
  destruct (pt1 =?= tgt1), (pt2 =?= tgt2).
  - reflexivity.
  - revert_one @complement. intro Hgoal. elim Hgoal.
    etransitivity; [| etransitivity]; [symmetry | |]; eassumption.
  - revert_one @complement. intro Hgoal. elim Hgoal.
    etransitivity; [| etransitivity]; [| | symmetry]; eassumption.
  - generalize (find_edge_compat _ _ Hpt _ _ Htgt). do 2 destruct_match; try (simpl; tauto); [].
    intro Heq. simpl in Heq. now rewrite Heq, Hconfig.
(* FIXME: why is there [EqDec V_Setoid] on the shelf? *)
Unshelve. all:autoclass.
Defined.

Instance da_C2D_compat : Proper (equiv ==> equiv) da_C2D.
Proof.
intros da1 da2 Hda. split; [| split; [| split; [| split]]]; cbn -[equiv].
+ intro. now apply activate_da_compat.
+ intros. apply relocate_byz_C2D_compat; reflexivity || now apply relocate_byz_da_compat.
+ intros config g. apply (change_frame_da_compat Hda); auto.
+ intros id rc traj. erewrite (choose_update_da_compat Hda); auto.
+ intros config id. erewrite (choose_inactive_da_compat Hda); auto.
Qed.

(** ** Final results: the translations commute with [round]. **)
(*
Lemma stepD2C : forall da config id,
  CGF.Aom_eq (CGF.step (daD2C da config) id (ConfigD2C config id))
             (actionD2C (DGF.step da id (config id))).
Proof.
intros da config id. simpl.
destruct_match_eq Heq.
+ reflexivity.
+ elim Heq. reflexivity.
Qed.

Lemma stepC2D : forall da config id,
  DGF.Aom_eq (DGF.step (daC2D da config) id (ConfigC2D config id))
             (actionC2D (CGF.step da id (config id)) (config id)).
Proof.
intros da config id. simpl.
destruct_match_eq Heq.
+ reflexivity.
+ elim Heq. reflexivity.
Qed.
*)

Context {Spect : @Spectrum _ _ InfoV3 _}.
Notation robogramV := (@robogram _ _ InfoV3 _ Spect).
Notation robogramG := (@robogram _ _ InfoG3 _ (spect_V2G Spect)).

Existing Instance graph_update_bool.
Existing Instance graph_update_ratio.
Existing Instance graph_inactive_bool.
Existing Instance graph_inactive_ratio.

Instance UpdFun_bool : @update_functions _ _ InfoV3 _ bool bool _ _.
simple refine {|
  update := fun config g traj (choice : bool) =>
    exist valid_stateV
      (if choice then traj ratio_1 else traj ratio_0, traj ratio_0, traj ratio_1) _;
  inactive := fun config id (choice : bool) =>
    exist valid_stateV
      (if choice then snd (proj1_sig (config id)) else fst (fst (proj1_sig (config id))),
       snd (fst (proj1_sig (config id))),
       snd (proj1_sig (config id))) _ |}.
Proof.
+ abstract (destruct choice; now left + right).
+ abstract (destruct (config id) as [[[pt src] tgt] Hprop], choice; simpl; (now right) || auto).
+ intros ? ? Hconfig ? ? ? ? ? Htraj ? ? Hchoice. simpl in Hchoice. subst.
  repeat split; simpl; try destruct_match; apply Htraj.
+ intros ? ? Hconfig ? ? ? ? ? Hchoice. simpl in Hchoice. subst.
  repeat split; simpl; try destruct_match; apply Hconfig.
Defined.

Definition add_edge (e : E) (ρ1 ρ2 : ratio) : loc.
refine (if (ρ1 + ρ2)%R =?= 0%R then OnVertex (src e) else
        if Rle_dec 1 (ρ1 + ρ2) then OnVertex (tgt e) else OnEdge e (exist _ (ρ1 + ρ2)%R _)).
Proof.
abstract (split; try solve [ apply Rle_neq_lt; (apply Rplus_le_le_0_compat; apply ratio_bounds) || (simpl in *; lra)
                           | now apply Rnot_le_lt ]).
Defined.

Instance add_edge_compat : Proper (equiv ==> equiv ==> equiv ==> equiv) add_edge.
Proof.
intros ? ? He ρ1 ρ1' Hρ1 ρ2 ρ2' Hρ2. unfold add_edge.
repeat destruct_match; solve [ rewrite Hρ1, Hρ2 in *; contradiction
                             | rewrite <- Hρ1, <- Hρ2 in *; contradiction
                             | rewrite He; reflexivity
                             | simpl; now rewrite He, Hρ1, Hρ2 ].
Qed.

Lemma add_edge_valid : forall e ρ1 ρ2, valid_stateG (add_edge e ρ1 ρ2, src e, tgt e).
Proof. intros. unfold add_edge. repeat destruct_match; now left + right + split. Qed.

(** Move a robot by a ratio ρ toward its current target. *)
Lemma move_proof : forall (state : locG3) ρ,
  let Hprop := proj2_sig state in
  let pt := fst (fst (proj1_sig state)) in
  let src := snd (fst (proj1_sig state)) in
  let tgt := snd (proj1_sig state) in
  valid_stateG
    (match find_edge src tgt with
     | Some e =>
         match pt with
         | OnVertex v => if src =?= v then add_edge e ratio_0 ρ else OnVertex tgt
         | OnEdge e0 p => add_edge e0 p ρ
         end
     | None => pt
     end, src, tgt).
Proof.
intros state ρ Hprop pt src tgt.
destruct_match_eq He; try destruct_match_eq Hcase; try destruct_match.
- eapply (eq_subrelation (R := equiv)) in He; autoclass; [].
  rewrite find_edge_Some in He.
  assert (Heq : (add_edge e ratio_0 ρ, src, tgt)
                 == (add_edge e ratio_0 ρ, Graph.src e, Graph.tgt e)) by now repeat split.
  rewrite Heq. apply add_edge_valid.
- now right.
- destruct state as [[[pt' src'] tgt'] Hprop']. simpl in * |-. subst pt src tgt Hprop pt'.
  assert (Heq : forall p, (add_edge e0 p ρ, src', tgt')
                          == (add_edge e0 p ρ, Graph.src e0, Graph.tgt e0)) by now repeat split.
  rewrite Heq. apply add_edge_valid.
- unfold pt, src, tgt. destruct state as [[[] ?] ?]. apply Hprop.
Qed.

Definition move (state : locG3) (ρ : ratio) : locG3 :=
(* BUG: [let '(exist _ (pt, src, tgt) Hprop) := state in ...] looses the link between Hprop and pt, src, tgt. *)
  let Hprop := proj2_sig state in
  let pt  := fst (fst (proj1_sig state)) in
  let src := snd (fst (proj1_sig state)) in
  let tgt := snd (proj1_sig state) in
  exist valid_stateG
    (match find_edge src tgt, pt with
       | None, _ => pt
       | _, OnEdge e p => add_edge e p ρ
       | Some e, OnVertex v =>
           if src =?= v then add_edge e ratio_0 ρ else OnVertex tgt
     end, src, tgt) (move_proof state ρ).

Instance move_compat : Proper (equiv ==> equiv ==> equiv) move.
Proof.
intros [[[] ?] ?] [[[] ?] ?] [[Hpt Hsrc] Htgt] ρ1 ρ2 Hρ.
unfold move. repeat split; cbn -[equiv] in *; trivial; [].
assert (He := find_edge_compat _ _ Hsrc _ _ Htgt).
repeat destruct_match; simpl in He; try tauto;
solve [ try destruct Hpt; apply add_edge_compat; auto; now f_equiv
      | exfalso; revert_one @complement; intro Hgoal; apply Hgoal;
        intuition; simpl in Hpt; rewrite Hpt, Hsrc in *; auto ].
Qed.

Instance UpdFun_ratio : @update_functions _ _ InfoG3 _ ratio ratio _ _.
simple refine {|
  update := fun (config : CGF_config) g traj ρ =>
    match traj ratio_0, traj ratio_1 with
      | OnVertex src, OnVertex tgt => 
          let target : locG3 := exist _ (OnVertex src, src, tgt) (or_introl (reflexivity _)) in
          move target ρ
      | _, _ => config (Good g)
    end;
  inactive := fun (config : CGF_config) id ρ => move (config id) ρ |}; autoclass.
Proof.
+ intros config1 config2 Hconfig gg g ? traj1 traj2 Htraj ρ1 ρ2 Hρ. subst gg.
  assert (Hsrc := Htraj ratio_0). assert (Htgt := Htraj ratio_1).
  destruct (traj1 ratio_0), (traj1 ratio_1), (traj2 ratio_0), (traj2 ratio_1);
  simpl in Hsrc, Htgt; try tauto || apply Hconfig; [].
  cbn zeta. f_equiv; now simpl.
+ intros config1 config2 Hconfig idid id ? ρ1 ρ2 Hρ.
  subst idid. now f_equiv.
Defined.

Theorem graph_equivD2C : forall (config : DGF_config) (rbg : robogramV) (da : DGF_da),
  config_V2G (round rbg da config) == round (rbg_V2G rbg) (da_D2C da) (config_V2G config).
Proof.
intros config rbg da id.
unfold config_V2G at 1. cbv beta delta [round].
simpl activate. destruct_match.
* (* activate = true *)
  destruct id as [g | b].
  + (* id = Good g *)
    assert (Hframe : change_frame (da_D2C da) (config_V2G config) g == change_frame da config g).
    { simpl change_frame. rewrite config_V2G2V. reflexivity. }
    cbv zeta.
    simpl (get_location
                 (map_config
                    (lift (Bijection.section (frame_choice_bijection (change_frame da config g)))
                       (precondition_satisfied da config g)) config (Good g))).
    simpl (get_location
              (map_config
                 (lift
                    (Bijection.section
                       (frame_choice_bijection (change_frame (da_D2C da) (config_V2G config) g)))
                    (precondition_satisfied (da_D2C da) (config_V2G config) g))
                 (config_V2G config) (Good g))).
    destruct (config (Good g)) as [[[pt src] tgt] Hprop]. simpl fst. unfold Datatypes.id.
    simpl.
  + (* id = Byz b *)
   (*  Time repeat split; simpl; unfold config_G2V; f_equiv; (* 190 s. *)
    apply (relocate_byz_compat da); trivial; intro; now rewrite state_V2G2V. *)
    admit. (* too long *)
* (* activate = false *)
  simpl choose_inactive at 2. rewrite config_V2G2V.
  change (@isomorphism locV E G) with (@isomorphism V E G). destruct_match_eq Hcase.
  + repeat split; try reflexivity; [].
    simpl. destruct_match_eq He.
    - unfold add_edge. simpl. repeat destruct_match; try reflexivity || (simpl in *; lra); [].
      apply (eq_subrelation (R := equiv)) in He; autoclass; [].
      now rewrite find_edge_Some in He.
    - (* wrong but should be impossible: there should be an edge between src and tgt *) admit.
  + repeat split; try reflexivity; [].
    simpl. destruct_match_eq He; try destruct_match.
    - unfold add_edge. simpl. destruct_match; try (simpl in *; exfalso; lra); [].
      apply (eq_subrelation (R := equiv)) in He; autoclass; [].
      rewrite find_edge_Some in He. now rewrite <- (proj1 He).
    - destruct (proj2_sig (config id)); intuition.
    - reflexivity.
Admitted.

Theorem graph_equiv_C2D : forall (config : CGF_config) (rbg : robogramG) (da : CGF_da),
  config_G2V (round rbg da config) == round (rbg_G2V rbg) (da_C2D da) (config_G2V config).
Proof.
intros config rbg da id.
unfold config_G2V at 1. unfold round. simpl activate. destruct_match.
* (* activate = true *)
  admit.
* (* activate = false *)
  repeat split; try reflexivity; [].
  simpl (choose_inactive (da_C2D da) (config_G2V config) id).
  destruct_match; try destruct_match_eq He.
  + 
  + 
  + 
  simpl (choose_inactive da config id).
Qed.

End GraphEquivalence.
