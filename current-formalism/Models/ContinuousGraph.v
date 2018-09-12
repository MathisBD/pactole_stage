(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import Reals.
Require Import Omega.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.Graph.
Require Import Pactole.Spaces.Isomorphism.
Require Import Pactole.Models.Flexible.


Notation "x == y" := (equiv x y).
Typeclasses eauto := (bfs).
Remove Hints eq_setoid : typeclass_instances.

Section CGF.

Context {V E : Type}.
Context `{Names}.
Context {G : Graph V E}.

Instance LocationV : Location := { location := V }.

(* Robots can be either on a location or on an edge. *)
Inductive loc :=
  | OnVertex (l : location)
  | OnEdge (e : E) (p : strict_ratio).

Global Instance locG_Setoid : Setoid loc := {
  equiv := fun l l'=>
             match l, l' with
               | OnVertex l, OnVertex l' => l == l'
               | OnEdge e p, OnEdge e' p' => e == e' /\ p == p'
               | _, _ => False
             end}.
Proof. split.
+ now intros [].
+ intros [] [] Heq; simpl in *; try (destruct Heq; split); now symmetry.
+ intros [] [] [] Heq1 Heq2; simpl in *;
  try destruct Heq1; try destruct Heq2; try split; etransitivity; eauto.
Defined.

Global Instance locG_EqDec: EqDec locG_Setoid.
Proof.
  intros [l1 | e1 p1] [l2 | e2 p2]; simpl.
+ apply equiv_dec.
+ intuition.
+ intuition.
+ destruct (e1 =?= e2); [destruct (p1 =?= p2) |]; intuition.
Qed.

Instance LocationG : Location := { location := loc }.

Notation locV := (@location LocationV).
Notation locG := (@location LocationG).

Global Instance OnVertex_compat : Proper (equiv ==> equiv) OnVertex.
Proof. repeat intro. auto. Qed.

Global Instance OnEdge_compat : Proper (equiv ==> equiv ==> equiv) OnEdge.
Proof. repeat intro. auto. Qed.


(** *  Projection functions  **)

(** ** On space *)
(** a robot can be on a node (Loc) or on an edge (Mvt) *)

Definition location_G2V (loc : locG) : locV :=
  match loc with
    | OnVertex l => l
    | OnEdge e p => if Rle_dec p (threshold e) then Graph.src e else Graph.tgt e
  end.

Global Instance location_G2V_compat : Proper (equiv ==> equiv) location_G2V.
Proof.
unfold location_G2V. intros [l1 | e1 p1] [l2 | e2 p2] Hxy; try tauto; [].
destruct Hxy as [Hexy Hpxy],
         (Rle_dec p1 (threshold e1)) eqn:Hx,
         (Rle_dec p2 (threshold e2)) eqn:Hy.
+ now apply Graph.src_compat.
+ assert (Ht := Graph.threshold_compat e1 e2 Hexy).
  assert (Hr : (p1 <= Graph.threshold e1)%R) by assumption.
  now rewrite Ht, Hpxy in Hr.
+ assert (Hr : (p2 <= Graph.threshold e2)%R) by assumption.
  assert (Ht := Graph.threshold_compat e1 e2 Hexy).
  now rewrite <- Ht, <- Hpxy in Hr.
+ now apply Graph.tgt_compat.
Qed.

Definition location_V2G : locV -> locG := OnVertex.

Global Instance location_V2G_compat : Proper (equiv ==> equiv) location_V2G.
Proof. repeat intro. now simpl. Qed.

(** ** Translation of states **)

Notation locV3 := (locV * locV * locV)%type.
(* source and target are still in locV but the location is now in locG *)
Notation locG3 := (locG * locV * locV)%type.

Definition rc_V2G (state : locV3) : locG3 :=
  (OnVertex (fst (fst state)), snd (fst state), snd state).

Global Instance rc_V2G_compat : Proper (equiv ==> equiv) rc_V2G.
Proof. intros ? ? HrcA. unfold rc_V2G. repeat try (split; simpl); apply HrcA. Qed.

Definition rc_G2V (state : locG3) : locV3 :=
  (location_G2V (fst (fst state)), snd (fst state), snd state).

Global Instance rc_G2V_compat : Proper (equiv ==> equiv) rc_G2V.
Proof. intros ? ? HrcV. unfold rc_G2V. repeat try (split; simpl); f_equiv; apply HrcV. Qed.

Lemma rc_V2G2V : forall state, rc_G2V (rc_V2G state) == state.
Proof. intro. simpl. repeat (split; try reflexivity). Qed.

(** ** On configurations *)

(* Instance Info : State location := OnlyLocation. *)
Instance InfoV3 : @State locV3 LocationV := AddLocation _ (AddLocation _ OnlyLocation).
Instance InfoG3 : @State locG3 LocationG.
refine {|
  get_location := fun st => fst (fst st);
  lift := fun f st => (f (fst (fst st)),
                       location_G2V (f (location_V2G (snd (fst st)))),
                       location_G2V (f (location_V2G (snd st))));
  lift_id := fun st => let '(loc, src, tgt) := st in ltac:(reflexivity) |}.
Proof.
+ (* get_location_lift *)
  intros. cbn [fst snd]. reflexivity.
+ (* get_location_compat *)
  now intros ? ? [[] ?].
+ (* lift_compat *)
  intros f g Hfg st1 st2 Hst. repeat split; cbn [fst snd];
  repeat (f_equiv; try eassumption); apply Hst.
Defined.

Notation configV := (@configuration locV3 _ _ _).
Notation configG := (@configuration locG3 _ _ _).

(* RMK: we cannot use map_config as the Location instance is not the same. *)
Definition config_V2G (config : configV) : configG := fun id => rc_V2G (config id).

Global Instance config_V2G_compat : Proper (equiv ==> equiv) config_V2G.
Proof. intros ? ? Hca id. unfold config_V2G. f_equiv. apply Hca. Qed.

Definition config_G2V (config : configG) : configV := fun id => rc_G2V (config id).

Global Instance config_G2V_compat : Proper (equiv ==> equiv) config_G2V.
Proof. intros ? ? Hcd id. unfold config_G2V. f_equiv. apply Hcd. Qed.

Lemma config_V2G2V : forall config : configV, config_G2V (config_V2G config) == config.
Proof. intros. unfold config_G2V, config_V2G. now repeat try (split; simpl). Qed.

(* Fixing source and target should already be done by the other model.
Definition config_G2V (config : configG) : configV :=
  fun id => let '(loc, src, tgt) := (config id) in
            match loc with
              | OnVertex pt => (pt, pt, tgt)
              | OnEdge e p as x => (location_G2V x, src, tgt)
            end.

Global Instance config_G2V_compat : Proper (equiv ==> equiv) config_G2V.
Proof.
intros c1 c2 Hc id. destruct (Hc id) as [[Hloc Hsrc] Htgt]. unfold config_G2V.
repeat destruct_match; cbn -[equiv] in *; try tauto; [|].
+ repeat split; simpl; auto.
+ destruct Hloc as [He Hp]. repeat split; simpl; trivial; [].
  repeat destruct_match; simpl; apply src_compat || apply tgt_compat || exfalso; trivial;
  subst; apply threshold_compat in He; auto; rewrite He, Hp in *; contradiction.
Qed.
*)
(** The spectrum for continuous setting is almost the same as for the discrete one:
    we simply project robots on edges either to the source or target of the edge
    depending on where they are located compared to the threshold of the edge;
    and add the current location. *)

Global Instance spect_V2G (Spect : @Spectrum _ _ InfoV3 _) : @Spectrum _ _ InfoG3 _ := {
  spectrum := @spectrum _ _ _ _ Spect;
  spect_from_config := fun config pt => spect_from_config (config_G2V config) (location_G2V pt);
  spect_is_ok s config pt := spect_is_ok s (config_G2V config) (location_G2V pt) }.
Proof.
+ abstract (now repeat intro; repeat f_equiv).
+ repeat intro. apply spect_from_config_spec.
Defined.

(** Robograms can only move to adjacent locations. *)

Class robogram_range `{@Spectrum _ LocationV _ _} r := {
  pgm_range : forall spect pt, Graph.find_edge pt (location_G2V (pgm r spect ratio_1)) =/= None }.

(** ** Translation of robograms **)

Context {Spect : @Spectrum _ _ InfoV3 _}.
Notation robogramV := (@robogram _ _ InfoV3 _ Spect).
Notation robogramG := (@robogram _ _ InfoG3 _ (spect_V2G Spect)).

Definition rbg_V2G (rbgV : robogramV) : robogramG.
refine (@Build_robogram _ _ InfoG3 _ (spect_V2G Spect)
         (fun s => lift_path location_V2G (rbgV s)) _).
Proof.
intros s1 s2 Hs r. unfold lift_path. cbn -[equiv].
apply location_V2G_compat. now rewrite Hs.
Unshelve. apply location_V2G_compat.
Defined.

Global Instance rbg_V2G_compat : Proper (equiv ==> equiv) rbg_V2G.
Proof. intros ra1 ra2 Hra. simpl. apply Hra. Qed.

Definition rbg_G2V (rbgG : robogramG) : robogramV.
refine (@Build_robogram _ _ InfoV3 _ Spect
         (fun s => lift_path location_G2V (rbgG s)) _).
Proof.
intros s1 s2 Hs r. unfold lift_path. cbn -[equiv].
apply location_G2V_compat. now rewrite Hs.
Unshelve. apply location_G2V_compat.
Defined.

Global Instance rbg_G2V_compat : Proper (equiv ==> equiv) rbg_G2V.
Proof. intros ra1 ra2 Hra s r. simpl. apply location_G2V_compat, Hra. Qed.

Lemma rbg_V2G2V : forall rbgV, rbg_G2V (rbg_V2G rbgV) == rbgV.
Proof. intro. simpl. reflexivity. Qed.

(** **  Demonic schedulers  **)

(** Graph isomorphisms as a frame choice *)
Global Instance FrameChoiceIsomorphismV : @frame_choice LocationV (@isomorphism locV E G) := {|
  frame_choice_bijection := @iso_V locV E G;
  frame_choice_Setoid := @isomorphism_Setoid locV E G;
  frame_choice_bijection_compat := @iso_V_compat locV E G |}.

(** Using the isomorphism to build a bijection continuous graphs. *)

Definition bijectionG (iso : isomorphism G) : Bijection.bijection loc.
simple refine {| Bijection.section := fun pt => match pt with
          | OnVertex v => OnVertex (iso.(iso_V) v)
          | OnEdge e p => OnEdge (iso.(iso_E) e) p
        end;
  Bijection.retraction := fun pt => match pt with
          | OnVertex v => OnVertex (Bijection.retraction iso.(iso_V) v)
          | OnEdge e p => OnEdge (Bijection.retraction iso.(iso_E) e) p
        end |}.
Proof.
+ intros [] [] Heq; simpl in Heq; trivial; now repeat f_equiv.
+ intros [] []; simpl in *; try tauto; [|]; split; intro Heq.
  - rewrite <- Heq. apply Bijection.retraction_section.
  - rewrite <- Heq. apply Bijection.section_retraction.
  - destruct Heq as [Heq1 Heq2]. rewrite Heq2, Heq1 || rewrite Heq2, <- Heq1.
    split; trivial; []. apply Bijection.retraction_section.
  - destruct Heq as [Heq1 Heq2]. rewrite Heq2, Heq1 || rewrite Heq2, <- Heq1.
    split; trivial; []. apply Bijection.section_retraction.
Defined.

Global Instance bijectionG_compat :  Proper (equiv ==> equiv) bijectionG.
Proof.
intros iso1 iso2 Hiso []; simpl.
+ apply Hiso.
+ split; trivial; []. apply Hiso.
Qed.

Global Instance FrameChoiceIsomorphismG : @frame_choice LocationG (@isomorphism locV E G) := {|
  frame_choice_bijection := bijectionG |}.

(** The update only contains the movement ratio. *)
Instance graph_update_bool : update_choice bool := { update_choice_EqDec := bool_eqdec }.
Instance graph_update_ratio : update_choice ratio := Flexible.OnlyFlexible.
(* TODO: Ensure that the following invariant holds:
         if activate is true, then the current location, the source and target are all the same. *)

Instance graph_inactive_bool : inactive_choice bool := { inactive_choice_EqDec := bool_eqdec }.
Instance graph_inactive_ratio : inactive_choice ratio := { inactive_choice_EqDec := ratio_EqDec }.

(*
(** [round r da conf] return the new configuration of robots (that is a function
    giving the configuration of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)

(** * recursive property *)

(** ** starting point 

we define an initial configuration where all robot are on nodes,
and their informations [source] and [target] are on the same node. *) 
Definition Conf_init (conf: Config.t) : Prop := forall id, exists l l' e,
      Graph.find_edge l l' = Some e /\
      Config.eq_RobotConf (conf id)
                          {| Config.loc := Loc l;
                             Config.state := {| Info.source := Loc l; Info.target := Loc l'|} |}.


Lemma round_flow : forall rbg da g conf e p,
    loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) -> 
    (exists l, loc_eq (Config.loc (conf (Good g))) (Loc l)) \/
    (exists p', (project_p p' <= project_p p)%R /\
                loc_eq (Config.loc (conf (Good g))) (Mvt e p')).
Proof.
  intros rbg da g conf e p Hl.
  unfold round in *.
  destruct (step da (Good g) (conf (Good g))) eqn : Hstep.
  simpl in *.
  destruct (Config.loc (conf (Good g))).
  left; (now exists l).
  destruct (Rle_dec 1 (project_p p0 + dist)); simpl in *; try now exfalso.
  destruct (Rdec dist 0). right. exists p0. unfold loc_eq in Hl; destruct Hl.
  repeat split. now rewrite H0. auto. right. exists p0.
  unfold loc_eq in *. destruct Hl.
  repeat split.
  assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Moving dist))
    by now rewrite Hstep.
  rewrite <- H0, <- inv_pro;
    assert (Hf:=step_flexibility da (Good g) (conf (Good g)) dist Hstep').
  lra.
  assert (Hp := project_p_image p0). lra. auto.
  destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                (Config.loc (Config.map (apply_sim sim) conf (Good g))))
  eqn : Hrbg.
  destruct (Location.eq_dec (Loc ((Iso.sim_V (sim ⁻¹)) l))
              (Config.loc (conf (Good g)))).
  simpl in *. right. exists p. now split.
  simpl in *. right. exists p. now split.
  destruct (Location.eq_dec (Loc (Graph.src e0)) (Config.loc (conf (Good g)))).
  simpl in *. right. exists p. now split.
  simpl in *. right. exists p. now split.
Qed.

(** ** if [source] and [target] are on some node, they're still on nodes after a [round] *)

(** defintion of probleme *)
Definition ri_loc_def (conf: Config.t) : Prop := forall g,
    exists v1 v2,
      loc_eq (Info.source (Config.state (conf (Good g)))) (Loc v1) /\
      loc_eq (Info.target (Config.state (conf (Good g)))) (Loc v2).


(** it's true starting from the initial configuration *)
Lemma ri_loc_init : forall conf da rbg,
    Conf_init conf ->
    ri_loc_def (round rbg da conf).
Proof.
  intros conf da rbg Hinit g.
  unfold Conf_init in Hinit.
  specialize (Hinit (Good g)).
  destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
  unfold round.
  destruct (step da (Good g) (conf (Good g)))
           eqn: Hstep,
                (Config.loc (conf (Good g)))
                  eqn : Hloc,
                        (Info.target (Config.state (conf (Good g))))
                          eqn : Htgt;
    try (destruct (Graph.Veq_dec l1 l0));
    try now simpl in *.
  + exists l, l'; now rewrite Htgt; split.
  + destruct (Rdec dist 0). exists l, l'; now rewrite Htgt; split.
    destruct (Rdec dist 1). simpl in *. exists l, l'; now rewrite Htgt; split.
    unfold loc_eq in Hti, Hli.
    exists l, l1.
    split; simpl.
    assumption.
    now rewrite Htgt.
  + simpl.
    rewrite Hloc in *.
    destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l0))) eqn : Hr.
    destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l2)) (Loc l0)).
    exists l, l'.
    now rewrite Htgt; split.
    simpl.
    exists l0, (Bijection.retraction (Iso.sim_V sim) l2).
    now split.
    generalize (pgm_range rbg (Spect.from_config
                                 (Config.map (apply_sim sim) conf))
                          (Loc ((Iso.sim_V sim) l0))
                           ((Iso.sim_V sim) l0) (reflexivity _)).
    intros Hrange.
    destruct Hrange as (lr, (er, (Hlr, Her))).
    simpl in *.
    rewrite Hr in Hlr.
    discriminate.
  + simpl.
    rewrite Hloc in *.
    destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l0))) eqn : Hr.
    destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l2)) (Loc l0)).
    exists l, l'.
    now rewrite Htgt; split.
    simpl.
    exists l0, (Bijection.retraction (Iso.sim_V sim) l2).
    now split.
    generalize (pgm_range rbg (Spect.from_config
                                 (Config.map (apply_sim sim) conf))
                          (Loc ((Iso.sim_V sim) l0))
                           ((Iso.sim_V sim) l0) (reflexivity _)).
    intros Hrange.
    destruct Hrange as (lr, (er, (Hlr, Her))).
    rewrite Hr in Hlr.
    discriminate.
Qed.


(** recurrence's hypothesis*)
Lemma ri_loc_always : forall conf da rbg,
    ri_loc_def conf ->
    ri_loc_def (round rbg da conf).
Proof.
  intros conf da rbg Hs' g.
  unfold ri_loc_def in *.
  destruct (Hs' g) as (v1, (v2, (Hs, Hg))).
  unfold round.
  simpl in *.
  destruct (step da (Good g) (conf (Good g)))
           eqn : Hstep,
                 (Config.loc (conf (Good g)))
                   eqn : Hloc,
                         (Info.target (Config.state (conf (Good g))))
                           eqn : Htgt;
    try easy;
    try (destruct (Graph.Veq_dec l0 l)).
  exists v1, v2; now rewrite Htgt; split.
  destruct (Rdec dist 0). exists v1, v2. now rewrite Htgt; split.
  destruct (Rdec dist 1). simpl. exists v1, v2; now rewrite Htgt; split.
  exists v1, v2. simpl. now rewrite Htgt; split.
  destruct (Rle_dec 1 (project_p p + dist)); 
    try (simpl; exists v1, v2; now rewrite Htgt; split).
  destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l))).
  destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l1)) (Loc l)).
  exists v1, v2; now rewrite Htgt; split.
  simpl. exists l, (Bijection.retraction (Iso.sim_V sim) l1); now split.
  destruct (Location.eq_dec (Loc (Graph.src e)) (Loc l)).
  exists v1, v2; now rewrite Htgt; split.
  simpl in *. exists l, (Graph.src e); now split.
  destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l))).
  destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l1)) (Loc l)).
  exists v1, v2; now rewrite Htgt; split.
  simpl. exists l, (Bijection.retraction (Iso.sim_V sim) l1); now split.
  destruct (Location.eq_dec (Loc (Graph.src e)) (Loc l)).
  exists v1, v2; now rewrite Htgt; split.
  simpl in *. exists l, (Graph.src e); now split.
  assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Active sim))
    by now rewrite Hstep.
  assert (Hfalse := step_delta da g (conf (Good g)) sim Hstep').
  destruct Hfalse as ((l',Hfalse), _). rewrite Hloc in Hfalse. now exfalso.
Qed.


CoInductive ri : execution -> Prop :=
  PropCons : forall e, ri_loc_def (Stream.hd e) -> ri (Stream.tl e) -> ri e.

Lemma ri_round : forall r da config, ri_loc_def config -> ri_loc_def (round r da config).
Proof.
  intros r da config Hinit g.
  destruct (Hinit g) as (v1, (v2, (Hs, Ht))).
  assert (Hfin := @ri_loc_always config da r).
  now apply Hfin.
Qed.

(** final proof *)
Lemma ri_always : forall r d config, ri_loc_def config -> ri (execute r d config).
Proof.
  cofix Hrec.
  intros d config r Hinit.
  constructor.
  + unfold execute. simpl. assumption.
  + rewrite execute_tail. simpl. apply Hrec. apply ri_round. assumption.
Qed.

Corollary ri_always_bis : forall r d config, Conf_init config -> ri (execute r d config).
Proof. intros. apply ri_always. unfold Conf_init, ri_loc_def in *. firstorder. Qed.

(** ** starting from a good configuration, we stay in a good configuration *)

(** a good conf is :
  - [source] and [target] are on node.
  - if a robot is on a node, it's on its [target] or [source].
  - if a robot is on an edge, it's the edge between its [source] and [target].
  - there is a edge between [source] and [target]. *)
Definition group_good_def (conf: Config.t) : Prop := forall g,(
      ri_loc_def conf /\
      (forall v0, loc_eq (Config.loc (conf (Good g))) (Loc v0) -> 
                  loc_eq (Info.source (Config.state (conf (Good g)))) (Loc v0) \/
                  loc_eq (Info.target (Config.state (conf (Good g)))) (Loc v0)) /\
      (forall v1 v2 e p,
          loc_eq (Info.source (Config.state (conf (Good g)))) (Loc v1) ->
          loc_eq (Info.target (Config.state (conf (Good g)))) (Loc v2) ->
          loc_eq (Config.loc (conf (Good g))) (Mvt e p) ->
          opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)) /\
      (forall v1 v2,
          loc_eq (Info.source (Config.state (conf (Good g)))) (Loc v1) ->
          loc_eq (Info.target (Config.state (conf (Good g)))) (Loc v2) ->
          exists e, (opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)))

     (* 


changer le cas 2 en (loc conf) = mvt e p -> (src conf) = Loc (src e) /\ (tgt conf) = Loc (tgt e))





/\
       loc = tgt ->
step = move ->
loc round = mvt e ->
find_edge loc tgt = e
      forall conf', (forall r da,
           Config.eq conf (round r da conf')) -> 
          (forall da, exists dist,
              step da (Good g) (conf' (Good g)) = Moving dist /\
          dist <> 0%R /\ dist <> 1%R)
          ->
          (exists l, Location.eq (Config.loc (conf' (Good g))) (Loc l))
          ->
          Location.eq (Info.source (Config.state (conf' (Good g))))
                      (Info.target (Config.state (conf' (Good g))))
          ->
          (exists e ll lt,
              Location.eq (Config.loc (conf' (Good g))) (Loc ll)
              /\
              Location.eq (Info.target (Config.state
                                            (conf' (Good g)))) (Loc lt)
              /\
              opt_eq Graph.Eeq
                     (Graph.find_edge ll lt)
                     (Some e))
          -> Location.eq (Config.loc (conf' (Good g)))
                         (Info.source (Config.state (conf' (Good g))))*)).


Axiom AutoLoop : forall l, exists e, (Graph.find_edge l l) = Some e.

(** initialisation *)
Lemma group_lem_init : forall conf (rbg : robogram) da,
    Conf_init conf -> (group_good_def (round rbg da conf)).
Proof.
  intros conf rbg da (*v0' v1' v2' e' p'*) Hinit g.
  split.
  - now apply ri_loc_init.
  - unfold Conf_init in Hinit.
    specialize (Hinit (Good g)).
    destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
    split;
      destruct (step da (Good g) (conf (Good g)))
               eqn: Hstep,
                    (Config.loc (conf (Good g)))
                      eqn : Hloc,
                            (Info.target (Config.state (conf (Good g))))
                              eqn : Htgt;
      try now unfold round in *; simpl in *.
    intro v0.
    intros Hl0.
    unfold round in *.
    + rewrite <- Hl in *.
      simpl in *.
      rewrite Hstep, Hloc, Htgt in *.
      destruct (Graph.Veq_dec l1 l0).
      rewrite Hloc in Hl0. rewrite <- Hl0.
      now left.
      destruct (Rdec dist 0). rewrite Hloc in Hl0. rewrite <- Hl0. now left.
      destruct (Rdec dist 1).
      simpl in *.
      now rewrite Htgt; right.
      destruct (Info.target (Config.state (conf (Good g)))) eqn : Ht;
        try now simpl in *.
    + unfold round.
      rewrite Hstep in *.
      simpl in *. left.
      rewrite Hloc in *.
      destruct (Location.eq_dec
             (Loc
                match
                  rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l0))
                with
                | Loc l => Bijection.retraction (Iso.sim_V sim) l
                | Mvt e _ => Graph.src e
                end) (Loc l0)).
      rewrite Hsi, Hloc, <- H in *.
      simpl.
      now symmetry.
      now simpl in *.
    + split.
      * unfold round in *.
        rewrite Hstep, Hloc, Htgt in *.
        intros v1 v2 e0 p Hs' Ht' Hl'.
        destruct (Graph.Veq_dec l1 l0). now rewrite Hloc in Hl'.
        destruct (Rdec dist 0). rewrite Hloc in Hl'; now simpl in *.
        destruct (Rdec dist 1). now simpl in *.
        unfold loc_eq in Hti, Hl.
        simpl in *.
        assert (opt_eq Graph.Eeq (Graph.find_edge l0 l1) (Graph.find_edge l l'))
          by now apply Graph.find_edge_compat.
        rewrite Hli in H.
        destruct (Graph.find_edge l0 l1); try contradiction.
        destruct Hl' as (He,_).
        simpl in *.
        rewrite He in H.
        rewrite Htgt, Hsi in *.
        simpl in *.
        assert (opt_eq Graph.Eeq (Some e) (Some e0)) by now simpl in *.
        rewrite <- H0, <- Hli.
        apply Graph.find_edge_compat; try now symmetry. now rewrite <- Ht'.
      * unfold round in *; rewrite Hstep, Hloc, Htgt in *.
        intros v1 v2 Hv1 Hv2.
        destruct (Graph.Veq_dec l1 l0).
        rewrite Htgt, Hv1, Hv2 in *.
        unfold loc_eq in Hsi, Hti.
        exists e.
        rewrite <- Hli.
        now apply Graph.find_edge_compat.
        destruct (Rdec dist 0).
        rewrite Htgt, Hv1, Hv2 in *.
        unfold loc_eq in Hsi, Hti.
        exists e.
        rewrite <- Hli.
        now apply Graph.find_edge_compat.
        destruct (Rdec dist 1). simpl in *.
        rewrite Htgt, Hv1 in *.
        simpl in *.
        rewrite Hv2 in *.
        exists e.
        rewrite <- Hli.
        now apply Graph.find_edge_compat.
        simpl in *.
        rewrite Htgt, Hv1 in *.
        simpl in *;
          rewrite Hv2 in *.
        unfold loc_eq in Hsi, Hti.
        exists e.
        rewrite <- Hli.
        now apply Graph.find_edge_compat.
    + unfold round.
      rewrite Hstep.
      simpl.
      rewrite Hloc.
      destruct (Location.eq_dec
              (Loc
                 match
                   rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                     (Loc ((Iso.sim_V sim) l0))
                 with
                 | Loc l1 => Bijection.retraction (Iso.sim_V sim) l1
                 | Mvt e1 _ => Graph.src e1
                 end) (Loc l0)).
      split; try now simpl in *.
      intros.
      now rewrite Hloc in *.
      intros v1 v2 Hv1 Hv2.
      rewrite Htgt, Hsi, Hti in *.
      simpl in *.
      exists e.
      rewrite <- Hli.
      now apply Graph.find_edge_compat.
      split.
      now intros.
      intros v1 v2 Hv1 Hv2.
      assert (Hrange :=
                pgm_range rbg (Spect.from_config
                                 (Config.map (apply_sim sim) conf))
                          (Config.loc
                             (Config.map (apply_sim sim) conf (Good g)))
                          ((Iso.sim_V sim) l0)).
      destruct Hrange as (lrange, (erange, (Hlrange, Herange)));
      simpl in *;
      try (now rewrite Hloc).
      simpl in *.
      rewrite Hloc in *.
      rewrite Hlrange in Hv2.
      exists (Bijection.retraction (Iso.sim_E sim) erange).
      rewrite Graph.find_edge_Some in *.
      destruct (Iso.sim_morphism sim (((Bijection.retraction (Iso.sim_E sim)) erange))) as [Hms Hmt].
      destruct Herange as [HSs HSt].
      rewrite Bijection.Inversion in *.
      rewrite Bijection.section_retraction in *; autoclass; [].
      split.
      * now rewrite <- Hv1, <- HSs, Hms.
      * now rewrite <- Hv2, <- Hmt, HSt.
Qed.

(** recurrence *)
Lemma group_lem : forall conf (rbg : robogram) da,
    group_good_def conf ->
    ri_loc_def (round rbg da conf) /\
    group_good_def (round rbg da conf).
Proof.
  intros conf rbg da Hgroup.
  (* A dummy robot to get the first component of group_good_def *)
  assert (Hinit' : ri_loc_def (round rbg da conf)).
  { intro g. destruct (Hgroup g) as [Hgg _]. now apply ri_round. }
  split; trivial; []. intro g.
  destruct (Hgroup g) as (Hinit, (Hli, (Hmi, Hex_e))).
  repeat split; trivial; clear Hinit'; [| |].
  + intros v0' H. unfold round in *.
    destruct (Hinit g) as (_, (lt' ,(_,Ht')));
    destruct (step da (Good g) (conf (Good g)))
             eqn: Hstep,
                  (Config.loc (conf (Good g)))
                    eqn : Hl,
                          (Info.target (Config.state (conf (Good g))))
                            eqn : Htgt;
    try easy.
  - destruct (Graph.Veq_dec l0 l).
    specialize (Hli v0'). rewrite Htgt in *. apply Hli. now rewrite Hl in H.
    destruct (Rdec dist 0). 
    specialize (Hli v0'). rewrite Htgt in *. apply Hli. now rewrite Hl in H.
    destruct (Rdec dist 1).
    simpl in *. now rewrite Htgt in *; right.
    now simpl in *.
  - destruct (Rle_dec 1 (project_p p + dist)); simpl in *.
    * destruct (Hinit g) as (v1, (v2, Hri)). specialize (Hmi v1 v2 e p).
      rewrite Graph.find_edge_Some in Hmi.
      destruct Hri as [Hsri Htri].
      assert (Hproof : Graph.Veq (Graph.tgt e) v2).
      { symmetry. apply Hmi; try easy; []. now rewrite Htgt in Htri. }
        right.
        rewrite Htri. simpl in *. now rewrite <- Hproof.
    * destruct (Rdec dist 0); now simpl in .
  - destruct (Location.eq_dec
                (Loc
                   match
                     rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                         (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                   with
                   | Loc l0 => (Iso.sim_V (sim ⁻¹)) l0
                   | Mvt e _ => Graph.src e
                   end) (Loc l)). simpl in *.
    destruct (Hgroup g) as (_, (Hl_ri,_)).
    now destruct (Hl_ri v0'); auto.
    now left.
  - destruct (Location.eq_dec
             (Loc
                match
                  rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                with
                | Loc l => (Iso.sim_V (sim ⁻¹)) l
                | Mvt e0 _ => Graph.src e0
                end) (Mvt e p)); now simpl in *.
  + intros v1' v2' e' p' Hs0 Ht0 Hl0. unfold round in *.
    destruct (Hinit g) as (_, (lt' ,(_,Ht')));
    destruct (step da (Good g) (conf (Good g)))
             eqn: Hstep,
                  (Config.loc (conf (Good g)))
                    eqn : Hl,
                          (Info.target (Config.state (conf (Good g))))
                            eqn : Htgt;
    try easy.
  - destruct (Graph.Veq_dec l0 l). now rewrite Hl in Hl0.
    destruct (Rdec dist 0). now rewrite Hl in Hl0.
    destruct (Rdec dist 1). now simpl in *.
    simpl in *.
    rewrite Htgt in *.            
    simpl in *.
    destruct (Graph.find_edge l l0) eqn : Hedge; simpl in *.
    specialize (Hli l (reflexivity _)).
    destruct Hli.
    destruct Hl0 as (He, Hp).
    assert (Hedge' : opt_eq Graph.Eeq (Graph.find_edge l l0) (Some e'))
      by now (rewrite Hedge; apply He).
    clear Hgroup Hmi.
    rewrite Ht0 in *.
    rewrite H in Hs0.
    now simpl in Hs0; rewrite Hs0 in Hedge'.
    easy.
    simpl in*.
    specialize (Hex_e v1' l0 Hs0 (reflexivity l0)).
    destruct Hex_e.
    destruct (Hli l (reflexivity _));
      try rewrite Hs0 in *.
    simpl in *.
    rewrite H0 in *.
    now rewrite Hedge in H.
    easy.
  - destruct (Rle_dec 1 (project_p p + dist));try now simpl in *.
    simpl in *.
    destruct (Rdec dist 0); simpl in *;
      specialize (Hmi v1' v2' e' p);
      rewrite Htgt in *;
      apply Hmi; try easy.
  - destruct (Location.eq_dec
                (Loc
                   match
                     rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                         (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                   with
                   | Loc l => (Iso.sim_V (sim ⁻¹)) l
                   | Mvt e _ => Graph.src e
                   end) (Loc l));
      try (rewrite Hl in Hl0;
           now simpl in * ).
    now simpl in *.
  - destruct (Location.eq_dec
                (Loc
                   match
                     rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                         (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                   with
                   | Loc l => (Iso.sim_V (sim ⁻¹)) l
                   | Mvt e _ => Graph.src e
                   end) (Mvt e p));
      try (rewrite Hl in Hl0;
           now simpl in * ).
    now simpl in *.
    + intros v1' v2'.
      unfold round; simpl in *.
      destruct (Hinit g) as (_, (lt', (_, Ht')));
      destruct (step da (Good g) (conf (Good g)))
        as [dist | sim]
             eqn : Hstep,
                   (Config.loc (conf (Good g)))
          as [l| e p] eqn : Hloc,
             (Info.target (Config.state (conf (Good g))))
               as [lt | ? ?] eqn : Htgt;
      try easy
      ; simpl in *.
  - specialize (Hex_e v1' v2').
    destruct (Graph.Veq_dec lt l);
    destruct (Rdec dist 0);
    destruct (Rdec dist 1); simpl in *;
      try rewrite Htgt; 
      try apply Hex_e.
  - specialize (Hex_e v1' v2').
    destruct (Rle_dec 1 (project_p p + dist)); simpl in *;
      rewrite Htgt; apply Hex_e.
  - destruct ( Location.eq_dec
             (Loc
                match
                  rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Loc ((Iso.sim_V sim) l))
                with
                | Loc l0 => Bijection.retraction (Iso.sim_V sim) l0
                | Mvt e _ => Graph.src e
                end) (Loc l)).
    { destruct (Hgroup g) as (_, (_, (_, Hsome))). apply Hsome. }
    simpl.
    assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Active sim)) by (now rewrite Hstep);
    assert (Hdelta := step_delta da g (conf (Good g)) sim Hstep').
    destruct Hdelta as (Hl_delta, Ht_delta).
    intros Hl Hr.
    rewrite Hloc in Ht_delta.
    destruct (Config.loc (Config.map (apply_sim sim) conf (Good g))) eqn : Hsim_loc.
    * assert (Hrange := pgm_range rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                                      (Config.loc (Config.map (apply_sim sim) conf (Good g))) l0).
      destruct Hrange as (l_rbg, (e_rbg, (Hr_loc, Hedge))).
      now rewrite Hsim_loc.
      simpl in *; rewrite Hloc in *.
      rewrite Hsim_loc in *.
      rewrite Hr_loc in Hr.
      exists ((Bijection.retraction (Iso.sim_E sim)) e_rbg).
      rewrite Graph.find_edge_Some in *.
      generalize (Iso.sim_morphism (Iso.inverse sim) e_rbg).
      intros (s,t).
      clear Hmi.
      simpl in *.
      rewrite <- s, <- (proj1 Hedge).
      unfold Config.map, apply_sim, projectS, projectS_loc in *.
      simpl in *.
      assert (Location.eq (Loc ((Iso.sim_V sim) l)) (Loc l0)) by now rewrite Hsim_loc.
      unfold Location.eq, loc_eq in H.
      rewrite <- H.
      rewrite (Bijection.retraction_section); autoclass; [].
      split; try now symmetry.
      apply LocationA.eq_equiv.
      rewrite <- Hr.
      simpl in *.
      destruct Hedge as (s',t').
      rewrite t'.
      now simpl.
    * destruct n.
      simpl in *.
      rewrite Hloc in *.
      now simpl in *.
  - destruct (Location.eq_dec
             (Loc
                match
                  rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                    (Mvt ((Iso.sim_E sim) e)
                       (project_p_inv ((Iso.sim_T sim) (project_p p))))
                with
                | Loc l => Bijection.retraction (Iso.sim_V sim) l
                | Mvt e0 _ => Graph.src e0
                end) (Mvt e p)); try now simpl in *.
Qed.


(** finals proofs*)
CoInductive group : execution -> Prop :=
  GroupCons : forall e, group_good_def (Stream.hd e) -> group (Stream.tl e) -> group e.

Lemma group_round : forall r da config, group_good_def config -> group_good_def (round r da config).
Proof.
  intros r da config Hinit g.
  apply group_lem.
  now destruct (Hinit g).
Qed.

Lemma group_always : forall r d config, group_good_def config -> group (execute r d config).
Proof.
  cofix Hrec.
  intros d config r Hinit.
  constructor.
  + unfold execute. simpl. assumption.
  + rewrite execute_tail. simpl. apply Hrec. apply group_round. assumption.
Qed.

Corollary group_always_bis : forall r d config, Conf_init config ->
                                                group (execute r d (round r (Stream.hd d) config)).
Proof.
  intros.
  apply group_always.
  now apply group_lem_init. 
Qed.
*)

End CGF.
