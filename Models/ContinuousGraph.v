(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)

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

(** We do not want to use the default equivalence on [E]
    because we only need equality of source, target and threshold on the edge. *)
Global Instance E_src_tgt_thd_Setoid : Setoid E :=
  @inter_Setoid E (@inter_Setoid E (precompose_Setoid src) (precompose_Setoid tgt))
                  (precompose_Setoid threshold).
Global Instance E_src_tgt_thd_EqDec : EqDec E_src_tgt_thd_Setoid :=
  inter_EqDec (inter_EqDec (precompose_EqDec src) (precompose_EqDec tgt)) (precompose_EqDec threshold).

Global Instance E_subrelation : subrelation (@equiv E E_Setoid) (@equiv E E_src_tgt_thd_Setoid).
Proof. intros ? ? Heq. split; simpl; now rewrite Heq. Qed.

Global Instance src_compat : Proper (equiv ==> equiv) src.
Proof. intros ? ? Heq. apply Heq. Qed.

Global Instance tgt_compat : Proper (equiv ==> equiv) tgt.
Proof. intros ? ? Heq. apply Heq. Qed.

Global Instance threshold_compat : Proper (equiv ==> equiv) threshold.
Proof. intros ? ? Heq. apply Heq. Qed.

(* Since iso_E gives a bijection that comes with its setoid,
   we need to be lower level to change it from [E_Setoid] to [E_src_tgt_thd_Setoid]. *)
Global Instance iso_E_compat : forall iso,
  Proper (equiv ==> equiv) (iso_E iso).
Proof.
intros iso ? ? [[Hsrc Htgt] Hthd].
repeat split; unfold equiv in *; cbn -[equiv] in *.
- now rewrite <- 2 (proj1 (iso_morphism _ _)), Hsrc.
- now rewrite <- 2 (proj2 (iso_morphism _ _)), Htgt.
- rewrite <- 2 iso_threshold. now f_equiv.
Qed.


(** Robots can be either on a location or somewhere on an edge. *)
Inductive loc :=
  | OnVertex (l : location)
  | OnEdge (e : E) (p : strict_ratio).

Global Instance locG_Setoid : Setoid loc := {
  equiv := fun l l' =>
             match l, l' with
               | OnVertex l, OnVertex l' => l == l'
               | OnEdge e p, OnEdge e' p' => e == e' /\ p == p'
               | _, _ => False
             end}.
Proof. split.
+ now intros [].
+ intros [] [] Heq; simpl in *; decompose [False and] Heq; repeat split; now symmetry.
+ intros [] [] [] Heq1 Heq2; simpl in *;
  decompose [False and] Heq1; decompose [False and] Heq2; repeat split; etransitivity; eauto.
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

(** We can use an isomorphism to build a bijection on a continuous graph. *)
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
* intros [| e1 p1] [| e2 p2] Heq; simpl in Heq; trivial.
  + now repeat f_equiv.
  + destruct Heq as [[[Hsrc Htgt] Hthd] Hp]. repeat split; simpl.
    - rewrite <- (proj1 (iso_morphism iso e1)), Hsrc. apply iso_morphism.
    - rewrite <- (proj2 (iso_morphism iso e1)), Htgt. apply iso_morphism.
    - now rewrite <- 2 iso_threshold, Hthd.
    - assumption.
* intros [| e1 p1] [| e2 p2] ; simpl in *; try tauto; [|]; split; intro Heq.
  + rewrite <- Heq. apply Bijection.retraction_section.
  + rewrite <- Heq. apply Bijection.section_retraction.
  + destruct Heq as [[[Hsrc Htgt] Hthd] Hp]. repeat split.
    - change (Bijection.retraction (iso_E iso)) with (Bijection.section (iso_E (inverse iso))).
      rewrite <- (proj1 (iso_morphism _ e2)). simpl.
      now rewrite <- (Bijection.Inversion iso), (proj1 (iso_morphism _ e1)).
    - change (Bijection.retraction (iso_E iso)) with (Bijection.section (iso_E (inverse iso))).
      rewrite <- (proj2 (iso_morphism _ e2)). simpl.
      now rewrite <- (Bijection.Inversion iso), (proj2 (iso_morphism _ e1)).
    - change (Bijection.retraction (iso_E iso)) with (Bijection.section (iso_E (inverse iso))).
      rewrite <- (iso_threshold _ e2), <- Hthd, iso_threshold.
      simpl. now rewrite Bijection.retraction_section.
    - auto.
  + destruct Heq as [[[Hsrc Htgt] Hthd] Hp]. repeat split.
    - now rewrite <- (proj1 (iso_morphism _ e1)), <- Hsrc, (proj1 (iso_morphism _ _)),
                  Bijection.section_retraction.
    - now rewrite <- (proj2 (iso_morphism _ e1)), <- Htgt, (proj2 (iso_morphism _ _)),
                  Bijection.section_retraction.
    - now rewrite <- (iso_threshold _ e1), <- Hthd, (iso_threshold _ _),
                  Bijection.section_retraction.
    - auto.
Defined.

Global Instance bijectionG_compat :  Proper (equiv ==> equiv) bijectionG.
Proof.
intros iso1 iso2 Hiso []; simpl.
+ apply Hiso.
+ repeat split; apply Graph.src_compat || apply Graph.tgt_compat
                                       || apply Graph.threshold_compat; apply Hiso.
Qed.

(** ** Translation of locations *)

Definition location_G2V (loc : locG) : locV :=
  match loc with
    | OnVertex l => l
    | OnEdge e p => if Rle_dec (threshold e) p then Graph.tgt e else Graph.src e
  end.

Global Instance location_G2V_compat : Proper (equiv ==> equiv) location_G2V.
Proof.
unfold location_G2V. intros [l1 | e1 p1] [l2 | e2 p2] Hxy; try tauto; [].
destruct Hxy as [Hexy Hpxy],
         (Rle_dec (threshold e1) p1) eqn:Hx,
         (Rle_dec (threshold e2) p2) eqn:Hy.
+ apply Hexy.
+ assert (Ht := proj2 Hexy).
  assert (Hr : (threshold e1 <= p1)%R) by assumption.
  now rewrite Ht, Hpxy in Hr.
+ assert (Hr : (threshold e2 <= p2)%R) by assumption.
  assert (Ht := proj2 Hexy).
  now rewrite <- Ht, <- Hpxy in Hr.
+ apply Hexy.
Qed.

Definition location_V2G : locV -> locG := OnVertex.

Global Instance location_V2G_compat : Proper (equiv ==> equiv) location_V2G.
Proof. repeat intro. now simpl. Qed.

(** ** Translation of states **)

(** Even in the discrete setting, the current location is either the source or the target
    of the edge the robot wants to move along. *)
Definition valid_stateV (state : locV * E) :=
  fst state == src (snd state) \/ fst state == tgt (snd state).

Definition stateV := sig valid_stateV.

Instance stateV_Setoid : Setoid stateV :=
  sig_Setoid (prod_Setoid location_Setoid E_src_tgt_thd_Setoid).
Instance stateV_EqDec : EqDec stateV_Setoid :=
  sig_EqDec (prod_EqDec location_EqDec E_src_tgt_thd_EqDec) _.

Global Instance valid_stateV_compat :
  Proper (@equiv _ (prod_Setoid _ E_src_tgt_thd_Setoid) ==> iff) valid_stateV.
Proof.
intros ? ? [Hpt [[Hsrc Htgt] _]]. simpl in Hsrc, Htgt.
unfold valid_stateV. now rewrite Hpt, Hsrc, Htgt.
Qed.

(** Applying a graph isomorphism preserves this property. *)
Lemma valid_stateV_iso : forall state iso,
  valid_stateV state -> valid_stateV (iso.(iso_V) (fst state), iso.(iso_E) (snd state)).
Proof.
intros [pt e] iso [Hcase | Hcase].
+ left. simpl in *. rewrite Hcase. apply iso_morphism.
+ right. simpl in *. rewrite Hcase. apply iso_morphism.
Qed.

Lemma valid_stateV_iso' : forall v e iso pt, pt == iso.(iso_V) v ->
  valid_stateV (v, e) -> valid_stateV (pt, iso.(iso_E) e).
Proof.
intros v e iso pt Hpt [Hcase | Hcase].
+ left. simpl in *. rewrite Hpt, Hcase. apply iso_morphism.
+ right. simpl in *. rewrite Hpt, Hcase. apply iso_morphism.
Qed.

(** In the continuous case, the state must also contain the destination of the robot.
    If it is on an edge, the destination is the [tgt] of the edge.
    If it is on a vertex, we it is the case as in the discrete case: we add the destination. *)
Inductive stateG :=
  | SOnVertex v e (proof : valid_stateV (v, e))
  | SOnEdge (e : E) (p : strict_ratio).

Global Instance stateG_Setoid : Setoid stateG := {
  equiv := fun x y =>
             match x, y with
               | SOnVertex v e _, SOnVertex v' e' _ => v == v' /\ e == e'
               | SOnEdge e p, SOnEdge e' p' => e == e' /\ p == p'
               | _, _ => False
             end}.
Proof. split.
+ intros [|]; split; reflexivity.
+ intros [|] [|] []; split; now symmetry.
+ intros [|] [|] [|] [] []; split; etransitivity; eauto.
Defined.

Global Instance stateG_EqDec : EqDec stateG_Setoid.
Proof.
intros [v1 e1 proof1 | e1 p1] [v2 e2 proof2 | e2 p2]; simpl.
+ destruct (v1 =?= v2); [destruct (e1 =?= e2) |]; auto.
+ auto.
+ auto.
+ destruct (e1 =?= e2); [destruct (p1 =?= p2) |]; auto.
Defined.

Lemma SOnVertex_compat : forall v v' e e' p p',
  v == v' -> e == e' -> SOnVertex v e p == SOnVertex v' e' p'.
Proof. intros. now split. Qed.

Global Instance SOnEdge_compat : Proper (equiv ==> equiv ==> equiv) SOnEdge.
Proof. intros ? ? He ? ? Hp. now split. Qed.

Definition stateG2loc state :=
  match state with
    | SOnVertex v _ _ => OnVertex v
    | SOnEdge e p => OnEdge e p
  end.

Instance stateG2loc_compat : Proper (equiv ==> equiv) stateG2loc.
Proof. intros [] [] *; simpl in *; tauto. Qed.

(** Embedding and projection between both kinds of states. *)
Definition state_V2G (state : stateV) : stateG :=
  SOnVertex (fst (proj1_sig state)) (snd (proj1_sig state)) (proj2_sig state).

Global Instance state_V2G_compat : Proper (equiv ==> equiv) state_V2G.
Proof. intros ? ? []. unfold state_V2G. now split. Qed.

Definition state_G2V (state : stateG) : stateV :=
  match state with
    | SOnVertex v e p => exist valid_stateV (v, e) p
    | SOnEdge e p => if Rle_dec (@threshold locV E G e) p
                     then exist valid_stateV (Graph.tgt e, e) ltac:(now right)
                     else exist valid_stateV (Graph.src e, e) ltac:(now left)
  end.

Global Instance state_G2V_compat : Proper (equiv ==> equiv) state_G2V.
Proof.
intros [v e p | e p] [v' e' p' | e' p'] Hstate; auto; [].
destruct Hstate as [[[Hsrc Htgt] Hthd] Hp]. simpl.
destruct (Rle_dec (threshold e) p), (Rle_dec (threshold e') p');
repeat split; simpl in *; rewrite ?Hsrc, ?Htgt, ?Hthd in *; try reflexivity; [|];
destruct p, p'; simpl in *; subst; contradiction.
Qed.

Lemma state_V2G2V : forall state, state_G2V (state_V2G state) == state.
Proof. intro. simpl. repeat (split; try reflexivity). Qed.

(** ** On configurations *)

(** The precondition for liftable changes of frame is that they must come from isomorphisms. *)
Global Instance InfoV : @State LocationV stateV := {|
  get_location := fun state => fst (proj1_sig state);
  state_Setoid := stateV_Setoid;
  precondition := fun f => sigT (fun iso => f == iso.(iso_V) /\ iso_T iso == @Bijection.id R _);
  lift := fun f state => exist _ (projT1 f (fst (proj1_sig state)),
                                  iso_E (projT1 (projT2 f)) (snd (proj1_sig state))) _ |}.
Proof.
+ abstract (destruct f as [f [iso [Hiso ?]]], state as [state [Hcase | Hcase]];
            cbn; left + right; rewrite Hiso, Hcase; cbn; apply iso_morphism).
+ (* lift_id *)
  intros [iso [Hiso Ht]] [state Hstate]. simpl. split; try reflexivity; [].
  change (src (snd state)) with (Datatypes.id (src (snd state))).
  change (tgt (snd state)) with (Datatypes.id (tgt (snd state))).
  rewrite (Hiso (src (snd state))), (Hiso (tgt (snd state))).
  repeat split; symmetry; try apply iso_morphism; [].
  now rewrite <- iso_threshold, Ht.
+ reflexivity.
+ intros ? ? Heq. apply Heq.
+ (* lift_compat *)
  intros [f [iso1 [Hiso1 Ht1]]] [g [iso2 [Hiso2 Ht2]]] Heq [] [] [Heq1 [Heq2 Heq3]].
  cbn in *. repeat split.
  - now apply Heq.
  - rewrite <- (proj1 (iso_morphism iso1 _)), <- Hiso1,
            <- (proj1 (iso_morphism iso2 _)), <- Hiso2.
    now apply Heq.
  - rewrite <- (proj2 (iso_morphism iso1 _)), <- Hiso1,
            <- (proj2 (iso_morphism iso2 _)), <- Hiso2.
    now apply Heq.
  - now rewrite <- 2 iso_threshold, Ht1, Ht2.
Defined.

Definition good_iso_of f iso := f == Bijection.section (bijectionG iso)
                                /\ iso_T iso == @Bijection.id R _.
Definition preconditionG := fun f => sigT (good_iso_of f).

Definition liftG (f : sigT preconditionG) state :=
  let iso := projT1 (projT2 f) in
  match state with
    | SOnVertex v e proof =>
        SOnVertex (iso_V iso v) (iso_E iso e) (valid_stateV_iso (v, e) iso proof)
    | SOnEdge e p => SOnEdge (iso_E iso e) p
  end.

Global Instance liftG_compat : Proper (@equiv (sigT preconditionG) _ ==> equiv ==> equiv) liftG.
Proof.
intros [f [iso1 [Hiso1 Ht1]]] [g [iso2 [Hiso2 Ht2]]] Hfg state1 state2 Hstate.
assert (Heq : iso_V iso1 == iso2).
{ intro x. assert (Heq1 := Hiso1 (OnVertex x)). assert (Heq2 := Hiso2 (OnVertex x)).
  cut ((bijectionG iso1) (OnVertex x) == (bijectionG iso2) (OnVertex x)); auto; [].
  rewrite <- Heq1, <- Heq2. now apply Hfg. }
hnf in Hfg. simpl projT1 in Hfg.
destruct state1 as [v1 e1 proof1 | e1 p1],
         state2 as [v2 e2 proof2 | e2 p2];
simpl; hnf in *; simpl fst in *; simpl snd in *.
+ repeat split.
  - rewrite Heq. now f_equiv.
  - rewrite <- (proj1 (iso_morphism iso1 e1)), <- (proj1 (iso_morphism iso2 e2)).
    rewrite Heq. f_equiv. apply Hstate.
  - rewrite <- (proj2 (iso_morphism iso1 e1)), <- (proj2 (iso_morphism iso2 e2)).
    rewrite Heq. f_equiv. apply Hstate.
  - rewrite <- 2 iso_threshold, Ht1, Ht2. simpl. apply Hstate.
+ tauto.
+ tauto.
+ repeat split.
  - rewrite <- (proj1 (iso_morphism iso1 e1)), Heq, <- (proj1 (iso_morphism iso2 e2)).
    f_equiv. apply Hstate.
  - rewrite <- (proj2 (iso_morphism iso1 e1)), Heq, <- (proj2 (iso_morphism iso2 e2)).
    f_equiv. apply Hstate.
  - rewrite <- 2 iso_threshold, Ht1, Ht2. simpl. apply Hstate.
  - apply Hstate.
Qed.

Lemma compose_precondition_proof : forall f g : sigT preconditionG,
  preconditionG (fun x => projT1 f (projT1 g x)).
Proof.
intros f g.
exists (compose (projT1 (projT2 f)) (projT1 (projT2 g))).
destruct f as [f [isof [Hf Hft]]], g as [g [isog [Hg Hgt]]].
split; intro x.
- simpl projT1. rewrite Hf, Hg. now destruct x.
- simpl iso_T. simpl Bijection.section. now rewrite Hft, Hgt.
Defined.

Definition compose_precondition f g :=
  existT preconditionG (fun x => projT1 f (projT1 g x)) (compose_precondition_proof f g).

Lemma liftG_compose : forall f g,
  (fun x => liftG f (liftG g x)) == liftG (compose_precondition f g).
Proof.
intros [f [isof [Hisof Hft]]] [g [isog [Hisog Hgt]]] x.
unfold compose_precondition.
destruct x; simpl; repeat split; reflexivity.
Qed.

Global Instance InfoG : @State LocationG stateG := {|
  get_location := stateG2loc;
  state_Setoid := stateG_Setoid;
  precondition := preconditionG;
  lift := liftG |}.
Proof.
* (* lift_id *)
  intros [iso [Hiso Ht]] [v e proof | e p]; simpl.
  + assert (Hv := Hiso (OnVertex v)).
    assert (Hsrc := Hiso (OnVertex (src e))).
    assert (Htgt := Hiso (OnVertex (tgt e))).
    specialize (Ht (threshold e)).
    simpl in Hv, Hsrc, Htgt, Ht.
    rewrite <- (proj1 (iso_morphism iso e)),
            <- (proj2 (iso_morphism iso e)), <- iso_threshold; auto.
  + assert (Hsrc := Hiso (OnVertex (src e))).
    assert (Htgt := Hiso (OnVertex (tgt e))).
    specialize (Ht (threshold e)).
    simpl in Hsrc, Htgt, Ht.
    rewrite <- (proj1 (iso_morphism iso e)),
            <- (proj2 (iso_morphism iso e)), <- iso_threshold; auto.
* (* get_location_lift *)
  intros [f [iso [Hiso Ht]]] [v e proof | e p]; simpl;
  destruct_match_eq Hf; simpl in Hf;
  (apply (@eq_subrelation _ equiv) in Hf; autoclass; []);
  rewrite Hiso in Hf; simpl in Hf; tauto.
* (* lift_compat *)
  intros [f [iso1 [Hiso1 Ht1]]] [g [iso2 [Hiso2 Ht2]]] Hfg state1 state2 Hstate.
  apply liftG_compat; trivial; [].
  hnf. simpl projT1. intro x. apply (Hfg x x (reflexivity x)).
Defined.

Notation configV := (@configuration _ stateV _ _).
Notation configG := (@configuration _ stateG _ _).

(* RMK: we cannot use map_config as the Location instance is not the same. *)
Definition config_V2G (config : configV) : configG := fun id => state_V2G (config id).

Global Instance config_V2G_compat : Proper (equiv ==> equiv) config_V2G.
Proof. intros ? ? Hconfig id. unfold config_V2G. f_equiv. apply Hconfig. Qed.

Definition config_G2V (config : configG) : configV := fun id => state_G2V (config id).

Global Instance config_G2V_compat : Proper (equiv ==> equiv) config_G2V.
Proof. intros ? ? Hconfig id. unfold config_G2V. f_equiv. apply Hconfig. Qed.

Lemma config_V2G2V : forall config : configV, config_G2V (config_V2G config) == config.
Proof. intros. unfold config_G2V, config_V2G. now repeat try (split; simpl). Qed.

(** The spectrum for continuous setting is almost the same as for the discrete one:
    we simply project robots on edges either to the source or target of the edge
    depending on where they are located compared to the threshold of the edge;
    and add the current location. *)
Global Instance spect_V2G (Spect : @Spectrum _ _ InfoV _) : @Spectrum _ _ InfoG _ := {
  spectrum := @spectrum _ _ _ _ Spect;
  spect_from_config := fun config st => spect_from_config (config_G2V config) (state_G2V st);
  spect_is_ok s config st := spect_is_ok s (config_G2V config) (state_G2V st) }.
Proof.
+ abstract (now repeat intro; repeat f_equiv).
+ repeat intro. apply spect_from_config_spec.
Defined.

(** Robograms can only pick which edge they want to move on.
    The update function will check that they only move to adjacent locations. *)
Global Instance Robot : robot_choice E := {robot_choice_Setoid := E_src_tgt_thd_Setoid}.

(** ** Translation of robograms **)

Context {Spect : @Spectrum _ _ InfoV _}.
Notation robogramV := (@robogram _ _ InfoV _ Spect).
Notation robogramG := (@robogram _ _ InfoG _ (spect_V2G Spect)).

Definition rbg_V2G (rbgV : robogramV) : robogramG :=
  @Build_robogram _ _ InfoG _ (spect_V2G Spect) _ _ rbgV rbgV.(pgm_compat).

Global Instance rbg_V2G_compat : Proper (equiv ==> equiv) rbg_V2G.
Proof. intros ra1 ra2 Hra. simpl. apply Hra. Qed.

Definition rbg_G2V (rbgG : robogramG) : robogramV :=
  @Build_robogram _ _ InfoV _ Spect _ _ rbgG rbgG.(pgm_compat).

Global Instance rbg_G2V_compat : Proper (equiv ==> equiv) rbg_G2V.
Proof. intros ra1 ra2 Hra s. simpl. apply Hra. Qed.

Lemma rbg_V2G2V : forall rbgV, rbg_G2V (rbg_V2G rbgV) == rbgV.
Proof. intro. simpl. repeat split; reflexivity. Qed.

(** **  Demonic schedulers  **)

(** Acceptable frame changes must not change the thresholds. *)
Definition stable_threshold iso := iso_T iso == @Bijection.id R _.

Definition stable_threshold_inverse : forall iso,
  stable_threshold iso -> stable_threshold (inverse iso).
Proof.
intros iso Hstable x. unfold stable_threshold in *. simpl in *.
now rewrite <- (Hstable x), Bijection.retraction_section.
Qed.

(** Graph isomorphisms not changing thresholds as a frame choice *)
Global Instance FrameChoiceIsomorphismV : @frame_choice LocationV (sig stable_threshold) := {|
  frame_choice_bijection := fun f => @iso_V locV E G (proj1_sig f);
  frame_choice_Setoid := sig_Setoid (@isomorphism_Setoid locV E G);
  frame_choice_bijection_compat :=
    fun f g => @iso_V_compat locV E G (proj1_sig f) (proj1_sig g) |}.

Global Instance FrameChoiceIsomorphismG : @frame_choice LocationG (sig stable_threshold) := {|
  frame_choice_bijection := fun f => bijectionG (proj1_sig f);
  frame_choice_Setoid := sig_Setoid (@isomorphism_Setoid locV E G);
  frame_choice_bijection_compat := fun f g => bijectionG_compat (proj1_sig f) (proj1_sig g) |}.

(** The demon update choice only contains the movement ratio, either a boolean or a ratio. *)
Global Instance graph_update_bool : update_choice bool := { update_choice_EqDec := bool_eqdec }.
Global Instance graph_update_ratio : update_choice ratio := Flexible.OnlyFlexible.

Global Instance graph_inactive_bool : inactive_choice bool := {
  inactive_choice_EqDec := bool_eqdec }.
Global Instance graph_inactive_ratio : inactive_choice ratio := {
  inactive_choice_EqDec := ratio_EqDec }.

End CGF.

Arguments config_V2G _ _ _ _ config id /.
Arguments config_G2V _ _ _ _ config id /.
