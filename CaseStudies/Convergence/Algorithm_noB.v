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
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.    *)
(**************************************************************************)


Require Import Utf8.
Require Import Reals.
Require Import SetoidDec.
Require Import Lia.
Require Import SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Observations.SetObservation.
Require Import Pactole.Models.Rigid.
Require Import Pactole.Models.Similarity.
Set Implicit Arguments.
Close Scope R_scope.
Import Datatypes.
Import List.
Import SetoidClass.
Typeclasses eauto := (bfs).


Section ConvergenceAlgo.
(** There are [n] good robots and no byzantine one. *)
Variable n : nat.
Hypothesis n_non_0 : n <> 0%nat.

Instance MyRobots : Names := Robots n 0.

(* BUG?: To help finding correct instances, loops otherwise! *)
Instance Loc : Location := {| location := R2 |}.
Instance Loc_VS : RealVectorSpace location := R2_VS.
Instance Loc_ES : EuclideanSpace location := R2_ES.
Remove Hints R2_Setoid R2_EqDec : typeclass_instances.
Instance Info : State location := OnlyLocation (fun _ => True).
Instance Robots : robot_choice location := { robot_choice_Setoid := location_Setoid }.
Instance FDC : frame_choice (Similarity.similarity location) := FrameChoiceSimilarity.
Instance NoActiveChoice : update_choice unit := {update_choice_EqDec := unit_eqdec}.
Instance NoInactiveChoice : inactive_choice unit := {inactive_choice_EqDec := unit_eqdec}.

Instance UpdateFun : update_function location (Similarity.similarity location) unit := {
  update := fun _ _ _ pt _ => pt;
  update_compat := ltac:(repeat intro; subst; auto) }.

Instance InactiveFun : inactive_function unit := {
  inactive := fun config id _ => config id;
  inactive_compat := ltac:(repeat intro; subst; auto) }.

Instance Update : RigidSetting.
Proof using . split. now intros. Qed.

(* Refolding typeclass instances *)
Ltac changeR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change state_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change state_EqDec with location_EqDec in *;
  change R2_VS with Loc_VS in *;
  change R2_ES with Loc_ES in *.

(** The observation is a set of positions *)
Notation "!!" := (fun config => @obs_from_config location _ _ _ set_observation config origin).

Implicit Type config : configuration.
Implicit Type da : demonic_action.
Implicit Type pt : location.

(** As there are robots, the observation can never be empty. *)
Lemma obs_non_empty : forall config pt, obs_from_config config pt =/= @empty location _ _ _.
Proof using n_non_0.
intros config pt.
rewrite obs_from_config_ignore_snd. intro Habs.
assert (Hn : 0%nat < n). { generalize n_non_0. intro. lia. }
pose (g := exist _ 0%nat Hn : G).
specialize (Habs (config (Good g))).
rewrite empty_spec in Habs.
assert (Hin := pos_in_config config origin (Good g)).
simpl in Hin. unfold id in Hin. tauto.
Qed.

Hint Resolve obs_non_empty : core.

(** There is no byzantine robot so to prove anything about an ident
    we just need to consider good robots.*)
Lemma no_byz : forall P, (forall g, P (Good g)) -> forall id, P id.
Proof using n_non_0.
intros P Hg [g | b].
+ apply Hg.
+ destruct b. lia.
Qed.

(** ** Properties of executions  *)

Open Scope R_scope.

(** All robots are contained in the disk defined by [center] and [radius]. *)
Definition contained (center : R2) (radius : R) (config : configuration) : Prop :=
  forall g, dist center (get_location (config (Good g))) <= radius.

(** Expressing that all good robots stay confined in a small disk. *)
Definition imprisoned (center : R2) (radius : R) (e : execution) : Prop :=
  Stream.forever (Stream.instant (contained center radius)) e.

(** The execution will end in a small disk. *)
Definition attracted (c : R2) (r : R) (e : execution) : Prop := Stream.eventually (imprisoned c r) e.

Instance contained_compat : Proper (equiv ==> Logic.eq ==> equiv ==> iff) contained.
Proof using .
intros ? ? Hc ? ? Hr ? ? Hconfig. subst. unfold contained.
setoid_rewrite Hc. setoid_rewrite Hconfig. reflexivity.
Qed.

Instance imprisoned_compat : Proper (equiv ==> Logic.eq ==> @equiv _ Stream.stream_Setoid ==> iff) imprisoned.
Proof using .
unfold imprisoned. repeat intro.
apply Stream.forever_compat; trivial; []. repeat intro.
apply Stream.instant_compat; trivial; [].
now apply contained_compat.
Qed.

Instance attracted_compat : Proper (equiv ==> eq ==> @equiv _ Stream.stream_Setoid ==> iff) attracted.
Proof using . intros ? ? Heq ? ? ?. now apply Stream.eventually_compat, imprisoned_compat. Qed.

(** A robogram solves convergence if all robots are attracted to a point,
    no matter what the demon and the starting configuration are. *)
Definition solution_SSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : similarity_demon), Fair d →
  forall (ε : R), 0 < ε → exists (pt : R2), attracted pt ε (execute r d config).

Definition solution_FSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : similarity_demon), FSYNC (similarity_demon2demon d) →
  forall (ε : R), 0 < ε → exists (pt : R2), attracted pt ε (execute r d config).

Lemma synchro : ∀ r, solution_SSYNC r → solution_FSYNC r.
Proof using .
unfold solution_SSYNC. intros r Hfair config d Hd.
apply Hfair, FSYNC_implies_fair; autoclass.
Qed.

Close Scope R_scope.


(** * Proof of correctness of a convergence algorithm with no byzantine robot. *)

Definition convergeR2_pgm (s : observation) : location :=
  isobarycenter (elements s).

Instance convergeR2_pgm_compat : Proper (equiv ==> equiv) convergeR2_pgm.
Proof using . intros ? ? Heq. unfold convergeR2_pgm. apply isobarycenter_compat. now rewrite Heq. Qed.

Definition convergeR2 : robogram := {| pgm := convergeR2_pgm |}.

(** Rewriting round using only the global frame fo reference. *)
Theorem round_simplify : forall da config, SSYNC_da da ->
  round convergeR2 da config
  == fun id => if da.(activate) id
               then isobarycenter (@elements location _ _ _ (!! config))
               else config id.
Proof using n_non_0.
intros da config HSSYNC. rewrite SSYNC_round_simplify; trivial; [].
intro id. pattern id. apply no_byz. clear id. intro g.
unfold round. destruct_match; try reflexivity; [].
remember (change_frame da config g) as sim.
change (Bijection.section (inverse (frame_choice_bijection sim)))
  with (Bijection.section (sim ⁻¹)).
cbn -[equiv location mul map_config lift precondition inverse].
unfold convergeR2_pgm. unfold map_config at 2.
rewrite <- obs_from_config_map, map_injective_elements; autoclass; try apply Similarity.injective; [].
cbn -[inverse isobarycenter equiv].
rewrite obs_from_config_ignore_snd, isobarycenter_sim_morph.
+ now simpl; rewrite Bijection.retraction_section.
+ rewrite elements_nil. apply obs_non_empty.
Qed.

(** Once robots are contained within a circle, they will never escape it. *)

(* First, we assume a geometric property of the isobarycenter:
   if all points are included in a circle, then so is their isobarycenter. *)
Axiom isobarycenter_circle : forall center radius (l : list R2),
  List.Forall (fun pt => dist center pt <= radius)%R l ->
  (dist center (isobarycenter l) <= radius)%R.

Lemma contained_isobarycenter : forall c r config,
  contained c r config -> (dist c (isobarycenter (elements (!! config))) <= r)%R.
Proof using n_non_0.
intros c r config Hc. apply isobarycenter_circle.
rewrite Forall_forall. intro.
rewrite <- InA_Leibniz. change eq with (@equiv location _).
rewrite elements_spec, obs_from_config_In.
intros [id Hpt]. rewrite <- Hpt.
pattern id. apply no_byz. apply Hc.
Qed.

Lemma contained_next : forall da c r config, SSYNC_da da ->
  contained c r config -> contained c r (round convergeR2 da config).
Proof using n_non_0.
intros da c r config HSSYNC Hconfig g.
rewrite round_simplify; trivial; [].
destruct_match.
- now apply contained_isobarycenter.
- auto.
Qed.

Lemma converge_forever : forall d c r config, SSYNC d ->
  contained c r config -> imprisoned c r (execute convergeR2 d config).
Proof using n_non_0.
cofix Hcorec. intros d c r config [] Hrec. constructor.
- apply Hrec.
- apply Hcorec; auto using contained_next.
Qed.


(************************)
(** *  Final theorems  **)
(************************)

Theorem convergence_FSYNC : solution_FSYNC convergeR2.
Proof using n_non_0.
intros config d [Hfair ?] ε Hε.
exists (isobarycenter (elements (obs_from_config (Observation := set_observation) config 0))).
apply Stream.Later, Stream.Now. rewrite execute_tail.
apply converge_forever; auto using FSYNC_SSYNC; [].
intro g. rewrite round_simplify; auto using FSYNC_SSYNC_da; [].
rewrite Hfair. changeR2.
transitivity 0%R; try (now apply Rlt_le); [].
apply Req_le. now apply dist_defined.
Qed.

Theorem convergence_SSYNC : solution_SSYNC convergeR2.
Proof.
Abort.

End ConvergenceAlgo.
