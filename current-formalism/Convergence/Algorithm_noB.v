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
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Utf8.
Require Import Reals.
Require Import Psatz.
Require Import SetoidDec.
Require Import Arith.Div2.
Require Import Omega.
Require Import SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Spectra.MultisetSpectrum.
Require Import Pactole.Models.Rigid.
Require Import Pactole.Models.Similarity.
Set Implicit Arguments.
Close Scope R_scope.
Import Datatypes.
Import List.
Import SetoidClass.
Import Pactole.Spaces.Similarity.Notations.


(** There are [n] good robots and no byzantine one. *)
Parameter n : nat.
Axiom n_non_0 : n <> 0%nat.

Instance MyRobots : Names := Robots n 0.

(* BUG?: To help finding correct instances, loops otherwise! *)
Existing Instance R2_Setoid.
Existing Instance R2_EqDec.
Existing Instance R2_RMS.


Instance Info : IsLocation R2 R2 := OnlyLocation.
Instance FDC : first_demonic_choice (Similarity.similarity R2) := FirstChoiceSimilarity.
Instance NoChoice : second_demonic_choice Datatypes.unit := {second_choice_EqDec := unit_eqdec}.

Instance UpdateFun : update_function Datatypes.unit := {update := fun _ pt _ => pt }.
Proof. now repeat intro. Defined.

Instance Update : RigidUpdate.
Proof. split. now intros. Qed.

(** The spectrum is a multiset of positions *)
Notation "!!" := (fun config => spect_from_config config origin).
Notation robogram := (@robogram R2 R2 _ _ _ _ _ MyRobots _).
Notation configuration := (@configuration R2 _ _ _ _).
Notation config_list := (@config_list R2 _ _ _ _).
Notation round := (@round R2 R2 _ _ _ _ _ _ _ _ _ _).
Notation execution := (@execution R2 _ _ _).
Notation demonic_action := (@demonic_action R2 R2 _ _ _ _ _ _).

Add Search Blacklist "Spect.M" "Ring".
Hint Extern 0 (1 =/= 0)%R => apply R1_neq_R0.
Hint Extern 0 (0 =/= 1)%R => symmetry; trivial.
Hint Extern 0 (1 <> 0)%R => apply R1_neq_R0.
Hint Extern 0 (0 <> 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (_ <> _) => match goal with | H : ?x <> ?y |- ?y <> ?x => intro; apply H; now symmetry end.
Hint Extern 0 (~@equiv R _ 1 0)%R => apply R1_neq_R0.
Hint Extern 0 (~@equiv R _ 0 1)%R => intro; apply R1_neq_R0; now symmetry.
Hint Extern 0 (~equiv R _ _ _) =>
  match goal with | H : ~@equiv R _ ?x ?y |- ~@equiv R _ ?y ?x => intro; apply H; now symmetry end.


Implicit Type config : configuration.
Implicit Type da : demonic_action.

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall config (pt : R2),
  (!! config)[pt] = countA_occ _ equiv_dec pt (List.map get_location (config_list config))
 := fun config => @spect_from_config_spec R2 R2 _ _ _ _ _ _ _ config origin.

(** Not true in general as the info may change even if the robot does not move. *)
Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof.
intros r da config Hmove id.
destruct (equiv_dec (round r da config id) (config id)) as [Heq | Heq]; trivial; [].
rewrite <- moving_spec, Hmove in Heq. inversion Heq.
Qed.

Definition nG_non_0 : nG <> 0 := n_non_0.

Lemma spect_non_empty : forall config pt, spect_from_config config pt =/= empty.
Proof.
intros config pt.
rewrite spect_from_config_ignore_snd. intro Habs.
assert (Hn : 0 < n). { generalize n_non_0. omega. }
pose (g := exist _ 0 Hn : G).
specialize (Habs (config (Good g))).
rewrite empty_spec in Habs.
assert (Hin := pos_in_config config origin (Good g)).
simpl in Hin. unfold id, MMultisetInterface.In in Hin. omega.
Qed.

Hint Resolve spect_non_empty.

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
Proof.
intros ? ? Hc ? ? Hr ? ? Hconfig. subst. unfold contained.
setoid_rewrite Hc. setoid_rewrite Hconfig. reflexivity.
Qed.

Instance imprisoned_compat : Proper (equiv ==> Logic.eq ==> equiv ==> iff) imprisoned.
Proof.
unfold imprisoned. repeat intro.
apply Stream.forever_compat; trivial. repeat intro.
apply Stream.instant_compat; trivial.
now apply contained_compat.
Qed.

Instance attracted_compat : Proper (equiv ==> eq ==> equiv ==> iff) attracted.
Proof. intros ? ? Heq ? ? ?. now apply Stream.eventually_compat, imprisoned_compat. Qed.

(** A solution is just convergence property for any demon. *)
Definition solution_SSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : similarity_demon), Fair d →
  forall (ε : R), 0 < ε → exists (pt : R2), attracted pt ε (execute r d config).

Definition solution_FSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : similarity_demon), FullySynchronous d →
  forall (ε : R), 0 < ε → exists (pt : R2), attracted pt ε (execute r d config).

Lemma synchro : ∀ r, solution_SSYNC r → solution_FSYNC r.
Proof.
unfold solution_SSYNC. intros r Hfair config d Hd.
apply Hfair, fully_synchronous_implies_fair; autoclass.
Qed.

Close Scope R_scope.


(** * Proof of correctness of a convergence algorithm with one third of robots byzantine. *)

Definition convergeR2_pgm (s : spectrum) : R2 := barycenter (support s).
(* TODO: support should be changed for elements, once we have SetSpectrum. *)

Instance convergeR2_pgm_compat : Proper (equiv ==> equiv) convergeR2_pgm.
Proof. intros ? ? Heq. unfold convergeR2_pgm. apply barycenter_compat. now rewrite Heq. Qed.

Definition convergeR2 : robogram := {| pgm := convergeR2_pgm |}.


Lemma barycenter_sim : forall (sim : Similarity.similarity R2) s, s =/= empty ->
  barycenter (support (MMultisetExtraOps.map sim s)) == sim (barycenter (support s)).
Proof.
intros sim s Hs.
rewrite map_injective_support; autoclass; try apply Similarity.injective; [].
apply barycenter_sim_morph. now rewrite support_nil.
Qed.

Theorem round_simplify : forall da config,
  round convergeR2 da config
  == fun id => if da.(activate) config id
               then (barycenter (support (spect_from_config config (config id))))
               else config id.
Proof.
intros da config id. unfold round.
destruct_match; try reflexivity; [].
destruct_match.
+ remember (change_frame da config g) as sim.
  change (Bijection.section (Bijection.inverse (first_choice_bijection sim)))
    with (Bijection.section (sim ⁻¹)).
  cbn -[equiv spect_from_config map_config barycenter support RobotInfo.app Similarity.inverse].
  unfold id, convergeR2_pgm.
  rewrite <- barycenter_sim, spect_from_config_map; autoclass.
  assert (Hconfig : map_config (RobotInfo.app (sim ⁻¹)) (map_config (RobotInfo.app sim) config) == config).
  { rewrite map_config_merge; autoclass; []. rewrite <- (map_config_id config) at 2.
    apply map_config_compat; try reflexivity; [].
    simpl. intros ? ? ?. unfold id. now rewrite Bijection.retraction_section. }
  rewrite Hconfig. f_equiv.
+ destruct b; omega.
Qed.

Lemma contained_barycenter : forall c r config,
  contained c r config -> (dist c (barycenter (support (spect_from_config config origin))) <= r)%R.
Proof.
Admitted.

Lemma contained_next : forall da c r config,
  contained c r config -> contained c r (round convergeR2 da config).
Proof.
intros da c r config Hconfig g.
rewrite round_simplify.
destruct_match.
- now apply contained_barycenter.
- auto.
Qed.

Lemma converge_forever : forall d c r config,
  contained c r config -> imprisoned c r (execute convergeR2 d config).
Proof. coinduction Hcorec; auto using contained_next. Qed.


(***********************)
(** *  Final theorem  **)
(***********************)

Theorem convergence_FSYNC : solution_FSYNC convergeR2.
Proof.
intros config d Hfair ε Hε.
eexists (barycenter (support _)).
apply Stream.Later, Stream.Now. rewrite execute_tail.
apply converge_forever.
intro g. unfold round.
destruct Hfair as [Hfair _]; hnf in Hfair.
rewrite Hfair.
rewrite rigid_update.
remember (change_frame (Stream.hd (d : demon)) config g) as sim.
simpl first_choice_bijection; simpl RobotInfo.app; unfold id.
change (pgm convergeR2) with convergeR2_pgm. unfold convergeR2_pgm.
change (Bijection.inverse sim) with (Similarity.sim_f (sim ⁻¹)).
rewrite <- barycenter_sim; auto; [].
rewrite spect_from_config_map; autoclass; [].
rewrite map_config_merge; autoclass.
change (λ x : R2, RobotInfo.app (sim ⁻¹) (sim x)) with (RobotInfo.app (sim ⁻¹ ∘ sim)).
rewrite Similarity.compose_inverse_l, map_config_id.
rewrite spect_from_config_ignore_snd.
transitivity 0%R; try lra; []. apply Req_le.
apply R2_dist_defined_2.
Qed.

Print Assumptions convergence_FSYNC.

Theorem convergence_SSYNC : solution_SSYNC convergeR2.
Proof.
Admitted.
