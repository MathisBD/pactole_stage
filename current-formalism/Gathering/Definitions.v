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
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Require Import Arith.Div2.
Require Import Omega.
Require Export SetoidDec.
Require Export Pactole.Util.Preliminary.
Require Export Pactole.Setting.
Require Export Pactole.Spectra.Definition.
Require Export Pactole.Spectra.MultisetSpectrum.
Require Export Pactole.Models.Rigid.
Close Scope R_scope.
Set Implicit Arguments.


Section GatheringDefinitions.

Context {loc : Type}.
Context {Sloc : Setoid loc} {Eloc : EqDec Sloc}.
Context {loc_RMS : @RealMetricSpace loc Sloc Eloc}.
Context {Robots : Names}.

Global Instance Info : Information loc Datatypes.unit := Unit _.

Notation "!!" := (@spect_from_config loc Datatypes.unit _ _ _ _ _ _ multiset_spectrum) (at level 1).
Notation robogram := (@robogram loc Datatypes.unit _ _ _ _ Info Robots _).
Notation configuration := (@configuration loc Datatypes.unit _ _ _ _ _ _ _).
Notation config_list := (@config_list loc Datatypes.unit _ _ _ _ _ _ _).
Notation round := (@round loc Datatypes.unit _ _ _ _ _ _ _).
Notation execution := (@execution loc Datatypes.unit _ _ _ _ _).

(** There is no meaningful information inside Info.t. *)
Lemma no_info : forall rc1 rc2 : loc * Datatypes.unit, fst rc1 == fst rc2 -> rc1 == rc2.
Proof. intros [? []] [? []] Heq; split; simpl in *; auto. Qed.

(** Not true in general as the info may change even if the robot does not move. *)
Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof.
intros r da config Hmove id.
destruct (round r da config id =?= config id) as [Heq | Heq]; trivial; [].
rewrite <- moving_spec, Hmove in Heq. inversion Heq.
Qed.

(** The full information for a robot only depends on its location. *)
Definition mk_info l : loc * _ := (l, tt).

(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : loc) (config : configuration) := forall g : G, fst (config (Good g)) == pt.

(** [Gather pt e] means that at all rounds of (infinite) execution [e],
    robots are gathered at the same position [pt]. *)
Definition Gather (pt: loc) (e : execution) : Prop := Stream.forever (Stream.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition WillGather (pt : loc) (e : execution) : Prop := Stream.eventually (Gather pt) e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these configurations as [invalid]. *)
Definition invalid (config : configuration) :=
     Nat.Even nG /\ nG >=2 /\ exists pt1 pt2, pt1 =/= pt2
  /\ (!! config)[pt1] = Nat.div2 nG /\ (!! config)[pt2] = Nat.div2 nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)

Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config : configuration, exists pt : loc, WillGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [invalid], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithms. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config : configuration, ~invalid config -> exists pt : loc, WillGather pt (execute r d config).


(** Compatibility properties *)
Global Instance gathered_at_compat : Proper (equiv ==> equiv ==> iff) gathered_at.
Proof.
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at.
split; intros H g; specialize (H g); specialize (Hconfig (Good g));
destruct (config2 (Good g)) eqn:c2, (config1 (Good g)) eqn:c1 in *;
rewrite <- Hpt, <- H || rewrite Hpt, <- H; hnf in Hconfig; intuition.
Qed.

Global Instance Gather_compat : Proper (equiv ==> equiv ==> iff) Gather.
Proof.
intros pt1 pt2 Hpt. apply Stream.forever_compat, Stream.instant_compat.
intros config1 config2 Hconfig. now rewrite Hpt, Hconfig.
Qed.

Global Instance WillGather_compat : Proper (equiv ==> equiv ==> iff) WillGather.
Proof. intros pt1 pt2 Hpt. apply Stream.eventually_compat. now apply Gather_compat. Qed.

Global Instance invalid_compat : Proper (equiv ==> iff) invalid.
Proof.
intros ? ? Heq. split; intros [HnG [Hle [pt1 [pt2 [Hneq Hpt]]]]];
repeat split; trivial; exists pt1, pt2; split; trivial; now rewrite Heq in *.
Qed.

(** **  Generic properties  **)

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall (config : configuration) l,
  (!! config)[l] = countA_occ _ equiv_dec l (List.map fst (config_list config))
 := @spect_from_config_spec loc Datatypes.unit _ _ _ _ _ _ _.

Lemma spect_non_nil : 2 <= nG -> forall config : configuration, ~!! config == MMultisetInterface.empty.
Proof.
simpl spect_from_config. intros HnG conf Heq.
assert (Hlgth:= config_list_length conf).
assert (Hl : config_list conf = nil).
{ apply List.map_eq_nil with _ fst. now rewrite <- make_multiset_empty, Heq. }
rewrite Hl in Hlgth.
simpl in *.
omega.
Qed.

Lemma invalid_support_length : nB = 0 -> forall config, invalid config ->
  size (!! config) = 2.
Proof.
intros HnB config [Heven [HsizeG [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
rewrite <- (@cardinal_total_sub_eq _ _ _ _ _ (add pt2 (Nat.div2 nG) (singleton pt1 (Nat.div2 nG))) (!! config)).
+ rewrite size_add.
  destruct (In_dec pt2 (singleton pt1 (Nat.div2 nG))) as [Hin | Hin].
  - exfalso. rewrite In_singleton in Hin.
    destruct Hin. now elim Hdiff.
  - rewrite size_singleton; trivial; [].
    apply Exp_prop.div2_not_R0. apply HsizeG.
  - apply Exp_prop.div2_not_R0. apply HsizeG.
+ intro pt. destruct (pt =?= pt2) as [Heq2 | Heq2], (pt =?= pt1) as [Heq1 | Heq1].
  - rewrite Heq1, Heq2 in *. now elim Hdiff.
  - rewrite add_spec, singleton_spec.
    do 2 destruct_match; try contradiction; [].
    simpl.
    rewrite Heq2.
    now apply Nat.eq_le_incl.
  - rewrite add_other, singleton_spec; auto; [].
    destruct_match; try contradiction; [].
    rewrite Heq1.
    now apply Nat.eq_le_incl.
  - rewrite add_other, singleton_spec; auto; [].
    destruct_match; try contradiction; [].
    auto with arith.
+ rewrite cardinal_add, cardinal_singleton, cardinal_spect_from_config.
  rewrite HnB, plus_0_r. now apply even_div2.
Qed.

End GatheringDefinitions.
