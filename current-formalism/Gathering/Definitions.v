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
Require Export Spaces.RealMetricSpace.
Require Pactole.Spaces.Similarity.
Require Export Pactole.Spectra.Definition.
Require Export Pactole.Models.Rigid.
Export Pactole.Spaces.Similarity.Notations.
Close Scope R_scope.
Set Implicit Arguments.


Section GatheringDefinitions.

Context {loc T : Type}.
Context `{RealMetricSpace loc}.
Context `{Names}.

(** The only information available is the current location. *)
Global Instance Info : IsLocation loc loc := OnlyLocation.

Context {Spect : Spectrum loc loc}.
Context {Choice : demonic_choice T}.
Context {UpdFun : update_function T}.

Lemma no_info : forall x y, get_location x == get_location y -> x == y.
Proof. now intros. Qed.

Notation "!!" := (fun config => @spect_from_config loc loc _ _ _ _ _ _ _ config origin).
Notation robogram := (@robogram loc loc _ _ _ _ _ _ _).
Notation configuration := (@configuration loc _ _ _ _).
Notation config_list := (@config_list loc _ _ _ _).
Notation round := (@round loc loc _ _ _ _ _ _ _).
Notation execution := (@execution loc _ _ _).

(** Not true in general as the info may change even if the robot does not move. *)
Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof.
intros r da config Hmove id.
destruct (round r da config id =?= config id) as [Heq | Heq]; trivial; [].
rewrite <- moving_spec, Hmove in Heq. inversion Heq.
Qed.

(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : loc) (config : configuration) := forall g, get_location (config (Good g)) == pt.

(** [Gather pt e] means that at all rounds of (infinite) execution [e],
    robots are gathered at the same position [pt]. *)
Definition Gather (pt: loc) (e : execution) : Prop := Stream.forever (Stream.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition WillGather (pt : loc) (e : execution) : Prop := Stream.eventually (Gather pt) e.

(** Compatibility properties *)
Global Instance gathered_at_compat : Proper (equiv ==> equiv ==> iff) gathered_at.
Proof.
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at.
setoid_rewrite Hconfig. setoid_rewrite Hpt. reflexivity.
Qed.

Global Instance Gather_compat : Proper (equiv ==> equiv ==> iff) Gather.
Proof.
intros pt1 pt2 Hpt. apply Stream.forever_compat, Stream.instant_compat.
intros config1 config2 Hconfig. now rewrite Hpt, Hconfig.
Qed.

Global Instance WillGather_compat : Proper (equiv ==> equiv ==> iff) WillGather.
Proof. intros pt1 pt2 Hpt. apply Stream.eventually_compat. now apply Gather_compat. Qed.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)

Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config : configuration, exists pt : loc, WillGather pt (execute r d config).

End GatheringDefinitions.

(** **  Definitions specific to a multiset spectrum  **)

Section MultisetGathering.

Require Import Pactole.Spectra.MultisetSpectrum.

Context {loc T : Type}.
Context `{RealMetricSpace loc}.
Context `{Names}.
Context {Choice : demonic_choice T}.
Context {UpdFun : update_function T}.

Notation robogram := (@robogram loc loc _ _ _ _ _ _ multiset_spectrum).
Notation configuration := (@configuration loc _ _ _ _).
Notation config_list := (@config_list loc _ _ _ _).
Notation round := (@round loc loc _ _ _ _ _ _ multiset_spectrum).
Notation execution := (@execution loc _ _ _).
Notation "!!" := (fun config => @spect_from_config loc loc _ _ _ _ _ _ _ config origin).

(** When all robots are on two towers of the same height, there is no solution to the gathering problem.
    Therefore, we define these configurations as [invalid]. *)
Definition invalid (config : configuration) :=
     Nat.Even nG /\ nG >=2 /\ exists pt1 pt2, pt1 =/= pt2
  /\ (!! config)[pt1] = Nat.div2 nG /\ (!! config)[pt2] = Nat.div2 nG.

Global Instance invalid_compat : Proper (equiv ==> iff) invalid.
Proof.
intros ? ? Heq. split; intros [HnG [Hle [pt1 [pt2 [Hneq Hpt]]]]];
repeat split; trivial; exists pt1, pt2; split; trivial; now rewrite Heq in *.
Qed.

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [invalid], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithms. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config : configuration, ~invalid config -> exists pt : loc, WillGather pt (execute r d config).

(** **  Generic properties  **)

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall (config : configuration) l,
  (!! config)[l] = countA_occ _ equiv_dec l (List.map get_location (config_list config))
 := fun config => @spect_from_config_spec loc loc _ _ _ _ _ _ _ config origin.

(* Only property also used for the flexible FSYNC gathering. *)
Lemma spect_non_nil : 2 <= nG -> forall config,
complement (@equiv (multiset loc) _) (!! config) MMultisetInterface.empty.
Proof.
simpl spect_from_config. intros HnG config Heq.
assert (Hlgth:= config_list_length config).
assert (Hl : config_list config = nil).
{ apply List.map_eq_nil with _ get_location.
  rewrite <- make_multiset_empty.
  now intro; rewrite Heq. }
rewrite Hl in Hlgth.
simpl in *.
omega.
Qed.

Lemma invalid_support_length : nB = 0 -> forall config, invalid config ->
  size (!! config) = 2.
Proof.
intros HnB config [Heven [HsizeG [pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
rewrite <- (@cardinal_total_sub_eq _ _ _ _ _ (add pt2 (Nat.div2 nG) (singleton pt1 (Nat.div2 nG)))).
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

End MultisetGathering.
