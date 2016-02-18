Require Import Pactole.Preliminary.
Require Import Arith.Div2.
Require Import Omega.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Similarity.
Require Pactole.CommonRealFormalism.
Require Pactole.RigidFormalism.
Require Import Pactole.MultisetSpectrum.
Require Import Morphisms.


Close Scope R_scope.
Set Implicit Arguments.


Module GatheringDefs(Loc : RealMetricSpace)(N : Size).

(** The spectrum is a multiset of positions *)
Module Spect := MultisetSpectrum.Make(Loc)(N).

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".

Module Export Common := CommonRealFormalism.Make(Loc)(N)(Spect).
Module Export Rigid := RigidFormalism.Make(Loc)(N)(Spect)(Common).

Module Sim := Common.Sim.


(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : Loc.t) (conf : Config.t) := forall g : Names.G, Loc.eq (conf (Good g)) pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather (pt: Loc.t) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive WillGather (pt : Loc.t) (e : execution) : Prop :=
  | Now : Gather pt e -> WillGather pt e
  | Later : WillGather pt (execution_tail e) -> WillGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these configurations as [forbidden]. *)
Definition forbidden (config : Config.t) :=
  Nat.Even N.nG /\ N.nG >=2 /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~Loc.eq pt1 pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : Loc.t, WillGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithms. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : Loc.t, WillGather pt (execute r d config).


(** Compatibility properties *)
Instance gathered_at_compat : Proper (Loc.eq ==> Config.eq ==> iff) gathered_at.
Proof.
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at. setoid_rewrite Hpt.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Instance Gather_compat : Proper (Loc.eq ==> eeq ==> iff) Gather.
Proof.
intros pt1 pt2 Hpt e1 e2 He. split.
+ revert e1 e2 He. coinduction rec.
  - rewrite <- Hpt, <- He. now destruct H.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
+ revert e1 e2 He. coinduction rec.
  - rewrite Hpt, He. now destruct H.
  - destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.

Instance WillGather_compat : Proper (Loc.eq ==> eeq ==> iff) WillGather.
Proof.
intros pt1 pt2 Hpt e1 e2 He. split; intro H.
+ revert e2 He. induction H as [e1 | e1 He1 IHe1]; intros e2 He.
  - apply Now. now rewrite <- Hpt, <- He.
  - apply Later. apply IHe1. apply He.
+ revert e1 He. induction H as [e2 | e2 He2 IHe2]; intros e1 He.
  - apply Now. now rewrite Hpt, He.
  - apply Later. apply IHe2. apply He.
Qed.

Instance forbidden_compat : Proper (Config.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [Hle [pt1 [pt2 [Hneq Hpt]]]]]; repeat split; trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

(** **  Generic properties  **)

Lemma spect_non_nil : 2 <= N.nG -> forall conf, ~Spect.eq (!! conf) Spect.empty.
Proof.
intros HnG conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.multiset_empty in Heq.
assert (Hlgth:= Spect.Config.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
omega.
Qed.

End GatheringDefs.