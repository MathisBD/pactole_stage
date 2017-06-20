(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Pactole.Preliminary.
Require Import Arith.Div2.
Require Import Omega.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RealMetricSpace.
Require Import Pactole.Similarity.
Require Pactole.CommonRealFormalism.
Require Pactole.FlexibleFormalism.
Require Import Pactole.SetSpectrum.
Require Import Morphisms.


Close Scope R_scope.
Set Implicit Arguments.


Module FlexGatheringDefs(Loc : RealMetricSpace)(N : Size).

(** The spectrum is a set of positions *)
Module Info := Unit(Loc).
Module Names := Robots.Make(N).
Module Config := Configurations.Make(Loc)(N)(Names)(Info).
Module Spect := SetSpectrum.Make(Loc)(N)(Names)(Info)(Config).

(* Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]"). *)
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist (*"Spect.M"*) "Ring".

Module Export Common := CommonRealFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect).
Module Export Flex := FlexibleFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect)(Common).

Module Sim := Common.Sim.

(* As there is no info inside robots, the location is enough to get all relevant information *)
Lemma no_info : forall rc1 rc2, Loc.eq (Config.loc rc1) (Config.loc rc2) -> Config.eq_RobotConf rc1 rc2.
Proof. intros [? []] [? []]. now split; simpl in *. Qed.

Definition mk_info pt := {| Config.loc := pt; Config.info := tt |}.

(** [gathered_at conf pt] means that in configuration [config] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : Loc.t) (config : Config.t) := forall g, Loc.eq (config (Good g)) pt.

(** [Gather pt e] means that at all rounds of (infinite) execution [e],
    robots are gathered at the same position [pt]. *)
Definition Gather (pt: Loc.t) (e : execution) : Prop := Stream.forever (Stream.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition WillGather (pt : Loc.t) (e : execution) : Prop := Stream.eventually (Gather pt) e.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed. *)
Definition FullSolGathering (r : robogram) (d : demon) delta :=
  forall config, exists pt : Loc.t, WillGather pt (execute delta r d config).

(** Compatibility properties *)
Instance gathered_at_compat : Proper (Loc.eq ==> Config.eq ==> iff) gathered_at.
Proof.
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at. setoid_rewrite Hpt.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Instance Gather_compat : Proper (Loc.eq ==> eeq ==> iff) Gather.
Proof.
intros pt1 pt2 Hpt. apply Stream.forever_compat, Stream.instant_compat.
intros config1 config2 Hconfig. now rewrite Hpt, Hconfig.
Qed.

Instance WillGather_compat : Proper (Loc.eq ==> eeq ==> iff) WillGather.
Proof. intros pt1 pt2 Hpt. apply Stream.eventually_compat. now apply Gather_compat. Qed.

(** **  Generic properties  **)

Lemma spect_non_nil : 2 <= N.nG -> forall conf, ~Spect.eq (!! conf) Spect.M.empty.
Proof.
intros HnG conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.set_empty in Heq.
assert (Hlgth:= Config.list_length conf).
apply List.map_eq_nil in Heq.
rewrite Heq in Hlgth.
simpl in *.
omega.
Qed.

End FlexGatheringDefs.