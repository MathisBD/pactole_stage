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

Require Import Pactole.Preliminary.
Require Import Arith.Div2.
Require Import Omega.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Similarity.
Require Pactole.CommonRealFormalism.
Require Pactole.FlexibleFormalism.
Require Import Pactole.SetSpectrum.
Require Import Morphisms.


Close Scope R_scope.
Set Implicit Arguments.


Module FlexGatheringDefs(Loc : RealMetricSpace)(N : Size).

(** The spectrum is a set of positions *)
Module Spect := SetSpectrum.Make(Loc)(N).

(* Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]"). *)
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist (*"Spect.M"*) "Ring".

Module Export Common := CommonRealFormalism.Make(Loc)(N)(Spect).
Module Export Flex := FlexibleFormalism.Make(Loc)(N)(Spect)(Common).

Module Sim := Common.Sim.


(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : Loc.t) (conf : Config.t) := forall g : Names.G, Loc.eq (conf (Good g)) pt.

(** [Gather pt e] means that at all rounds of (infinite) execution [e],
    robots are gathered at the same position [pt]. *)
Definition Gather (pt: Loc.t) (e : execution) : Prop := Streams.forever (Streams.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition WillGather (pt : Loc.t) (e : execution) : Prop := Streams.eventually (Gather pt) e.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) delta :=
  forall config, exists pt : Loc.t, WillGather pt (execute delta r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithms. *)
Definition ValidSolGathering (r : robogram) (d : demon) delta :=
  forall config, exists pt : Loc.t, WillGather pt (execute delta r d config).


(** Compatibility properties *)
Instance gathered_at_compat : Proper (Loc.eq ==> Config.eq ==> iff) gathered_at.
Proof.
intros pt1 pt2 Hpt config1 config2 Hconfig. unfold gathered_at. setoid_rewrite Hpt.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

Instance Gather_compat : Proper (Loc.eq ==> eeq ==> iff) Gather.
Proof.
intros pt1 pt2 Hpt. apply Streams.forever_compat, Streams.instant_compat.
intros config1 config2 Hconfig. now rewrite Hpt, Hconfig.
Qed.

Instance WillGather_compat : Proper (Loc.eq ==> eeq ==> iff) WillGather.
Proof. intros pt1 pt2 Hpt. apply Streams.eventually_compat. now apply Gather_compat. Qed.

(** **  Generic properties  **)

Lemma spect_non_nil : 2 <= N.nG -> forall conf, ~Spect.eq (!! conf) Spect.M.empty.
Proof.
intros HnG conf Heq.
unfold Spect.from_config in Heq.
rewrite Spect.set_empty in Heq.
assert (Hlgth:= Spect.Config.list_length conf).
rewrite Heq in Hlgth.
simpl in *.
omega.
Qed.

End FlexGatheringDefs.
