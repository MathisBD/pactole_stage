Require Import Omega.
Require Export Pactole.Gathering.Definitions.
Require Export Pactole.Spectra.MultisetSpectrum.
Close Scope R_scope.
Set Implicit Arguments.
Typeclasses eauto := (bfs) 5.


(** Gathering Definitions specific to a setting with multiplicities, i.e. a multiset spectrum. *)

Section MultisetGathering.

Context `{Location}.
Context {T : Type}.
Context {RMS : RealMetricSpace location}.
Context `{Names}.
Context {Choice : update_choice T}.
Context {UpdFun : update_function T}.

Notation "!!" := (fun config => spect_from_config config origin : spectrum).

(** When all robots are on two towers of the same height, there is no solution to the gathering problem.
    Therefore, we define these configurations as [invalid]. *)
Definition invalid (config : configuration) :=
     Nat.Even nG /\ nG >=2 /\ exists pt1 pt2 : location, pt1 =/= pt2
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
  forall config : configuration, ~invalid config -> exists pt : location, WillGather pt (execute r d config).

(** **  Generic properties  **)

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall (config : configuration) (pt : location),
  (!! config)[pt] = countA_occ _ equiv_dec pt (List.map get_location (config_list config))
  := fun config => spect_from_config_spec config origin.

(* Only property also used for the flexible FSYNC gathering. *)
(* FIXME: fix the notation failure with "=/=" *)
Lemma spect_non_nil : 2 <= nG -> forall config,
  complement (@equiv (multiset location) _) (!! config) MMultisetInterface.empty.
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

(* FIXME: size gets typed as multiset spectrum instead of multiset location. *)
Lemma invalid_support_length : nB = 0 -> forall config : configuration, invalid config ->
  @size location _ _ _ (!! config) = 2.
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
