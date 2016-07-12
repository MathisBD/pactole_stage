(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Pactole.CommonFormalism.
Require Pactole.FlexibleFormalism.
Require Import Pactole.SetSpectrum.
Require Import Pactole.Lexprod.
Require Import Pactole.Gathering.InR2.R2geometry.
Require Import Pactole.Gathering.Definitions.


Import Permutation.
Set Implicit Arguments.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR2.

(** **  Framework of the correctness proof: a finite set with at least three elements  **)

Parameter nG: nat.
Hypothesis Hyp_nG : (2 <= nG)%nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.

(** We instantiate in our setting the generic definitions of the gathering problem. *)
Module Defs := Definitions.GatheringDefs(R2)(N).
Import Defs.

Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

Lemma Config_list_alls : forall pt, Spect.Config.list (fun _ => pt) = alls pt N.nG.
Proof.
intro. rewrite Config.list_spec, map_cst.
setoid_rewrite Spect.Names.names_length. unfold N.nB. now rewrite plus_0_r.
Qed.

Lemma map_sim_support : forall (sim : Sim.t) s,
  Permutation (Spect.support (Spect.map sim s)) (map sim (Spect.support s)).
Proof.
intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_support.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.empty.
Proof. apply spect_non_nil. assert (Hle := Hyp_nG). unfold N.nG. omega. Qed.

Lemma support_non_nil : forall config, Spect.support (!! config) <> nil.
Proof. intros config Habs. rewrite Spect.support_nil in Habs. apply (spect_non_nil _ Habs). Qed.

Lemma gathered_at_dec : forall conf pt, {gathered_at pt conf} + {~gathered_at pt conf}.
Proof.
intros conf pt.
destruct (forallb (fun id => R2dec_bool (conf id) pt) Names.names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. rewrite <- R2dec_bool_true_iff. apply Hall. apply Names.In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  destruct id as [g | b]; try now apply Fin.case0; exact b. intro Habs. specialize (Habs g).
  rewrite negb_true_iff, R2dec_bool_false_iff in Heq. contradiction.
Qed.

(*
(* FIXME: These three definitions: gathered_at, gather and WillGather
   should be shared by all our proofs about gathering (on Q, R, R2,
   for impossibility and possibility proofs). Shouldn't they be in a
   module? We could even add a generic notion of forbidden
   configurations. *)


(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (conf : Config.t) := forall g : Names.G, conf (Good g) = pt.

Instance gathered_at_compat : Proper (eq ==> Config.eq ==> iff) gathered_at.
Proof.
intros ? pt ? config1 config2 Hconfig. subst. unfold gathered_at.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
Definition gather (pt : R2.t) (e : execution) : Prop := Streams.forever (Streams.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition willGather (pt : R2.t) (e : execution) : Prop := Streams.eventually (gather pt) e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these configurations as [forbidden]. *)
Definition forbidden (config : Config.t) :=
  Nat.Even N.nG /\ N.nG >=2 /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : R2.t, willGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R2.t, willGather pt (execute r d config).


Instance forbidden_compat : Proper (Config.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [? [pt1 [pt2 [Hneq Hpt]]]]];(split;[|split]); trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.
*)

(** **  Definition of the robogram  **)

Open Scope R_scope.

(** The robogram solving the gathering problem in R². *)
Definition ffgatherR2_pgm (s : Spect.t) : R2.t :=
  let spect := Spect.support s in
  match spect with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* gathered *)
    | _ :: _ :: _ =>
      barycenter spect
  end.

Instance ffgatherR2_pgm_compat : Proper (Spect.eq ==> R2.eq) ffgatherR2_pgm.
Proof.
intros s1 s2 Hs. unfold ffgatherR2_pgm.
assert (Hsize : length (Spect.support s1) = length (Spect.support s2)).
{ f_equiv. now do 2 f_equiv. }
destruct (Spect.support s1) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support s2) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ apply Spect.support_compat in Hs. rewrite Hs1, Hs2 in Hs.
  rewrite PermutationA_Leibniz in Hs. apply Permutation_length_1_inv in Hs. now inversion Hs.
+ apply Spect.support_compat in Hs.
  apply barycenter_compat.
  rewrite Hs1 in Hs.
  rewrite Hs2 in Hs.
  assumption.  
Qed.

Definition ffgatherR2 : robogram := {| pgm := ffgatherR2_pgm |}.

Close Scope R_scope.


(** **  Decreasing measure ensuring termination  **)

(** ***  Global decreasing measure  **)

(** It is a lexicographic order on the index of the type of config + the number of robots that should move. *)
(**
  -  ]   Gathered: no need
  - 0]   Regular case
*)

Open Scope R_scope.

(* Coercion Spect.Names.names : list Spect.Names.Internals.ident >-> list Spect.Names.ident. *)

Definition max_dist_R2_pt_list (pt: R2.t) (l: list R2.t) : R :=
  fold_right (fun pt1 max => Rmax (R2.dist pt pt1) max) 0 l.

Lemma max_dist_R2_pt_list_le :
  forall pt l pt1,
    In pt1 l -> R2.dist pt pt1 <= max_dist_R2_pt_list pt l.
Proof.
  intros pt l pt1 Hin1.
  induction l.
  + elim Hin1.
  + destruct Hin1.
    - subst. unfold max_dist_R2_pt_list.
      simpl.
      apply Rmax_l.
    - unfold max_dist_R2_pt_list. simpl.
      unfold max_dist_R2_pt_list in IHl. apply IHl in H.
      apply (Rle_trans _ _ _ H).
      apply Rmax_r.
Qed.

Lemma max_dist_not_first :
  forall pt pt1 l,
    max_dist_R2_pt_list pt (pt1 :: l) <> R2.dist pt pt1 ->
    l <> nil /\
    max_dist_R2_pt_list pt (pt1 :: l) = max_dist_R2_pt_list pt l.
Proof.
  intros pt pt1 l Hnotfirst.
  unfold max_dist_R2_pt_list in Hnotfirst.
  simpl in Hnotfirst.
  unfold Rmax at 1 in Hnotfirst.
  unfold max_dist_R2_pt_list at 1. simpl.
  unfold Rmax at 1.
  destruct (Rle_dec (R2.dist pt pt1)
                  (fold_right (fun (pt1 : R2.t) (max : R) => Rmax (R2.dist pt pt1) max) 0 l)).
  split.
  intro.
  apply Hnotfirst.
  rewrite H in *.
  simpl in *.
  assert (0 <= R2.dist pt pt1).
  apply R2.dist_pos.
  destruct H0.
  assert (R2.dist pt pt1 < R2.dist pt pt1).
  now apply Rle_lt_trans with (r2 := 0).
  exfalso.
  apply (Rlt_irrefl _ H1).
  assumption.
  reflexivity.
  now elim Hnotfirst.
Qed.
  
Lemma max_dist_R2_pt_list_ex :
  forall pt l,
    l <> nil ->
    exists pt1, In pt1 l /\ R2.dist pt pt1 = max_dist_R2_pt_list pt l.
Proof.
  intros pt l Hl.
  induction l.
  + now elim Hl.
  + destruct (Req_dec (R2.dist pt a) (max_dist_R2_pt_list pt (a :: l))).
    - exists a.
      split.
      now left.
      assumption.
    - assert (Hmax: max_dist_R2_pt_list pt (a::l) = max_dist_R2_pt_list pt l).
      { apply max_dist_not_first.
        intro. apply H. now rewrite H0. }
      assert (Hlnotnil: l <> nil).
      { generalize (max_dist_not_first pt a l).
        intro.
        apply H0.
        intro. apply H. now rewrite H1. }
      destruct (IHl Hlnotnil). destruct H0.
      exists x.
      split.
      now right.
      now rewrite Hmax.
Qed.      
      
Definition max_dist_R2_list_list (l1: list R2.t) (l2: list R2.t): R :=
  fold_right (fun pt0 max => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1.

Lemma max_dist_R2_list_list_le :
  forall pt1 l1 pt2 l2,
    In pt1 l1 -> In pt2 l2 -> R2.dist pt1 pt2 <= max_dist_R2_list_list l1 l2.
Proof.
  intros pt1 l1 pt2 l2 Hin1 Hin2.
  induction l1.
  + elim Hin1.
  + destruct Hin1.
    - subst. unfold max_dist_R2_list_list. simpl.
      apply Rle_trans with (r2 := max_dist_R2_pt_list pt1 l2).
      now apply max_dist_R2_pt_list_le.
      now apply Rmax_r.
    - unfold max_dist_R2_list_list. simpl.
      apply IHl1 in H.
      apply (Rle_trans _ _ _ H).
      now apply Rmax_l.
Qed.

Lemma max_dist_R2_list_list_ex :
  forall l1 l2,
    l1 <> nil ->
    l2 <> nil ->
    exists pt1 pt2, In pt1 l1 /\ In pt2 l2 /\ R2.dist pt1 pt2 = max_dist_R2_list_list l1 l2.
Proof.
  intros l1 l2 Hl1notnil Hl2notnil.
  induction l1.
  + now elim Hl1notnil.
  + unfold max_dist_R2_list_list.
    simpl.
    unfold Rmax at 1.
    destruct (Rle_dec (fold_right (fun (pt0 : R2.t) (max : R) => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1)
         (max_dist_R2_pt_list a l2)).
    - exists a.
      destruct (max_dist_R2_pt_list_ex a Hl2notnil) as [? [? ?]].
      exists x. split.
      now left.
      now split.
    - clear Hl1notnil.
      assert (Hl1notnil: l1 <> nil).
      { intro. apply n. subst. simpl.
        induction l2.
        unfold max_dist_R2_pt_list. simpl. apply Rle_refl.
        simpl. apply Rle_trans with (r2 := R2.dist a a0).
        apply R2.dist_pos.
        apply Rmax_l. }
      destruct (IHl1 Hl1notnil) as [? [? [? [? ?]]]].
      exists x, x0.
      split.
      now right.
      now split.
Qed.
      
Lemma max_dist_spect:
  forall (spect: Spect.t),
    Spect.support spect <> nil ->
    exists (dm: R),
      (forall pt0 pt1, In pt0 (Spect.support spect) ->
                       In pt1 (Spect.support spect) ->
                       R2.dist pt0 pt1 <= dm)
      /\
      (exists pt0 pt1, In pt0 (Spect.support spect)
                       /\ In pt1 (Spect.support spect)
                       /\ R2.dist pt0 pt1 = dm).
Proof.
  intros.
  exists (max_dist_R2_list_list (Spect.support spect) (Spect.support spect)).
  split.
  + intros pt0 pt1 Hin0 Hin1.
    now apply max_dist_R2_list_list_le.
  + now apply max_dist_R2_list_list_ex.
Qed.

Lemma max_dist_exists :
  forall (conf: Config.t),
  exists (dm: R),
    forall r1 r2, R2.dist (conf r1) (conf r2) <= dm /\ exists r1 r2, R2.dist (conf r1) (conf r2) = dm.
Proof.
  intros.
  set (rlist := (*Spect.Names.Internals.fin_map*) Spect.Names.names).
  set (dm_candidate := fold_left (fun max r0 =>
                                    Rmax (fold_left (fun max r1 => Rmax (R2.dist (conf r0) (conf r1)) max) rlist 0) max)
                                 rlist 0).
  assert (forall r1 r2, In r1 rlist -> In r2 rlist -> R2.dist (conf r1) (conf r2) <= dm_candidate).
  induction rlist.
  intros ? ? Hin; elim Hin.
  intros r1 r2 Hin1 Hin2.
  destruct (Spect.Names.eq r1 a).
  
  exists (fold_left (fun max r0 =>
                       Rmax (fold_left (fun max r1 => Rmax (R2.dist (conf r0) (conf r1)) max) rlist 0) max)
                    rlist 0).
  intros.
  split.
  
  
Definition max_dist_conf (conf: Config.t) : R :=
  

Function measure (s : Spect.t) : nat * nat :=
  match Spect.support (Spect.max s) with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => (0, N.nG -  s[pt]) (* majority *)
    | _ :: _ :: _ =>
      match on_SEC (Spect.support s) with
        | nil | _ :: nil => (0, 0) (* impossible cases *)
        | pt1 :: pt2 :: nil => (* diameter case *)
            if is_clean s then (1, measure_clean s) else (2, measure_dirty s)
        | pt1 :: pt2 :: pt3 :: nil => (* triangle case *)
            if is_clean s then (3, measure_clean s) else (4, measure_dirty s)
        | _ => (* general case *) if is_clean s then (5, measure_clean s) else (6, measure_dirty s)
      end
  end.

Instance measure_clean_compat : Proper (Spect.eq ==> Logic.eq) measure_clean.
Proof. intros ? ? Heq. unfold measure_clean. now rewrite Heq. Qed.

Instance measure_dirty_compat : Proper (Spect.eq ==> Logic.eq) measure_dirty.
Proof. intros ? ? Heq. unfold measure_dirty. now rewrite Heq. Qed.

Instance measure_compat : Proper (Spect.eq ==> Logic.eq) measure.
Proof.
intros s1 s2 Hs. unfold measure.
assert (Hsize : length (Spect.support (Spect.max s1)) = length (Spect.support (Spect.max s2))).
{ f_equiv. now do 2 f_equiv. }
destruct (Spect.support (Spect.max s1)) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.support (Spect.max s2)) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ rewrite Hs. repeat f_equal.
  rewrite <- (PermutationA_1 _). rewrite <- Hs1, <- Hs2. rewrite Hs. reflexivity.
+ clear -Hs.
  assert (Hperm : Permutation (on_SEC (Spect.support s1)) (on_SEC (Spect.support s2))).
  { now rewrite <- PermutationA_Leibniz, Hs. }
  destruct (on_SEC (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1.
  - apply Permutation_nil in Hperm. now rewrite Hperm.
  - apply Permutation_length_1_inv in Hperm. now rewrite Hperm.
  - apply Permutation_length_2_inv in Hperm.
    destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial;
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (on_SEC (Spect.support s2)) =3%nat) by now rewrite <- Hperm.
    destruct (on_SEC (Spect.support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite Hs. destruct (is_clean s2); f_equal; now rewrite Hs.
  - assert (length (on_SEC (Spect.support s2)) = 4 + length l)%nat by now rewrite <- Hperm.
    destruct (on_SEC (Spect.support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega.
    rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs.
Qed.


Definition lt_config x y := lexprod lt lt (measure (!! x)) (measure (!! y)).

Lemma wf_lt_conf: well_founded lt_config.
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply wf_lexprod; apply lt_wf.
Qed.

Instance lt_conf_compat: Proper (Config.eq ==> Config.eq ==> iff) lt_config.
Proof.
  intros conf1 conf1' heq1 conf2 conf2' heq2.
  unfold lt_config.
  rewrite <- heq1, <- heq2.
  reflexivity.
Qed.

(** ***  The robogram is invariant by a change of the frame of reference  **)

(** We first prove how the functions used by the robogram are affected by a change of the frame of reference. *)
Definition map_triangle_type f t :=
  match t with
  | Isosceles p => Isosceles (f p)
  | _ => t
  end.

Definition sim_circle (sim:Sim.t) c :=
  {| center := sim c.(center) ; radius := sim.(Sim.zoom) * (c.(radius)) |}.

Lemma classify_triangle_morph :
  forall (sim : Sim.t) pt1 pt2 pt3, classify_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = map_triangle_type sim (classify_triangle pt1 pt2 pt3).
Proof.
  intros sim pt1 pt2 pt3.
  unfold classify_triangle at 1.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *; try apply Sim.zoom_non_null.
  functional induction (classify_triangle pt1 pt2 pt3);
  repeat rewrite ?e, ?e0, ?e1, ?(sim.(Sim.dist_prop)), ?Rdec_bool_mult_l; try reflexivity;
  try apply Sim.zoom_non_null.
Qed.

Lemma on_circle_morph :
  forall (sim : Sim.t) pt c, on_circle (sim_circle sim c) (sim pt) = on_circle c pt.
Proof.
  intros sim pt c.
  unfold on_circle at 1.
  unfold sim_circle.
  simpl.
  setoid_rewrite (sim.(Sim.dist_prop)).
  rewrite Rdec_bool_mult_l in *;try apply Sim.zoom_non_null.
  reflexivity.
Qed.

Lemma enclosing_circle_morph :
  forall (sim : Sim.t) c l, enclosing_circle (sim_circle sim c) (List.map sim l) <-> enclosing_circle c l.
Proof.
  intros sim c l.
  unfold enclosing_circle.
  unfold sim_circle.
  simpl.
  setoid_rewrite in_map_iff.
  split;intro h.
  - intros x h'.
    specialize (h (sim x)).
    setoid_rewrite (sim.(Sim.dist_prop)) in h.
    apply Rmult_le_reg_l in h;auto.
    + apply Sim.zoom_pos.
    + eauto.
  - intros x H.
    destruct H as [x' [hsim hIn]].
    subst.
    rewrite (sim.(Sim.dist_prop)).
    eapply Rmult_le_compat_l in h;eauto.
    apply Rlt_le, Sim.zoom_pos.
Qed.

Lemma SEC_morph : forall (sim:Sim.t) l, SEC (List.map sim l) = sim_circle sim (SEC l).
Proof.
intros sim l. symmetry. apply SEC_unicity.
+ intros pt' Hin. rewrite in_map_iff in Hin. destruct Hin as [pt [Hpt Hin]]. subst pt'.
  unfold sim_circle. simpl. rewrite sim.(Sim.dist_prop).
  apply Rmult_le_compat_l.
  - apply Rlt_le. apply Sim.zoom_pos.
  - now apply SEC_spec1.
+ assert ( 0 < / (Sim.zoom sim))%R by apply Rinv_0_lt_compat, Sim.zoom_pos.
  unfold sim_circle. simpl. apply Rmult_le_reg_l with (/ (Sim.zoom sim))%R; trivial; [].
  rewrite <- Rmult_assoc. rewrite Rinv_l; try (now assert (Hpos := Sim.zoom_pos sim); lra); [].
  change (/ Sim.zoom sim * radius (SEC (map sim l)))%R with (radius (sim_circle (sim ⁻¹) (SEC (map sim l)))).
  ring_simplify. apply SEC_spec2.
  intros pt Hin. replace pt with ((sim ⁻¹) (sim pt)).
  - change (center (sim_circle (sim ⁻¹) (SEC (map sim l)))) with ((sim ⁻¹) (center (SEC (map sim l)))).
    rewrite (Sim.dist_prop (sim ⁻¹)). simpl. apply Rmult_le_reg_l with (/ (Sim.zoom sim))%R; trivial.
    do 2 (apply Rmult_le_compat_l; try lra; []).
    apply SEC_spec1. now apply in_map.
  - simpl. apply (Similarity.retraction_section _).
Qed.

Lemma barycenter_3_morph: forall (sim : Sim.t) pt1 pt2 pt3,
  barycenter_3_pts (sim pt1) (sim pt2) (sim pt3) = sim (barycenter_3_pts pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. eapply bary3_unique.
+ apply bary3_spec.
+ intro p. change p with (Sim.id p). rewrite <- (Sim.compose_inverse_r sim).
  change ((Sim.compose sim (sim ⁻¹)) p) with (sim ((sim ⁻¹) p)).
  repeat rewrite sim.(Sim.dist_prop), R_sqr.Rsqr_mult. repeat rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  - apply Rle_0_sqr.
  - apply bary3_spec.
Qed.

Lemma opposite_of_max_side_morph : forall (sim : Sim.t) pt1 pt2 pt3,
  opposite_of_max_side (sim pt1) (sim pt2) (sim pt3) = sim (opposite_of_max_side pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold opposite_of_max_side.
repeat rewrite (sim.(Sim.dist_prop)).
assert (Hconf : (0 < Sim.zoom sim)%R) by apply Sim.zoom_pos.
repeat rewrite Rle_bool_mult_l; trivial.
repeat match goal with
  | |- context[Rle_bool ?x ?y] => destruct (Rle_bool x y)
end; reflexivity.
Qed.

Lemma target_triangle_morph:
  forall (sim : Sim.t) pt1 pt2 pt3, target_triangle (sim pt1) (sim pt2) (sim pt3)
                                  = sim (target_triangle pt1 pt2 pt3).
Proof.
intros sim pt1 pt2 pt3. unfold target_triangle.
rewrite classify_triangle_morph.
destruct (classify_triangle pt1 pt2 pt3);simpl;auto.
- apply barycenter_3_morph.
- apply opposite_of_max_side_morph.
Qed.

Lemma R2_is_middle_morph : forall x y C (sim:Sim.t), is_middle x y C -> (is_middle (sim x) (sim y) (sim C)).
Proof.
  intros x y C sim hmid.
  red.
  intros p.
  unfold is_middle in hmid.
  rewrite <- (@Similarity.section_retraction _ _ _ (sim.(Sim.sim_f)) p).
  setoid_rewrite sim.(Sim.dist_prop).
  setoid_rewrite R_sqr.Rsqr_mult.
  setoid_rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  - apply Rle_0_sqr.
  - apply hmid.
Qed.


Lemma R2_middle_morph : forall x y (sim:Sim.t), (R2.middle (sim x) (sim y))%R2 = sim ((R2.middle x y))%R2.
Proof.
intros x y sim. symmetry. apply middle_is_R2middle, R2_is_middle_morph, middle_spec.
Restart.
  intros x y sim.
  generalize (@middle_spec x y).
  intro hmidlxy.
  generalize (@middle_spec (sim x) (sim y)).
  intro hmidsimxy.
  assert (is_middle (sim x) (sim y) (sim (R2.middle x y))).
  { apply R2_is_middle_morph.
    auto. }
  apply is_middle_uniq with (sim x) (sim y); assumption.
Qed.

Lemma R2_is_bary3_morph : forall x y z C (sim : Sim.t),
  is_barycenter_3_pts x y z C -> (is_barycenter_3_pts (sim x) (sim y) (sim z) (sim C)).
Proof.
  intros x y z C sim hmid.
  red.
  intros p.
  unfold is_barycenter_3_pts in hmid.
  rewrite <- (@Similarity.section_retraction _ _ _ (sim.(Sim.sim_f)) p).
  setoid_rewrite sim.(Sim.dist_prop).
  setoid_rewrite R_sqr.Rsqr_mult.
  repeat setoid_rewrite <- Rmult_plus_distr_l.
  apply Rmult_le_compat_l.
  - apply Rle_0_sqr.
  - apply hmid.
Qed.

Lemma R2_bary3_morph : forall x y z (sim : Sim.t),
  (barycenter_3_pts (sim x) (sim y) (sim z))%R2 = sim ((barycenter_3_pts x y z))%R2.
Proof.
  intros x y z sim.
  generalize (@bary3_spec x y z).
  intro hmidlxy.
  generalize (@bary3_spec (sim x) (sim y) (sim z)).
  intro hmidsimxy.
  assert (is_barycenter_3_pts (sim x) (sim y) (sim z) (sim (barycenter_3_pts x y z))).
  { apply R2_is_bary3_morph.
    auto. }
  apply bary3_unique with (sim x) (sim y) (sim z);assumption.
Qed.

Lemma target_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> target (Spect.map sim s) = sim (target s).
Proof.
intros sim s hnonempty. unfold target.
assert (Hperm : Permutation (List.map sim (on_SEC (Spect.support s))) (on_SEC (Spect.support (Spect.map sim s)))).
{ assert (Heq : on_SEC (Spect.support s)
              = filter (fun x => on_circle (sim_circle sim (SEC (Spect.support s))) (sim x)) (Spect.support s)).
  { apply filter_extensionality_compat; trivial. repeat intro. subst. now rewrite on_circle_morph. }
  rewrite Heq. rewrite <- filter_map.
  rewrite <- PermutationA_Leibniz. rewrite <- Spect.map_injective_support; trivial.
  - unfold on_SEC. rewrite filter_extensionality_compat; try reflexivity.
    repeat intro. subst. f_equal. symmetry. rewrite <- SEC_morph.
    apply SEC_compat. apply map_sim_support.
  - intros ? ? H. now rewrite H.
  - apply Sim.injective. }
rewrite <- PermutationA_Leibniz in Hperm.
assert (Hlen := PermutationA_length Hperm).
destruct ((on_SEC (Spect.support s))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hn,
         (on_SEC (Spect.support (Spect.map sim s))) as [| pt1' [| pt2' [| pt3' [| ? ?]]]];
simpl in *; try (omega || reflexivity); clear Hlen.
+ rewrite on_SEC_nil in Hn. contradiction.
+ now rewrite (PermutationA_1 _) in Hperm.
+ change (sim (center (SEC (Spect.support s)))) with (center (sim_circle sim (SEC (Spect.support s)))).
  f_equal. rewrite <- SEC_morph. apply SEC_compat, map_sim_support.
+ rewrite PermutationA_Leibniz in Hperm. rewrite <- (target_triangle_compat Hperm). apply target_triangle_morph.
+ change (sim (center (SEC (Spect.support s)))) with (center (sim_circle sim (SEC (Spect.support s)))).
  f_equal. rewrite <- SEC_morph. apply SEC_compat, map_sim_support.
Qed.

Corollary SECT_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> Permutation (SECT (Spect.map sim s)) (map sim (SECT s)).
Proof.
intros sim s s_nonempty. unfold SECT.
rewrite (target_morph _ s_nonempty). simpl. constructor.
transitivity (filter (on_circle (SEC (Spect.support (Spect.map sim s)))) (map sim (Spect.support s))).
+ rewrite <- PermutationA_Leibniz. apply (filter_PermutationA_compat _).
  - repeat intro. now subst.
  - rewrite PermutationA_Leibniz. apply map_sim_support.
+ rewrite filter_map.
  cut (map sim (filter (fun x => on_circle (SEC (Spect.support (Spect.map sim s))) (sim x)) (Spect.support s))
       = (map sim (on_SEC (Spect.support s)))).
  - intro Heq. now rewrite Heq.
  - f_equal. apply filter_extensionality_compat; trivial.
    repeat intro. subst. now rewrite map_sim_support, SEC_morph, on_circle_morph.
Qed.

Lemma is_clean_morph : forall (sim : Sim.t) s,
    Spect.support s <> nil -> is_clean (Spect.map sim s) = is_clean s.
Proof.
intros sim s s_nonempty. unfold is_clean.
destruct (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support (Spect.map sim s)) (SECT (Spect.map sim s))) eqn:Hx,
         (inclA_bool R2.eq_equiv R2.eq_dec (Spect.support s) (SECT s)) eqn:Hy;
trivial; rewrite ?inclA_bool_true_iff, ?inclA_bool_false_iff, ?inclA_Leibniz in *.
- elim Hy. intros x Hin. apply (in_map sim) in Hin. rewrite <- map_sim_support in Hin.
  apply Hx in Hin. rewrite SECT_morph, in_map_iff in Hin;auto.
  destruct Hin as [x' [Heq ?]]. apply Sim.injective in Heq. now rewrite <- Heq.
- elim Hx. intros x Hin. rewrite SECT_morph;auto. rewrite map_sim_support in Hin.
  rewrite in_map_iff in *. destruct Hin as [x' [? Hin]]. subst. exists x'. repeat split. now apply Hy.
Qed.

(** We express the behavior of the algorithm in the global (demon) frame of reference. *)
Theorem round_simplify : forall da conf,
    Config.eq (round gatherR2 da conf)
              (fun id => match da.(step) id with
                         | None => conf id
                         | Some f =>
                           let s := !! conf in
                           match Spect.support (Spect.max s) with
                           | nil => conf id (* only happen with no robots *)
                           | pt :: nil => pt (* majority tower *)
                           | _ => if is_clean s then target s else
                                    if mem R2.eq_dec (conf id) (SECT s) then conf id else target s
                           end
                         end).
Proof.
intros da conf id. hnf. unfold round.
assert (supp_nonempty:=support_non_nil conf).
destruct (step da id) as [f |] eqn:Hstep; trivial.
destruct id as [g | b]; try now eapply Fin.case0; exact b.
remember (conf (Good g)) as pt. remember (f pt) as sim.
assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. }
simpl pgm. unfold gatherR2_pgm.
assert (Hperm : Permutation (map sim (Spect.support (Spect.max (!! conf))))
                            (Spect.support (Spect.max (!! (Config.map sim conf)))))
  by (now rewrite <- map_sim_support, <- PermutationA_Leibniz, <- max_morph, Spect.from_config_map).
assert (Hlen := Permutation_length Hperm).
destruct (Spect.support (Spect.max (!! conf))) as [| pt1 [| pt2 l]] eqn:Hmax,
         (Spect.support (Spect.max (!! (Config.map sim conf)))) as [| pt1' [| pt2' l']];
simpl in Hlen; discriminate || clear Hlen.
- rewrite Spect.support_nil, Spect.max_empty in Hmax. elim (spect_non_nil _ Hmax).
- simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'. now apply Sim.compose_inverse_l.
- rewrite <- Spect.from_config_map, is_clean_morph; trivial.
  + destruct (is_clean (!! conf)).
    * rewrite <- Spect.from_config_map, target_morph; trivial; auto.
      now apply Sim.compose_inverse_l.
    * rewrite <- (Sim.center_prop sim). rewrite Heqsim at 3. rewrite (step_center da _ _ Hstep).
      assert (Hperm' : PermutationA eq (SECT (!! (Config.map sim conf))) (map sim (SECT (!! conf)))).
      { rewrite PermutationA_Leibniz, <- SECT_morph;auto.
        f_equiv. now rewrite Spect.from_config_map. }
    rewrite Hperm'. rewrite (mem_injective_map _); trivial; try (now apply Sim.injective); [].
    destruct (mem R2.eq_dec pt (SECT (!! conf))).
      -- rewrite <- (Sim.center_prop sim), Heqsim, (step_center _ _ _ Hstep). now apply Sim.compose_inverse_l.
      -- simpl. rewrite <- sim.(Similarity.Inversion), <- target_morph;auto.
         f_equiv. now apply Spect.from_config_map.
Qed.

(** ****  Specialization of [round_simplify] in the three main cases of the robogram  **)

(** If we have a majority tower, every robot goes there. **)
Lemma round_simplify_Majority : forall da config pt,
    MajTower_at pt config ->
    Config.eq (round gatherR2 da config)
              (fun id => match step da id with
                      | None => config id
                      | Some _ => pt
                         end).
Proof.
intros da config pt Hmaj id. rewrite round_simplify; auto.
destruct (step da id); try reflexivity. cbv zeta.
rewrite MajTower_at_equiv in Hmaj. now rewrite Hmaj.
Qed.

(** If the configuration is clean, every robot goes to the target. *)
Lemma round_simplify_clean : forall da config,
  no_Majority config ->
  is_clean (!! config) = true ->
  Config.eq (round gatherR2 da config)
         (fun id => match step da id with
                      | None => config id
                      | Some _ => target (!! config)
                    end).
Proof.
intros da config Hmaj Hclean id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta. rewrite Hclean.
rewrite no_Majority_equiv in Hmaj. destruct Hmaj as [? [? [? Hmaj]]].
now rewrite Hmaj.
Qed.

(** If the configuration is dirty, every robot /not on the SECT/ goes to the target. *)
Lemma round_simplify_dirty : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  Config.eq (round gatherR2 da config)
         (fun id => match step da id with
                      | None => config id
                      | Some _ => if mem R2.eq_dec (config id) (SECT (!! config))
                                  then config id else target (!! config)
                    end).
Proof.
intros da config Hmaj Hclean id. rewrite round_simplify.
destruct (step da id); try reflexivity. cbv zeta. rewrite Hclean.
rewrite no_Majority_equiv in Hmaj. destruct Hmaj as [? [? [? Hmaj]]].
now rewrite Hmaj.
Qed.


(* In the case where one majority tower exists, target is not used and does not compute the real target.
   Hence the no_Majority hypothesis  *)
Theorem destination_is_target : forall da config, no_Majority config ->
  forall id, In id (moving gatherR2 da config) -> round gatherR2 da config id = target (!! config).
Proof.
intros da config Hmaj id Hmove. rewrite round_simplify.
destruct (step da id) as [f |] eqn:Hstep.
* rewrite moving_spec, round_simplify, Hstep in Hmove. cbn in *.
  unfold no_Majority in Hmaj. rewrite Spect.size_spec in Hmaj.
  destruct (Spect.support (Spect.max (!! config))) as [| ? [| ? ?]]; simpl in Hmaj; try omega.
  destruct (is_clean (!! config)) eqn:Hclean.
  + reflexivity.
  + destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem.
    - now elim Hmove.
    - reflexivity.
* apply moving_active in Hmove. rewrite active_spec in Hmove. contradiction.
Qed.

Corollary same_destination : forall da config id1 id2,
  In id1 (moving gatherR2 da config) -> In id2 (moving gatherR2 da config) ->
  round gatherR2 da config id1 = round gatherR2 da config id2.
Proof.
intros da config id1 id2 Hmove1 Hmove2.
destruct (le_lt_dec 2 (length (Spect.support (Spect.max (!! config))))) as [Hle |Hlt].
+ assert (no_Majority config). { unfold no_Majority. now rewrite Spect.size_spec. }
  now repeat rewrite destination_is_target.
+ rewrite moving_spec in *. do 2 rewrite round_simplify in *. cbn in *.
  destruct (step da id1), (step da id2); try (now elim Hmove1 + elim Hmove2); [].
  destruct (Spect.support (Spect.max (!! config))) as [| ? [| ? ?]] eqn:Hsupp.
  - now elim Hmove1.
  - reflexivity.
  - simpl in Hlt. omega.
Qed.

(** Generic result of robograms using multiset spectra. *)
Lemma increase_move :
  forall r conf da pt,
    ((!! conf)[pt] < (!! (round r da conf))[pt])%nat ->
    exists id, round r da conf id = pt /\ round r da conf id <> conf id.
Proof.
  intros r conf da pt Hlt.
  destruct (existsb (fun x =>
                       (andb (R2dec_bool ((round r da conf x))  pt)
                             (negb (R2dec_bool (conf x) pt)))) Names.names) eqn:Hex.
  - apply (existsb_exists) in Hex.
    destruct Hex as [id [Hin Heq_bool]].
    exists id.
    rewrite andb_true_iff, negb_true_iff, R2dec_bool_true_iff, R2dec_bool_false_iff in Heq_bool.
    destruct Heq_bool; subst; auto.
  - exfalso. rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hex.
    (* Let us remove the In x (Gnames nG) and perform some rewriting. *)
    assert (Hg : forall id, round r da conf id <> pt \/ conf id = pt).
    { intro id. specialize (Hex id). rewrite negb_andb, orb_true_iff, negb_true_iff, negb_involutive in Hex.
      rewrite <- R2dec_bool_false_iff, <- R2dec_bool_true_iff. apply Hex, Names.In_names. }
    (** We prove a contradiction by showing that the opposite inequality of Hlt holds. *)
    clear Hex. revert Hlt. apply le_not_lt.
    do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
    induction Spect.Names.names as [| id l]; simpl; trivial.
    destruct (R2.eq_dec (round r da conf id) pt) as [Heq | Heq].
    + destruct (R2.eq_dec (conf id) pt); try omega. specialize (Hg id). intuition.
    + destruct (R2.eq_dec (conf id) pt); omega.
Qed.


(** Because of [same_destination], we can strengthen the previous result into an equivalence. *)
Theorem increase_move_iff :
  forall conf da pt,
    ((!! conf)[pt] < (!! (round gatherR2 da conf))[pt])%nat <->
    exists id, round gatherR2 da conf id = pt /\ round gatherR2 da conf id <> conf id.
Proof.
intros conf da pt. split.
* apply increase_move.
* intros [id [Hid Hroundid]].
  assert (Hdest : forall id', In id' (moving gatherR2 da conf) -> round gatherR2 da conf id' = pt).
  { intros. rewrite <- Hid. apply same_destination; trivial; rewrite moving_spec; auto. }
  assert (Hstay : forall id, conf id = pt -> round gatherR2 da conf id = pt).
  { intros id' Hid'. destruct (R2.eq_dec (round gatherR2 da conf id') pt) as [Heq | Heq]; trivial.
    assert (Habs := Heq). rewrite <- Hid', <- moving_spec in Habs. apply Hdest in Habs. contradiction. }
  do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
  assert (Hin : In id Spect.Names.names) by apply Names.In_names.
  induction Spect.Names.names as [| id' l]; try (now inversion Hin); [].
  inversion_clear Hin.
  + subst id'. clear IHl. simpl. destruct (R2.eq_dec (conf id) pt) as [Heq | Heq].
    - rewrite <- Hid in Heq. now elim Hroundid.
    - destruct (R2.eq_dec (round gatherR2 da conf id) pt ) as [Hok | Hko]; try contradiction; [].
      apply le_n_S. induction l; simpl.
      -- reflexivity.
      -- repeat R2dec_full; try now idtac + apply le_n_S + apply le_S; apply IHl.
         elim Hneq. now apply Hstay.
  + apply IHl in H. simpl. repeat R2dec_full; try omega.
    elim Hneq. apply Hdest. now rewrite moving_spec, Heq.
Qed.

(** ***  Lemmas about [target]  **)

(** ****  The value of [target] in the various cases  **)

Lemma diameter_target:
  forall conf ptx pty,
    on_SEC (Spect.support (!! conf)) = ptx :: pty :: nil
    -> target (!! conf) = R2.middle ptx pty.
Proof.
  intros conf ptx pty HonSEC.
  unfold target.
  rewrite HonSEC.
  apply on_SEC_pair_is_diameter in HonSEC.
  now rewrite HonSEC.
Qed.

Lemma equilateral_target : forall conf ptx pty ptz,
  PermutationA R2.eq (on_SEC (Spect.support (!! conf))) (ptx :: pty :: ptz :: nil) ->
  classify_triangle ptx pty ptz = Equilateral ->
  target (!! conf) = barycenter_3_pts ptx pty ptz.
Proof.
intros conf ptx pty ptz Hperm Htriangle.
unfold target.
assert (Hlen : length (on_SEC (Spect.support (!! conf))) = 3) by now rewrite Hperm.
destruct (on_SEC (Spect.support (!! conf))) as [| ? [| ? [| ? [| ? ?]]]]; simpl in Hlen; try discriminate.
rewrite PermutationA_Leibniz in Hperm. rewrite (target_triangle_compat Hperm).
unfold target_triangle. now rewrite Htriangle.
Qed.

Lemma isosceles_target : forall conf ptx pty ptz vertex,
    PermutationA R2.eq (on_SEC (Spect.support (!! conf))) (ptx :: pty :: ptz :: nil) ->
    classify_triangle ptx pty ptz = Isosceles vertex ->
    target (!! conf) = vertex.
Proof.
  intros conf ptx pty ptz vertex Hsec Htriangle.

  unfold target.
  destruct (on_SEC (Spect.support (!! conf))) eqn:heq.
  - assert (@length R2.t nil = length (ptx :: pty :: ptz :: nil)).
    { rewrite Hsec at 1.
      reflexivity. }
    cbn in H; omega.
  - destruct l.
    + assert (@length R2.t (t :: nil) = length (ptx :: pty :: ptz :: nil)).
      { rewrite Hsec at 1.
        reflexivity. }
      cbn in H; omega.
    + destruct l.
      * assert (@length R2.t (t :: t0 :: nil) = length (ptx :: pty :: ptz :: nil)).
        { rewrite Hsec at 1.
          reflexivity. }
        cbn in H; omega.
      * destruct l.
        -- assert (h:=PermutationA_3 R2.eq_equiv t t0 t1 ptx pty ptz).
           destruct h.
           specialize (H Hsec).
           decompose [or and] H;
             match goal with
             | |- target_triangle ?x ?y ?z = ?v => 
               assert (hhh:classify_triangle x y z = classify_triangle ptx pty ptz);
                 [ eapply classify_triangle_compat;
                   rewrite <- PermutationA_Leibniz;
                   rewrite PermutationA_3;auto;autoclass
                 | rewrite <- hhh in Htriangle;auto;
                   unfold target_triangle; rewrite Htriangle;reflexivity]
             end.
           
        -- assert (@length R2.t (t :: t0 :: t1 :: t2 :: l) = length (ptx :: pty :: ptz :: nil)).
           { rewrite Hsec at 1.
             reflexivity. }
           cbn in H; omega.
Qed.

Lemma scalene_target : forall conf ptx pty ptz,
    PermutationA R2.eq (on_SEC (Spect.support (!! conf))) (ptx :: pty :: ptz :: nil) ->
    classify_triangle ptx pty ptz = Scalene ->
    target (!! conf) = opposite_of_max_side ptx pty ptz.
Proof.
  intros conf ptx pty ptz Hsec Htriangle.
  remember (opposite_of_max_side ptx pty ptz) as vertex.
  unfold target.
  
  destruct (on_SEC (Spect.support (!! conf))) eqn:heq.
  - assert (@length R2.t nil = length (ptx :: pty :: ptz :: nil)).
    { rewrite Hsec at 1.
      reflexivity. }
    cbn in H; omega.
  - destruct l.
    + assert (@length R2.t (t :: nil) = length (ptx :: pty :: ptz :: nil)).
      { rewrite Hsec at 1.
        reflexivity. }
      cbn in H; omega.
    + destruct l.
      * assert (@length R2.t (t :: t0 :: nil) = length (ptx :: pty :: ptz :: nil)).
        { rewrite Hsec at 1.
          reflexivity. }
        cbn in H; omega.
      * destruct l.
        -- assert (h:=PermutationA_3 R2.eq_equiv t t0 t1 ptx pty ptz).
           destruct h.
           specialize (H Hsec).
           decompose [or and] H;
             match goal with
             | |- target_triangle ?x ?y ?z = ?v => 
               assert (hhh:classify_triangle x y z = classify_triangle ptx pty ptz);
                 [ eapply classify_triangle_compat;
                   rewrite <- PermutationA_Leibniz;
                   rewrite PermutationA_3;auto;autoclass
                 | rewrite <- hhh in Htriangle;auto;
                   unfold target_triangle; rewrite Htriangle;rewrite H2,H1,H4; symmetry; auto ]
             end;
             match goal with
             | |- ?v = opposite_of_max_side ?x ?y ?z => 
               assert (hhhh:opposite_of_max_side ptx pty ptz = opposite_of_max_side x y z);
                 [ apply opposite_of_max_side_compat;[rewrite <- hhh;assumption|rewrite <- PermutationA_Leibniz;
             rewrite PermutationA_3;auto 8;autoclass]
                 | rewrite <- hhhh;assumption ]
             end.
        -- assert (@length R2.t (t :: t0 :: t1 :: t2 :: l) = length (ptx :: pty :: ptz :: nil)).
           { rewrite Hsec at 1.
             reflexivity. }
           cbn in H; omega.
Qed.

Lemma generic_target : forall config,
  generic_case config ->
  target (!! config) = center (SEC (Spect.support (!! config))).
Proof.
intros config [_ [? [? [? [? [? HpermSEC]]]]]]. unfold target.
apply PermutationA_length in HpermSEC.
destruct (on_SEC (Spect.support (!! config))) as [| ? [| ? [| ? [| ? ?]]]]; cbn in HpermSEC; omega || reflexivity.
Qed.

(** ****  Results about [target] and [SEC]  **)

Lemma same_on_SEC_same_target : forall config1 config2,
  PermutationA R2.eq (on_SEC (Spect.support (!! config1))) (on_SEC (Spect.support (!! config2))) ->
  target (!! config1) = target (!! config2).
Proof.
intros config1 config2 Hperm. unfold target.
assert (Hlen := PermutationA_length Hperm).
destruct (on_SEC (Spect.support (!! config1))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec1,
         (on_SEC (Spect.support (!! config2))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec2;
reflexivity || simpl in Hlen; try omega.
- now rewrite (PermutationA_1 _) in Hperm.
- f_equal. setoid_rewrite SEC_on_SEC. now rewrite Hsec1, Hperm, Hsec2.
- apply target_triangle_compat. now rewrite <- PermutationA_Leibniz.
- f_equal. setoid_rewrite SEC_on_SEC. now rewrite Hsec1, Hperm, Hsec2.
Qed.

Lemma same_on_SEC_same_SECT : forall config1 config2,
  PermutationA R2.eq (on_SEC (Spect.support (!! config1))) (on_SEC (Spect.support (!! config2))) ->
  PermutationA R2.eq (SECT (!! config1)) (SECT (!! config2)).
Proof.
intros config1 config2 Hsame. unfold SECT.
rewrite Hsame.
apply same_on_SEC_same_target in Hsame.
now rewrite Hsame.
Qed.

Lemma target_inside_SEC : forall config,
  no_Majority config ->
  (R2.dist (target (!! config)) (center (SEC (Spect.support (!! config))))
   <= radius (SEC (Spect.support (!! config))))%R.
Proof.
intros config Hmaj. unfold target.
assert (Hlen := no_Majority_on_SEC_length Hmaj).
destruct (on_SEC (Spect.support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec;
simpl in Hlen; omega || clear Hlen; [| |].
+ rewrite R2_dist_defined_2.
  rewrite SEC_on_SEC, Hsec, radius_is_max_dist, SEC_dueton. simpl.
  unfold max_dist. simpl. rewrite middle_comm at 2. do 2 rewrite R2dist_middle.
  rewrite R2.dist_sym. repeat rewrite Rmax_right.
  - assert (Hpos := R2.dist_pos pt2 pt1). lra.
  - reflexivity.
  - assert (Hpos := R2.dist_pos pt2 pt1). lra.
+ rewrite SEC_on_SEC, Hsec. unfold target_triangle.
  destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
  - apply barycenter_3_pts_inside_SEC.
  - rewrite classify_triangle_Isosceles_spec in Htriangle.
    assert (Hin : InA R2.eq vertex (on_SEC (Spect.support (!! config)))).
    { rewrite Hsec. decompose [and or] Htriangle; subst; intuition. }
    unfold on_SEC in Hin. rewrite filter_InA in Hin; autoclass. destruct Hin as [_ Hin].
    rewrite on_circle_true_iff, SEC_on_SEC, Hsec in Hin. now rewrite Hin.
  - unfold opposite_of_max_side. unfold Rle_bool.
    do 2 match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
    match goal with |- (R2.dist ?pt _ <= _)%R =>
      assert (Hin : InA R2.eq pt (on_SEC (Spect.support (!! config)))) by (rewrite Hsec; intuition);
      unfold on_SEC in Hin; rewrite filter_InA in Hin; autoclass; []; rewrite <- Hsec, <- SEC_on_SEC;
      destruct Hin as [_ Hin]; rewrite on_circle_true_iff in Hin; now rewrite Hin
    end.
+ rewrite R2_dist_defined_2.
  rewrite SEC_on_SEC, Hsec, radius_is_max_dist.
  transitivity (R2.dist pt1 (center (SEC (pt1 :: pt2 :: pt3 :: t :: l)))).
  - apply R2.dist_pos.
  - apply max_dist_le. intuition.
Qed.

(** If the target is on the SEC, then we are in a non-equilateral triangle case. *)
Lemma target_on_SEC_cases : forall config, no_Majority config ->
  (on_circle (SEC (Spect.support (!! config))) (target (!! config)) = true <->
  triangle_case config /\ ~equilateral_case config).
Proof.
intros config Hmaj. split.
* intro Htarget.
  rewrite SEC_on_SEC in Htarget. unfold target in *.
  assert (Hlen := no_Majority_on_SEC_length Hmaj).
  assert (Hnodup : NoDupA R2.eq (on_SEC (Spect.support (!! config)))) by apply on_SEC_NoDupA, Spect.support_NoDupA.
  destruct (on_SEC (Spect.support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec;
  simpl in Hlen; omega || clear Hlen; [| |].
  + exfalso.
    assert (Heq : R2.eq pt1 pt2).
    { rewrite SEC_dueton in Htarget.
      rewrite on_circle_true_iff in Htarget.
      rewrite SEC_on_SEC, Hsec, SEC_dueton in Htarget.
      cbn in Htarget.
      rewrite R2_dist_defined_2 in Htarget.
      rewrite <- R2.dist_defined. lra. }
    inversion_clear Hnodup. intuition.
  + unfold target_triangle in *. destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
    - exfalso.
      rewrite triangle_barycenter_inside in Htarget; try discriminate; [].
      inversion_clear Hnodup. intuition.
    - get_case config. split; trivial. intro Habs.
      unfold triangle_case, equilateral_case in *.
      destruct Habs as [_ [? [? [? [Hperm Hequilateral]]]]].
      rewrite Hsec, PermutationA_Leibniz in Hperm.
      rewrite <- (classify_triangle_compat Hperm), Htriangle in Hequilateral.
      discriminate.
    - get_case config. split; trivial. intro Habs.
      unfold triangle_case, equilateral_case in *.
      destruct Habs as [_ [? [? [? [Hperm Hequilateral]]]]].
      rewrite Hsec, PermutationA_Leibniz in Hperm.
      rewrite <- (classify_triangle_compat Hperm), Htriangle in Hequilateral.
      discriminate.
  + exfalso.
    setoid_rewrite SEC_on_SEC in Htarget at 2. rewrite Hsec in Htarget.
    rewrite center_on_circle in Htarget.
    rewrite SEC_zero_radius_incl_singleton in Htarget. destruct Htarget as [pt Hpt].
    assert (Heq : R2.eq pt1 pt2).
    { transitivity pt.
      - specialize (Hpt pt1). cbn in Hpt. intuition.
      - specialize (Hpt pt2). cbn in Hpt. intuition. }
    inversion_clear Hnodup. intuition.
* intros [[_ [ptx [pty [ptz Hperm]]]] Hequilateral].
  assert (Hlen := PermutationA_length Hperm).
  destruct (on_SEC (Spect.support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec; try discriminate; [].
  destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
  + get_case config. contradiction.
  + erewrite (isosceles_target config ltac:(now rewrite Hsec)); try eassumption; [].
    eapply proj2. rewrite <- (filter_InA _). unfold on_SEC in Hsec. rewrite Hsec.
    rewrite classify_triangle_Isosceles_spec in Htriangle.
    decompose [and or] Htriangle; subst; intuition.
  + erewrite (scalene_target config ltac:(now rewrite Hsec)); try eassumption; [].
    eapply proj2. rewrite <- (filter_InA _). unfold on_SEC in Hsec. rewrite Hsec.
    unfold opposite_of_max_side.
    do 2 match goal with |- context[Rle_bool ?x ?y] => destruct (Rle_bool x y) end; intuition.
Qed.

Lemma target_on_SEC_already_occupied : forall config,
  no_Majority config ->
  on_circle (SEC (Spect.support (!! config))) (target (!! config)) = true ->
  InA R2.eq (target (!! config)) (Spect.support (!! config)).
Proof.
intros config Hmaj Htarget.
apply target_on_SEC_cases in Htarget; trivial.
destruct Htarget as [[_ [ptx [pty [ptz Hperm]]]] Hequilateral].
assert (Hlen := PermutationA_length Hperm).
destruct (on_SEC (Spect.support (!! config))) as [| pt1 [| pt2 [| pt3 [| ? ?]]]] eqn:Hsec;
simpl in Hlen; discriminate || clear Hlen; [].
unfold target. rewrite Hsec. unfold target_triangle.
destruct (classify_triangle pt1 pt2 pt3) eqn:Htriangle.
+ get_case config. contradiction.
+ rewrite classify_triangle_Isosceles_spec in Htriangle.
  decompose [and or] Htriangle; subst; clear Htriangle;
  match goal with |- InA R2.eq ?pt (Spect.support (!! config)) =>
    assert (Hin : InA R2.eq pt (pt1 :: pt2 :: pt3 :: nil)) by intuition;
    rewrite <- Hsec in Hin; unfold on_SEC in Hin; now rewrite filter_InA in Hin; autoclass
  end.
+ unfold opposite_of_max_side. unfold Rle_bool.
  do 2 match goal with |- context[Rle_dec ?x ?y] => destruct (Rle_dec x y) end;
  match goal with |- InA R2.eq ?pt (Spect.support (!! config)) =>
    assert (Hin : InA R2.eq pt (pt1 :: pt2 :: pt3 :: nil)) by intuition;
    rewrite <- Hsec in Hin; unfold on_SEC in Hin; now rewrite filter_InA in Hin; autoclass
  end.
Qed.

(** ***  Generic results about the [SEC] after one round **)

Lemma incl_next : forall da conf,
    (inclA R2.eq
           (Spect.support (!! (round gatherR2 da conf)))
           ((target (!! conf)) :: (Spect.support (!! conf)))).
Proof.
  intros da conf.
  red.
  intros x hIn.
  rewrite Spect.support_elements in hIn.
  apply Spect.elements_spec in hIn.
  destruct hIn as [_ hIn].
  destruct (R2.eq_dec x (target (!! conf))).
  - left.
    assumption.
  - right.
    rewrite Spect.support_elements.
    apply Spect.elements_spec.
    split;auto.
    destruct (le_lt_dec ((!! conf)[x]) 0).
    + exfalso.
      destruct (@increase_move gatherR2 conf da x)
        as [r_moving [hdest_rmoving  hrmoving ]].
      * omega.
      * { destruct (le_lt_dec 2 (length (Spect.support (Spect.max (!! conf))))).
          - rewrite destination_is_target in hdest_rmoving.
            + elim n.
              subst;reflexivity.
            + unfold no_Majority. now rewrite Spect.size_spec.
            + rewrite moving_spec.
              assumption.
          - assert ((Spect.support (Spect.max (!! conf))) = x::nil).
            { destruct (Spect.support (Spect.max (!! conf))) as [| pt [| ? ?]] eqn:heq; cbv in l0; try omega.
              - destruct (support_max_non_nil conf).
                assumption.
              - get_case conf.
                rewrite (@round_simplify_Majority _ _ pt Hcase) in hdest_rmoving.
                destruct (step da r_moving).
                + subst;reflexivity.
                + assert (h:=Spect.pos_in_config conf r_moving).
                  subst x.
                  unfold Spect.In in h.
                  exfalso;omega.
            }
            assert (hperm:PermutationA eq (Spect.support (Spect.max (!! conf)))
                                 (x :: nil)).
            { rewrite H;reflexivity. }
            rewrite Spect.support_1 in hperm.
            destruct hperm as [_ hperm].
            destruct (Spect.max_2_mult (!! conf) x);omega. }
    + assumption.
Qed.

Lemma incl_clean_next : forall da conf,
  is_clean (!! conf) = true ->
  inclA R2.eq (Spect.support (!! (round gatherR2 da conf)))
              (target (!! conf) :: on_SEC (Spect.support (!! conf))).
Proof.
  intros da conf H.
  transitivity ((target (!! conf)) :: (Spect.support (!! conf))).
  - apply incl_next.
  - rewrite inclA_Leibniz.
    apply incl_cons.
    + now left.
    + now rewrite <- inclA_Leibniz, <- is_clean_spec.
Qed.

Lemma next_SEC_enclosed : forall da config,
  no_Majority config -> 
  enclosing_circle (SEC (Spect.support (!! config))) (Spect.support (!! (round gatherR2 da config))).
Proof.
intros da config Hmaj pt Hin.
rewrite <- InA_Leibniz, Spect.support_In in Hin. unfold Spect.In in Hin.
rewrite Spect.from_config_spec, Spect.Config.list_spec in Hin.
induction Spect.Names.names as [| id l]; simpl in *; try omega; [].
R2dec_full in Hin; try (now apply IHl); [].
rewrite <- Heq.
rewrite round_simplify; trivial; []. simpl.
destruct (step da id).
* assert (Hmax := Hmaj). rewrite no_Majority_equiv in Hmax. destruct Hmax as [pt1 [pt2 [lmax Hmax]]]. rewrite Hmax.
  destruct (is_clean (!! config)).
  + now apply target_inside_SEC.
  + destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem.
    - apply SEC_spec1. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
    - now apply target_inside_SEC.
* apply SEC_spec1. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
Qed.

(** ***  Lemmas about the dirty cases  **)

(* To prove dirty_next_on_SEC_same below, we first prove that any point on the SEC does not move. *)
Lemma dirty_next_still_on_SEC : forall da config id,
  no_Majority config ->
  is_clean (!! config) = false ->
  on_circle (SEC (Spect.support (!! config))) (config id) = true ->
  round gatherR2 da config id = config id.
Proof.
intros da config id Hmaj Hclean Hcircle.
rewrite round_simplify_dirty; trivial; [].
destruct (step da id); trivial; [].
destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem; trivial; [].
rewrite mem_false_iff in Hmem. elim Hmem.
unfold SECT. right. unfold on_SEC. rewrite filter_InA; autoclass; [].
split; trivial; [].
rewrite Spect.support_In. apply Spect.pos_in_config.
Qed.

Lemma dirty_next_SEC_same : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  SEC (Spect.support (!! (round gatherR2 da config))) = SEC (Spect.support (!! config)).
Proof.
intros da config Hmaj Hclean.
assert (HonSEC : forall id, In (config id) (on_SEC (Spect.support (!! config))) ->
                   round gatherR2 da config id = config id).
{ intros id Hid. rewrite round_simplify_dirty; trivial; [].
  destruct (step da id); trivial; [].
  assert (Heq : mem R2.eq_dec (config id) (SECT (!! config)) = true).
  { rewrite mem_true_iff. right. now apply InA_Leibniz. }
  now rewrite Heq. }
apply enclosing_same_on_SEC_is_same_SEC.
+ now apply next_SEC_enclosed.
+ intros pt Hin.
  assert (Hid : exists id, config id = pt).
  { unfold on_SEC in Hin. rewrite filter_In in Hin. destruct Hin as [Hin Hsec].
    now rewrite <- InA_Leibniz, Spect.support_In, Spect.from_config_In in Hin. }
  destruct Hid as [id Hid]. rewrite <- Hid in *. 
  rewrite <- HonSEC; trivial. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config.
Qed.

Lemma dirty_next_on_SEC_same : forall da config,
  no_Majority config ->
  is_clean (!! config) = false ->
  PermutationA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da config)))) (on_SEC (Spect.support (!! config))).
Proof.
intros da config Hmaj Hclean. apply (NoDupA_equivlistA_PermutationA _).
- unfold on_SEC. apply (Preliminary.NoDupA_filter_compat _), Spect.support_NoDupA.
- unfold on_SEC. apply (Preliminary.NoDupA_filter_compat _), Spect.support_NoDupA.
- intro pt.
  unfold on_SEC in *. rewrite dirty_next_SEC_same; trivial; [].
  do 2 (rewrite filter_InA; autoclass); [].
  split; intros [Hin Hcircle]; split; trivial; [|].
  + rewrite Spect.support_In, Spect.from_config_In in Hin. destruct Hin as [id Hid].
    rewrite round_simplify_dirty in Hid; trivial; [].
    destruct (step da id).
    * destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem.
      -- rewrite <- Hid, Spect.support_In. apply Spect.pos_in_config.
      -- rewrite <- Hid in *. clear Hid pt.
         now apply target_on_SEC_already_occupied.
    * rewrite <- Hid, Spect.support_In. apply Spect.pos_in_config.
  + rewrite Spect.support_In, Spect.from_config_In in Hin. destruct Hin as [id Hid].
    rewrite <- Hid in *.
    assert (Heq : round gatherR2 da config id = config id) by now apply dirty_next_still_on_SEC.
    rewrite <- Heq, Spect.support_In. apply Spect.pos_in_config.
Qed.

(** ***  Lemma about the majority case  **)

(* Next lemmas taken from the gathering algo in R. *)
(** When there is a majority tower, it grows and all other towers wither. **)
Theorem Majority_grow :  forall pt config da, MajTower_at pt config ->
  (!! config)[pt] <= (!! (round gatherR2 da config))[pt].
Proof.
intros pt confif da Hmaj.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - R2dec. R2dec_full; apply le_n_S + apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.

(* This proof follows the exact same structure. *)
Theorem Majority_wither : forall config da pt, MajTower_at pt config ->
  forall pt', pt <> pt' -> (!! (round gatherR2 da config))[pt'] <= (!! config)[pt'].
Proof.
intros conf da pt Hmaj pt' Hdiff.
rewrite (round_simplify_Majority _ Hmaj).
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
induction Spect.Names.names as [| id l]; simpl.
+ reflexivity.
+ destruct (step da id).
  - R2dec_full; try contradiction; []. R2dec_full; try apply le_S; apply IHl.
  - R2dec_full; try apply le_n_S; apply IHl.
Qed.

(** Whenever there is a majority tower, it remains forever so. *)
Theorem MajTower_at_forever : forall pt conf da, MajTower_at pt conf -> MajTower_at pt (round gatherR2 da conf).
Proof.
intros pt conf da Hmaj x Hx. assert (Hs := Hmaj x Hx).
apply le_lt_trans with ((!! conf)[x]); try eapply lt_le_trans; try eassumption; [|].
- eapply Majority_wither; eauto.
- eapply Majority_grow; eauto.
Qed.

Lemma solve_measure_clean : forall da config,
  no_Majority config ->
  moving gatherR2 da config <> nil ->
  target (!! (round gatherR2 da config)) = target (!! config) ->
  measure_clean (!! (round gatherR2 da config)) < measure_clean (!! config).
Proof.
intros da config Hmaj Hmoving Htarget.
unfold measure_clean. rewrite Htarget.
assert (Hle := multiplicity_le_nG (target (!! config)) (round gatherR2 da config)).
cut ((!! config)[target (!! config)] < (!! (round gatherR2 da config))[target (!! config)]); try omega.
rewrite increase_move_iff.
apply not_nil_In in Hmoving. destruct Hmoving as [gmove Hmove].
assert (Hstep : step da gmove <> None).
{ apply moving_active in Hmove. now rewrite active_spec in Hmove. }
exists gmove. split.
- now apply destination_is_target.
- now rewrite <- moving_spec.
Qed.

Lemma solve_measure_dirty : forall da config,
  moving gatherR2 da config <> nil ->
  no_Majority config ->
  is_clean (!! config) = false ->
  no_Majority (round gatherR2 da config) ->
  is_clean (!! (round gatherR2 da config)) = false ->
  measure_dirty (!! (round gatherR2 da config)) < measure_dirty (!! config).
Proof.
intros da config Hmoving Hmaj Hclean Hmaj' Hclean'.
assert (HsameSEC := dirty_next_on_SEC_same da Hmaj Hclean).
assert (Htarget := same_on_SEC_same_target _ _ HsameSEC).
assert (HsameSECT := same_on_SEC_same_SECT _ _ HsameSEC).
unfold measure_dirty.
assert (HlenG : SECT_cardinal (!! (round gatherR2 da config)) <= N.nG) by apply SECT_cardinal_le_nG.
cut (SECT_cardinal (!! config) < SECT_cardinal (!! (round gatherR2 da config))); try omega; [].
assert (Hlt : (!! config)[target (!! config)] < (!! (round gatherR2 da config))[target (!! config)]).
{ rewrite increase_move_iff.
  apply not_nil_In in Hmoving. destruct Hmoving as [gmove Hmove].
  assert (Hstep : step da gmove <> None).
  { apply moving_active in Hmove. now rewrite active_spec in Hmove. }
  exists gmove. split.
  - now apply destination_is_target.
  - now rewrite <- moving_spec. }
unfold SECT_cardinal.
pose (f s x := if in_dec R2.eq_dec x (SECT s) then true else false).
assert (Hext : forall x, f (!! (round gatherR2 da config)) x = f (!! config) x).
{ intro pt. unfold f.
  destruct (in_dec R2.eq_dec pt (SECT (!! config))) as [Htest1 | Htest1],
           (in_dec R2.eq_dec pt (SECT (!! (round gatherR2 da config)))) as [Htest2 | Htest2]; trivial.
  - elim Htest2.
    rewrite <- InA_Leibniz in *.
    now rewrite HsameSECT.
  - elim Htest1.
    rewrite <- InA_Leibniz in *.
    now rewrite <- HsameSECT. }
unfold f in Hext.
rewrite (Spect.filter_extensionality_compat _ _ Hext). clear Hext.
pose (f_target := fun x => if R2.eq_dec x (target (!! config)) then true else false).
pose (f_out_target := fun x => if in_dec R2.eq_dec x (SECT (!! config)) then negb (f_target x) else false).
assert (Hext : forall x, f (!! config) x = f_target x || f_out_target x).
{ intro pt. unfold f, f_out_target, f_target. simpl. do 2 R2dec_full; intuition. }
unfold f in Hext. setoid_rewrite (Spect.filter_extensionality_compat _ _ Hext). clear Hext f.
assert (Hdisjoint : forall m x, Spect.In x m -> f_target x && f_out_target x = false).
{ intros m x Hin.
  destruct (f_target x) eqn:Heq1, (f_out_target x) eqn:Heq2; trivial.
  exfalso. unfold f_out_target, f_target in *. clear f_target f_out_target.
  R2dec_full in Heq1; try discriminate; [].
  rewrite Heq in Heq2.
  destruct (in_dec R2.eq_dec (target (!! config)) (SECT (!! config))); discriminate. }
setoid_rewrite Spect.filter_disjoint_or_union; autoclass.
do 2 rewrite Spect.cardinal_union.
unfold f_target.
setoid_rewrite Spect.cardinal_filter_is_multiplicity.
assert (Heq : Spect.eq (Spect.filter f_out_target (!! (round gatherR2 da config)))
                       (Spect.filter f_out_target (!! config))).
{ intro pt. repeat rewrite Spect.filter_spec; autoclass.
  destruct (f_out_target pt) eqn:Htest; trivial.
  rewrite round_simplify_dirty; trivial. symmetry.
  (* by induction on the list of robot names *)
  do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
  induction Spect.Names.names as [| id l]; simpl.
  * reflexivity.
  * R2dec_full.
    + rewrite Heq in *. destruct (step da id) eqn:Hactive.
      - assert (Hmem : mem R2.eq_dec pt (SECT (!! config)) = true).
        { rewrite mem_true_iff, InA_Leibniz. unfold f_out_target in Htest. clear Hdisjoint f_out_target.
          destruct (in_dec R2.eq_dec pt (SECT (!! config))) as [Hin | Hin]; trivial; discriminate. }
        rewrite Hmem. R2dec. f_equal. apply IHl.
      - R2dec. f_equal. apply IHl.
    + destruct (step da id) eqn:Hactive.
      - destruct (mem R2.eq_dec (config id) (SECT (!! config))) eqn:Hmem.
        ++ R2dec_full; contradiction || apply IHl.
        ++ destruct (R2.eq_dec (target (!! config)) pt) as [Heq | Heq].
           -- exfalso.
              unfold f_out_target in Htest.
              destruct (in_dec R2.eq_dec pt (SECT (!! config))); try discriminate.
              rewrite negb_true_iff in Htest.
              unfold f_target in Htest. symmetry in Heq.
              R2dec_full in Htest; discriminate || contradiction.
           -- apply IHl.
      - R2dec. f_equal. R2dec_full; contradiction || apply IHl. }
rewrite Heq.
omega.
Qed.

(** ***  A forbidden configuration cannot appear  **)

(* For [never_forbidden] *)
Lemma towers_elements_3 : forall config pt1 pt2,
  (Spect.size (!! config) >= 3)%nat ->
  Spect.In pt1 (!! config) -> Spect.In pt2 (!! config) -> pt1 <> pt2 ->
  exists pt3, pt1 <> pt3 /\ pt2 <> pt3 /\ Spect.In pt3 (!! config).
Proof.
intros config pt1 pt2 Hlen Hpt1 Hpt2 Hdiff12.
rewrite <- Spect.support_In in *. rewrite Spect.size_spec in Hlen.
apply (PermutationA_split _) in Hpt1. destruct Hpt1 as [supp1 Hperm].
rewrite Hperm in Hpt2. inversion_clear Hpt2; try (now elim Hdiff12); []. rename H into Hpt2.
apply (PermutationA_split _) in Hpt2. destruct Hpt2 as [supp2 Hperm2].
rewrite Hperm2 in Hperm. rewrite Hperm in Hlen.
destruct supp2 as [| pt3 supp]; try (now simpl in Hlen; omega); [].
exists pt3.
rewrite <- Spect.support_In. assert (Hnodup := Spect.support_NoDupA (!! config)).
rewrite Hperm in *. inversion_clear Hnodup. inversion_clear H0. repeat split.
- intro Habs. subst. apply H. now right; left.
- intro Habs. subst. apply H1. now left.
- now right; right; left.
Qed.

(* For [never_forbidden] *)
Lemma sum3_le_total : forall config pt1 pt2 pt3, pt1 <> pt2 -> pt2 <> pt3 -> pt1 <> pt3 ->
  (!! config)[pt1] + (!! config)[pt2] + (!! config)[pt3] <= N.nG.
Proof.
intros config pt1 pt2 pt3 Hpt12 Hpt23 Hpt13.
replace N.nG with (N.nG + N.nB) by (unfold N.nB; omega).
rewrite <- (Spect.cardinal_from_config config).
rewrite <- (@Spect.add_remove_id pt1 _ (!! config) (reflexivity _)) at 4.
rewrite Spect.cardinal_add.
rewrite <- (@Spect.add_remove_id pt2 _ (!! config) (reflexivity _)) at 6.
rewrite Spect.remove_add_comm, Spect.cardinal_add; trivial.
rewrite <- (@Spect.add_remove_id pt3 _ (!! config) (reflexivity _)) at 8.
rewrite Spect.remove_add_comm, Spect.remove_add_comm, Spect.cardinal_add; trivial.
omega.
Qed.

(* Taken from the gathering in R.
   Any non-forbidden config without a majority tower contains at least three towers.
   All robots move toward the same place (same_destination), wlog pt1.
   |\before(pt2)| >= |\after(pt2)| = nG / 2
   As there are nG robots, nG/2 at p2, we must spread nG/2 into at least two locations
   thus each of these towers has less than nG/2 and pt2 was a majority tower. *)
Theorem never_forbidden : forall da conf, ~forbidden conf -> ~forbidden (round gatherR2 da conf).
Proof.
intros da conf Hok.
(* Three cases for the robogram *)
destruct (Spect.support (Spect.max (!! conf))) as [| pt [| pt' l']] eqn:Hmaj.
- assert (Config.eq (round gatherR2 da conf) conf).
  { rewrite round_simplify; simpl; try rewrite Hmaj; simpl.
    intros id. now destruct (step da id). }
  now rewrite H.
  (* There is a majority tower *)
- apply Majority_not_forbidden with pt.
  rewrite <- MajTower_at_equiv in *.
  apply (@MajTower_at_forever pt conf da) in Hmaj.
  assumption.
- get_case conf.
  clear pt pt' l' Hmaj. rename Hmaj0 into Hmaj.
  (* A robot has moved otherwise we have the same configuration before and it is forbidden. *)
  assert (Hnil := no_moving_same_conf gatherR2 da conf).
  destruct (moving gatherR2 da conf) as [| rmove l] eqn:Heq.
  * now rewrite Hnil.
  * intro Habs.
    clear Hnil.
    assert (Hmove : In rmove (moving gatherR2 da conf)). { rewrite Heq. now left. }
    rewrite moving_spec in Hmove.
    (* the robot moves to one of the two locations in round robogram conf *)
    assert (Hforbidden := Habs). destruct Habs as [HnG [HsizeG[pt1 [pt2 [Hdiff [Hpt1 Hpt2]]]]]].
    assert (Hpt : exists pt pt', (pt = pt1 /\ pt' = pt2 \/ pt = pt2  /\ pt' = pt1)
                                  /\ round gatherR2 da conf rmove = pt).
    { assert (Hperm : Permutation (Spect.support (!! (round gatherR2 da conf))) (pt1 :: pt2 :: nil)).
      { symmetry. apply NoDup_Permutation_bis.
        + repeat constructor.
          - intro Habs. inversion Habs. now elim Hdiff. now inversion H.
          - intro Habs. now inversion Habs.
        + rewrite <- NoDupA_Leibniz. apply Spect.support_NoDupA.
        + simpl. now rewrite <- Spect.size_spec, forbidden_support_length.
        + intros pt Hpt. inversion_clear Hpt.
          - subst. rewrite <- InA_Leibniz, Spect.support_spec. unfold Spect.In. rewrite Hpt1.
            apply Exp_prop.div2_not_R0. apply HsizeG.
          - inversion H; (now inversion H0) || subst. rewrite <- InA_Leibniz, Spect.support_spec.
            unfold Spect.In. rewrite Hpt2. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hpt : In (round gatherR2 da conf rmove) (pt1 :: pt2 :: nil)).
      { rewrite <- Hperm. rewrite <- InA_Leibniz, Spect.support_In. apply Spect.pos_in_config. }
      inversion_clear Hpt; try (now exists pt1, pt2; eauto); [].
      inversion_clear H; now exists pt2, pt1; eauto. }
    destruct Hpt as [pt [pt' [Hpt Hrmove_pt]]].
    assert (Hdiff2 : pt <> pt').
    { decompose [and or] Hpt; congruence. }
    assert (Hdest : forall g, In g (moving gatherR2 da conf) -> round gatherR2 da conf g = pt).
    { intros id Hid.
      rewrite <- Hrmove_pt.
      apply same_destination; auto. rewrite moving_spec. congruence. }
    assert ((div2 N.nG) <= (!! conf)[pt']).
    { transitivity ((!! (round gatherR2 da conf))[pt']).
      - decompose [and or] Hpt; subst; omega.
      - generalize (@increase_move_iff conf da pt').
        intro H1. apply Nat.nlt_ge.
        rewrite H1. intros [id [Hid1 Hid2]].
        apply Hdiff2.
        rewrite <- Hid1.
        symmetry.
        apply Hdest. rewrite moving_spec. assumption. }
    assert (Hlt : forall p, p <> pt' -> (!! conf)[p] < div2 N.nG).
    { assert (Hpt'_in : Spect.In pt' (!! conf)).
      { unfold Spect.In. eapply lt_le_trans; try eassumption. apply Exp_prop.div2_not_R0. apply HsizeG. }
      assert (Hle := not_forbidden_no_majority_size Hmaj Hok).
      intros p Hp. apply Nat.nle_gt. intro Habs. apply (lt_irrefl N.nG).
      destruct (@towers_elements_3 conf pt' p Hle Hpt'_in) as [pt3' [Hdiff13 [Hdiff23 Hpt3_in]]]; trivial.
      + apply lt_le_trans with (div2 N.nG); try assumption. apply Exp_prop.div2_not_R0. apply HsizeG.
      + auto.
      + eapply lt_le_trans; try apply (sum3_le_total conf Hp Hdiff13 Hdiff23); [].
        unfold Spect.In in Hpt3_in. rewrite <- ?Even.even_equiv in *.
        rewrite (even_double N.nG);simpl;auto.
        unfold Nat.double.
        omega. }
    assert (Hmaj' : MajTower_at pt' conf).
    { intros x Hx. apply lt_le_trans with (div2 N.nG); trivial. now apply Hlt. }
    apply MajTower_at_equiv in Hmaj'.
    red in Hmaj.
    rewrite Spect.size_spec in Hmaj.
    rewrite Hmaj' in Hmaj.
    simpl in Hmaj.
    omega.
Qed.

(** ***  Lemmas about the diameter case  **)


Lemma diameter_clean_support:
  forall conf ptx pty,
    ~ forbidden conf
    -> no_Majority conf
    -> is_clean (!! conf) = true
    -> on_SEC (Spect.support (!! conf)) = ptx :: pty :: nil
    -> PermutationA R2.eq (Spect.support (!! conf)) (R2.middle ptx pty :: ptx :: pty :: nil).
Proof.
  intros conf ptx pty Hforbidden hmax Hclean HonSEC.
  assert (Htarget : target (!!conf) = R2.middle ptx pty) by (apply (diameter_target);auto).
  apply (NoDupA_inclA_length_PermutationA _).
  - apply Spect.support_NoDupA.
  - assert (Hdiff : ptx <> pty).
    { assert (Hnodup : NoDupA R2.eq (on_SEC (Spect.support (!! conf)))).
      { unfold on_SEC in HonSEC.
        apply Preliminary.NoDupA_filter_compat;autoclass.
        apply Spect.support_NoDupA. }
      rewrite HonSEC in Hnodup.
      inversion Hnodup as [ | ? ? h1 h2]; subst.
      intro abs; subst.
      apply h1; now left. }
    constructor.
    + apply middle_diff.
      assumption.
    + rewrite <- HonSEC. apply on_SEC_NoDupA, Spect.support_NoDupA.
  - intros x Hin.
    rewrite is_clean_spec in Hclean. apply Hclean in Hin.
    now rewrite <- Htarget, <- HonSEC.
  - rewrite <- Spect.size_spec. now apply not_forbidden_no_majority_size.
Qed.

Lemma diameter_round_same:
  forall da conf ptx pty,
  no_Majority (round gatherR2 da conf)
  -> PermutationA R2.eq (Spect.support (!! conf)) (R2.middle ptx pty :: ptx :: pty :: nil)
  -> PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                        (R2.middle ptx pty :: ptx :: pty :: nil).
Proof.
  intros da conf ptx pty Hmaj Hperm.
  assert (Htarget : target (!! conf) = R2.middle ptx pty).
  { assert (HonSEC : PermutationA R2.eq (on_SEC (Spect.support (!! conf))) (ptx :: pty :: nil)).
    { rewrite Hperm. rewrite on_SEC_middle_diameter, on_SEC_dueton; try reflexivity; [].
      assert (Hnodup : NoDupA R2.eq (Spect.support (!! conf))) by apply Spect.support_NoDupA.
      rewrite Hperm in Hnodup. inversion_clear Hnodup. inversion_clear H0. intuition. }
    destruct (on_SEC (Spect.support (!! conf))) as [| ? [| ? [| ? ?]]] eqn:Hsec;
    try (apply PermutationA_length in HonSEC; discriminate); [].
    apply (PermutationA_2 _) in HonSEC. destruct HonSEC as [[Heq1 Heq2] | [Heq1 Heq2]]; rewrite <- Heq1, <- Heq2.
    - now apply diameter_target.
    - rewrite middle_comm. now apply diameter_target. }
  apply (NoDupA_inclA_length_PermutationA _).
  - apply Spect.support_NoDupA.
  - rewrite <- Hperm.
    apply Spect.support_NoDupA.
  - assert (Hincl:= incl_next da conf).
    rewrite Hperm in Hincl.
    rewrite Htarget in Hincl.
    apply (inclA_cons_InA _) in Hincl; auto.
    now left.
  - transitivity 3.
    + reflexivity.
    + rewrite <- Spect.size_spec.
      apply not_forbidden_no_majority_size; trivial.
      apply never_forbidden.
      rewrite forbidden_equiv.
      intros [_ Habs].
      rewrite Spect.size_spec, Hperm in Habs.
      simpl in Habs; omega.
Qed.


Lemma diameter_next_target_same : forall da conf,
  ~forbidden conf ->
  clean_diameter_case conf ->
  no_Majority (round gatherR2 da conf) ->
  target (!! (round gatherR2 da conf)) = target (!! conf).
Proof.
  intros da conf Hforbidden Hcleandiam Hmaj'.
  destruct Hcleandiam as [[Hmaj [pt1 [pt2 Htwocol]]] Hclean].
  apply PermutationA_length in Htwocol.
  unfold target.
  destruct (on_SEC (Spect.support (!! conf))) as [| ptx [| pty [| ptz [| ptt ?]]]] eqn:Hsec; try discriminate.
  assert (Hincl := incl_next da conf).
  assert (Htarget : target (!!conf) = R2.middle ptx pty) by (apply diameter_target; auto).
  assert (Hperm := @diameter_clean_support conf ptx pty Hforbidden Hmaj Hclean Hsec).
  assert (Hperm' : PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                      (R2.middle ptx pty :: ptx :: pty :: nil)).
  { apply (NoDupA_inclA_length_PermutationA _).
    - apply Spect.support_NoDupA.
    - rewrite <- Hperm.
      apply Spect.support_NoDupA.
    - apply (inclA_cons_InA _) with (R2.middle ptx pty).
      + intuition.
      + rewrite <- Hperm, <- Htarget. apply Hincl.
    - cbn. rewrite <- Spect.size_spec. now apply not_forbidden_no_majority_size, never_forbidden. }
  assert (HpermSEC' : PermutationA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da conf))))
                                         (ptx :: pty :: nil)).
  { rewrite Hperm'. rewrite on_SEC_middle_diameter.
    - now rewrite on_SEC_dueton.
    - assert (Hnodup : NoDupA R2.eq (R2.middle ptx pty :: ptx :: pty :: nil)).
      { rewrite <- Hperm. apply Spect.support_NoDupA. }
      inversion_clear Hnodup. inversion_clear H0. intuition. }
  assert (Hlen : length (on_SEC (Spect.support (!! (round gatherR2 da conf)))) = 2) by now rewrite HpermSEC'.
  destruct (on_SEC (Spect.support (!! (round gatherR2 da conf))))
    as [| ptx' [| pty' [| ? ?]]] eqn:Hsec'; cbn in Hlen; try discriminate.
  do 2 rewrite SEC_on_SEC, ?Hsec, ?Hsec', SEC_dueton. simpl.
  apply (PermutationA_2 _) in HpermSEC'.
  destruct HpermSEC' as [[Heq1 Heq2] | [Heq1 Heq2]]; rewrite Heq1, Heq2; trivial || apply middle_comm.
Qed.

Lemma clean_diameter_next_maj_or_diameter : forall da config ptx pty,
  ~forbidden config ->
  no_Majority config ->
  is_clean (!! config) = true ->
  on_SEC (Spect.support (!! config)) = ptx :: pty :: nil ->
  (exists pt, MajTower_at pt (round gatherR2 da config))
  \/ no_Majority (round gatherR2 da config)
     /\ PermutationA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da config)))) (ptx :: pty :: nil).
Proof.
intros da config ptx pty Hforbidden Hmaj Hclean Hsec.
assert (Hperm := diameter_clean_support Hforbidden Hmaj Hclean Hsec).
destruct (Spect.support (Spect.max (!! (round gatherR2 da config)))) as [| pt [| ? ?]] eqn:Hmax'.
- rewrite Spect.support_nil, Spect.max_empty, <- Spect.support_nil in Hmax'.
  now elim (support_non_nil _ Hmax').
- left. exists pt.
  rewrite MajTower_at_equiv. now rewrite Hmax'.
- right.
  assert (Hmaj' : no_Majority (round gatherR2 da config)).
  { eapply make_no_Majority. rewrite Hmax'. reflexivity. }
  split; trivial; [].
  assert (Htarget := diameter_target config Hsec).
  assert (Hperm' := diameter_round_same Hmaj' Hperm).
  rewrite Hperm'.
  rewrite on_SEC_middle_diameter.
  + now rewrite on_SEC_dueton.
  + assert (Hnodup : NoDupA R2.eq (on_SEC (Spect.support (!! config)))).
    { apply on_SEC_NoDupA, Spect.support_NoDupA. }
    rewrite Hsec in Hnodup. inversion_clear Hnodup. intuition.
Qed.

(** ***  Lemmas about the triangle cases  **)


(** ****  Lemmas about the equilateral triangle case  **)

Lemma SEC_3_to_2: forall da conf ptx pty ptz bary pt ptdiam,
    InA R2.eq pt (ptx :: pty :: ptz :: nil) ->
    InA R2.eq ptdiam (ptx :: pty :: ptz :: nil) ->
    pt<> ptdiam ->
    PermutationA R2.eq (on_SEC (Spect.support (!! conf))) (ptx :: pty :: ptz :: nil) ->
    PermutationA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da conf)))) (bary :: ptdiam :: nil) ->
    classify_triangle ptx pty ptz = Equilateral ->
    R2.eq bary (barycenter_3_pts ptx pty ptz) ->
    ~ InA R2.eq pt (Spect.support (!! (round gatherR2 da conf))).
Proof.
  intros da conf ptx pty ptz bary pt ptdiam hIn_pt hIn_ptdiam hneq_pt_ptdiam Hsec Hsec' Htriangle heq_bary.
  intro abs.
  assert (h_bary:=@same_dist_vertex_notin_sub_circle ptdiam pt bary). 

  assert (h_radius_pt : radius (SEC (ptx :: pty :: ptz :: nil)) =  R2.dist bary pt).
  { rewrite InA_Leibniz in hIn_pt.
    simpl in hIn_pt.
    decompose [or False] hIn_pt;subst.
    - generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity.
    - assert (hperm:PermutationA R2.eq (ptx :: pt :: ptz :: nil) (pt :: ptx :: ptz :: nil)) by permut_3_4.
      rewrite ?hperm in *.
      generalize hperm;intro hperm'.
      apply PermutationA_Leibniz in hperm'.
      rewrite (classify_triangle_compat hperm') in Htriangle.
      rewrite (barycenter_3_pts_compat hperm') in heq_bary.
      generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity.
    - assert (hperm:PermutationA R2.eq (ptx :: pty :: pt :: nil) (pt :: ptx :: pty :: nil)) by permut_3_4.
      rewrite ?hperm in *.
      generalize hperm;intro hperm'.
      apply PermutationA_Leibniz in hperm'.
      rewrite (classify_triangle_compat hperm') in Htriangle.
      rewrite (barycenter_3_pts_compat hperm') in heq_bary.
      generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity. }
  assert (h_radius_ptdiam : radius (SEC (ptx :: pty :: ptz :: nil)) =  R2.dist bary ptdiam).
  { rewrite InA_Leibniz in hIn_ptdiam.
    simpl in hIn_ptdiam.
    decompose [or False] hIn_ptdiam;subst.
    - generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity.
    - assert (hperm:PermutationA R2.eq (ptx :: ptdiam :: ptz :: nil) (ptdiam :: ptx :: ptz :: nil)) by permut_3_4.
      rewrite ?hperm in *.
      generalize hperm;intro hperm'.
      apply PermutationA_Leibniz in hperm'.
      rewrite (classify_triangle_compat hperm') in Htriangle.
      rewrite (barycenter_3_pts_compat hperm') in heq_bary.
      generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity.
    - assert (hperm:PermutationA R2.eq (ptx :: pty :: ptdiam :: nil) (ptdiam :: ptx :: pty :: nil)) by permut_3_4.
      rewrite ?hperm in *.
      generalize hperm;intro hperm'.
      apply PermutationA_Leibniz in hperm'.
      rewrite (classify_triangle_compat hperm') in Htriangle.
      rewrite (barycenter_3_pts_compat hperm') in heq_bary.
      generalize (@equilateral_SEC _ _ _ Htriangle).
      intro h_sec_xyz.
      rewrite <- heq_bary in h_sec_xyz.
      rewrite h_sec_xyz.
      simpl.
      reflexivity. }
  assert (R2.dist ptdiam bary = R2.dist pt bary).
  { setoid_rewrite R2.dist_sym.
    rewrite <- h_radius_ptdiam , <- h_radius_pt.
    reflexivity. }
  apply hneq_pt_ptdiam.
  apply h_bary;auto. 
  assert (h_diameter_after : SEC (Spect.support (!! (round gatherR2 da conf)))
                             = {| center := R2.middle bary ptdiam; radius := / 2 * R2.dist bary ptdiam |}).
  { assert (Hlen := PermutationA_length Hsec').
    destruct (on_SEC (Spect.support (!! (round gatherR2 da conf))))
      as [| x [ | y [|?] ]] eqn:Heq; simpl in Hlen; omega || clear Hlen.
    apply PermutationA_2 in Hsec'; autoclass.
    destruct Hsec' as [ [h1 h2] | [h2 h1]].
    - apply on_SEC_pair_is_diameter.
      rewrite Heq.
      hnf in h1, h2.
      now subst.
    - rewrite middle_comm.
      rewrite R2.dist_sym.
      apply on_SEC_pair_is_diameter.
      rewrite Heq.
      hnf in h1, h2.
      now subst. }
  assert (dist_pt1_mid_is_radius: R2.dist bary (R2.middle bary ptdiam)
                                  = radius (SEC (Spect.support (!! (round gatherR2 da conf))))).
  { rewrite h_diameter_after.
    simpl.
    rewrite R2dist_middle.
    reflexivity. }
  
  rewrite dist_pt1_mid_is_radius.
  rewrite radius_is_max_dist.
  replace (R2.middle bary ptdiam) with (center (SEC (Spect.support (!! (round gatherR2 da conf))))).
  + rewrite R2.dist_sym.
    apply max_dist_le.
    now rewrite InA_Leibniz in abs.
  + now rewrite h_diameter_after.
Qed.

(* Extracting nodupA and ~InA consequences (in terms of <>) *)
Ltac inv_notin H :=
  match type of H with
  | ~ In ?x nil => clear H
  | ~ InA R2.eq ?x ?l =>
    let h := fresh H in
    assert (h:~ In x l); 
    [ rewrite <- InA_Leibniz;assumption | inv_notin h ]
  | ~ In ?x ?l =>
    apply not_in_cons in H;
    let h := fresh H in
    let heq := fresh "heq" in
    destruct H as [heq h];
    try inv_notin h
  end.

Ltac inv_nodup H :=
  lazymatch type of H with
  | NoDupA R2.eq nil => clear H
  | NoDupA R2.eq (?x::nil) => clear H
  | NoDupA R2.eq (?x::?y::?l) =>
    let x := fresh "x" in
    let l := fresh "l" in
    let C := fresh "h_notin" in
    let D := fresh "h_nodup" in
    inversion H as [|x l C D [E F]];
    match type of E with
    | ?x = _ => subst x
    end;
    match type of F with
    | ?x = _ => subst x
    end;
    inv_notin C;
    inv_nodup D
(*     try clear C; try clear D *)
  | NoDupA R2.eq (?x :: ?l) => idtac (* nothing to do here *)
  end.

(** ****  Merging results about the different kinds of triangles  **)

Lemma triangle_next_maj_or_diameter_or_triangle : forall da conf,
  ~forbidden conf ->
  triangle_case conf ->
  (* A majority tower *)
  length (Spect.support (Spect.max (!! (round gatherR2 da conf)))) = 1
  (* No majority tower and we go from equilateral to unclean diameter case *)
  \/ no_Majority (round gatherR2 da conf)
     /\ equilateral_case conf
     /\ length (on_SEC (Spect.support (!! (round gatherR2 da conf)))) = 2
     /\ is_clean (!! (round gatherR2 da conf)) = false
     /\ inclA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da conf)))) ((on_SEC (Spect.support (!! conf))))
  (* No majority tower and the SEC remains the same *)
  \/ no_Majority (round gatherR2 da conf)
     /\ PermutationA R2.eq (on_SEC (Spect.support (!! (round gatherR2 da conf))))
                           (on_SEC (Spect.support (!! conf))).
Proof.
intros da conf Hforbidden [Hmaj [ptx [pty [ptz Hsec]]]].
destruct (Spect.support (Spect.max (!! (round gatherR2 da conf)))) as [| ? [| ? ?]] eqn:Hmax'.
- rewrite Spect.support_nil, Spect.max_empty in Hmax'. elim (spect_non_nil _ Hmax').
- now left.
- right.
  get_case (round gatherR2 da conf). rename Hmaj0 into Hmaj'.
  clear Hmax' e e0 l.
  assert (Hforbidden' : ~forbidden (round gatherR2 da conf)) by now apply never_forbidden.
  assert (Hlen' : Spect.size (!! (round gatherR2 da conf)) >= 3) by now apply not_forbidden_no_majority_size.
  destruct (classify_triangle ptx pty ptz) eqn:Htriangle.
  + (* Equilateral case *)
    assert (Htarget : target (!! conf) = barycenter_3_pts ptx pty ptz) by now apply equilateral_target.
    assert (Hle := no_Majority_on_SEC_length Hmaj').
    destruct (on_SEC (Spect.support (!! (round gatherR2 da conf)))) as [| pt1 [| pt2 [| pt3 l]]] eqn:Hsec';
    cbn in Hle; try omega.
    * (* Valid case: SEC is a pair *)
      destruct (is_clean (!! (round gatherR2 da conf))) eqn:Hclean'.
      -- (* Absurd case: the center of the SEC is not on a diameter *)
        exfalso.
        clear Hle.
        assert (Hcenter := on_SEC_pair_is_diameter _ Hsec').
        assert (PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                   (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)).
        apply diameter_clean_support;auto.
        destruct (is_clean (!! conf)) eqn:Hclean.
        ** assert (inclA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                               (target (!! conf) :: ptx :: pty :: ptz :: nil)).
           { rewrite <- Hsec.
             apply incl_clean_next.
             assumption. }
           rewrite H in H0.
           destruct (List.in_dec R2.eq_dec (target(!! conf)) (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)) as [HIn|HIn].
           --- rewrite Htarget in HIn.
               assert (hNoDup:NoDupA R2.eq (pt1 :: pt2 :: nil)).
               { rewrite <- Hsec'.
                 apply on_SEC_NoDupA.
                 apply Spect.support_NoDupA. }
               cbn in HIn.
               { decompose [or False] HIn; clear HIn.
                  - rewrite (equilateral_target _ Hsec Htriangle), <- H1 in H0.
                    eapply inclA_cons_inv in H0; autoclass; auto.
                    + unfold inclA in H0.
                      assert (hpt1:= H0 pt1 (InA_cons_hd _ eq_refl)).
                      assert (hpt2:= H0 pt2 (InA_cons_tl pt1 (InA_cons_hd _ eq_refl))).
                      rewrite InA_Leibniz in hpt1,hpt2.

                      simpl in hpt1,hpt2;
                      decompose [or False] hpt1;
                      decompose [or False] hpt2;subst;clear hpt1; clear hpt2;
                      try match goal with
                      | H: pt1 = pt2 |- _ =>
                        absurd (InA R2.eq pt1  (pt2 :: nil));
                          [rewrite NoDupA_Leibniz in hNoDup;
                            rewrite NoDup_cons_iff in hNoDup;
                            destruct hNoDup;
                            rewrite InA_Leibniz;
                            assumption
                          | rewrite H; left;reflexivity
                          ]
                          end.
                      * assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                        inversion hNoDup;subst.
                        match goal with
                        | H: ~ InA _ _ _ |- _ => apply H
                        end.
                        left.
                        reflexivity.
                      * rewrite (@barycenter_3_pts_compat pt1 pty pt2 pt1 pt2 pty) in H1;repeat econstructor.
                        rewrite(@classify_triangle_compat pt1 pty pt2 pt1 pt2 pty) in Htriangle;repeat econstructor.
                        assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                        inversion hNoDup;subst.
                        match goal with
                        | H: ~ InA _ _ _ |- _ => apply H
                        end.
                        left.
                        reflexivity. 
                      * rewrite (@barycenter_3_pts_compat pt2 pt1 ptz pt1 pt2 ptz) in H1;repeat econstructor.
                        rewrite(@classify_triangle_compat pt2 pt1 ptz pt1 pt2 ptz) in Htriangle;repeat econstructor.
                        assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                        inversion hNoDup;subst.
                        match goal with
                        | H: ~ InA _ _ _ |- _ => apply H
                        end.
                        left.
                        reflexivity.

                      * rewrite (@barycenter_3_pts_compat ptx pt1 pt2 pt1 pt2 ptx) in H1.
                        -- rewrite (@classify_triangle_compat ptx pt1 pt2 pt1 pt2 ptx) in Htriangle.
                           ++
                             assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                             inversion hNoDup;subst.
                             match goal with
                             | H: ~ InA _ _ _ |- _ => apply H
                             end.
                             left.
                             reflexivity. 
                           ++ now do 3 econstructor.
                        -- now do 3 econstructor.

                      * rewrite (@barycenter_3_pts_compat pt2 pty pt1 pt1 pt2 pty) in H1.
                        -- rewrite (@classify_triangle_compat pt2 pty pt1 pt1 pt2 pty) in Htriangle.
                           ++ assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                              inversion hNoDup;subst.
                              match goal with
                              | H: ~ InA _ _ _ |- _ => apply H
                              end.
                              left.
                              reflexivity.
                           ++ now do 3 econstructor.
                        -- now do 3 econstructor.

                      * rewrite (@barycenter_3_pts_compat ptx pt2 pt1 pt1 pt2 ptx) in H1.
                        -- rewrite (@classify_triangle_compat ptx pt2 pt1 pt1 pt2 ptx) in Htriangle.
                           ++ assert (heq:=middle_barycenter_3_neq _ _ _ Htriangle H1).
                              inversion hNoDup;subst.
                              match goal with
                              | H: ~ InA _ _ _ |- _ => apply H
                              end.
                              left.
                              reflexivity. 
                           ++ permut_3_4.
                        -- econstructor 4 with (pt2 :: ptx :: pt1 :: nil); now do 3 econstructor.
                    + apply middle_diff.
                      inversion hNoDup; subst.
                      intro abs; subst.
                      apply H4.
                      left; reflexivity.
                  - (* if (target (conf)) is in (SEC (round conf)) then two previously
                       SEC-towers have moved to (target (conf)). therefore there are
                       two tower => majority (or contradicting forbidden).  *)
                    
                    assert (hIn:In pt2 (ptx :: pty :: ptz :: nil)).
                    { assert (In pt2 (target (!! conf) :: ptx :: pty :: ptz :: nil)).
                      { rewrite <- Hsec.
                        apply InA_Leibniz.
                        eapply incl_clean_next with da;auto.
                        assert (InA R2.eq pt2 (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                        { rewrite Hsec'.
                          right;left;reflexivity. }
                        rewrite InA_Leibniz in H1 |-*.
                        apply on_SEC_In.
                        assumption. }
                      inversion H1.
                      - exfalso.
                        rewrite <- H2 in Htarget.
                        rewrite Htarget in H3.
                        subst.
                        rewrite H3 in hNoDup.
                        inversion  hNoDup.
                        apply H6.
                        left;reflexivity.
                      - assumption. }
                    unfold inclA in H0.
                    assert (hmid:InA R2.eq (R2.middle pt1 pt2) (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)).
                    { left.
                      reflexivity. }
                    specialize (H0 (R2.middle pt1 pt2) hmid).
                    rewrite InA_Leibniz in H0.
                    simpl in H0.
                    decompose [or False] H0;clear H0.
                    + rewrite Htarget in H1.
                      rewrite <- H2 in H1.
                      elim (@middle_diff pt1 pt2).
                      * intro abs. rewrite abs in hNoDup. inversion hNoDup.
                        apply H4.
                        left; reflexivity.
                      * rewrite <- H1.
                        left;reflexivity.
                    + assert(ptx = pt2).
                      { rewrite middle_comm in H3.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=ptx) (white:=pt1);eauto.
                        left.
                        reflexivity. }
                      subst ptx.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(pty = pt2).
                      { rewrite middle_comm in H1.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=pty) (white:=pt1);eauto.
                        right;left.
                        reflexivity. }
                      subst pty.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(ptz = pt2).
                      { rewrite middle_comm in H3.
                        eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt2) (mid:=ptz) (white:=pt1);eauto.
                        right;right;left.
                        reflexivity. }
                      subst ptz.
                      rewrite middle_comm in H0.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                  - (* if (target (conf)) is in (SEC (round conf)) then two previously
                       SEC-towers have moved to (target (conf)). therefore there are
                       two tower => majority (or contradicting forbidden).  *)

                    assert (hIn:In pt1 (ptx :: pty :: ptz :: nil)).
                    { assert (In pt1 (target (!! conf) :: ptx :: pty :: ptz :: nil)).
                      { rewrite <- Hsec.
                        apply InA_Leibniz.
                        eapply incl_clean_next with da;auto.
                        assert (InA R2.eq pt1 (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                        { rewrite Hsec'.
                          left;reflexivity. }
                        rewrite InA_Leibniz in H2 |-*.
                        apply on_SEC_In.
                        assumption. }
                      inversion H2.
                      - exfalso.
                        rewrite H3 in Htarget.
                        rewrite <- Htarget in H1.
                        subst pt2.
                        inversion  hNoDup.
                        apply H5.
                        left;reflexivity.
                      - assumption. }
                    unfold inclA in H0.
                    assert (hmid:InA R2.eq (R2.middle pt1 pt2) (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)).
                    { left.
                      reflexivity. }
                    specialize (H0 (R2.middle pt1 pt2) hmid).
                    rewrite InA_Leibniz in H0.
                    simpl in H0.
                    decompose [or False] H0;clear H0.
                    + rewrite Htarget in H2.
                      rewrite <- H1 in H2.
                      elim (@middle_diff pt1 pt2).
                      * intro abs. rewrite abs in hNoDup. inversion hNoDup.
                        apply H4.
                        left; reflexivity.
                      * rewrite <- H2.
                        right;left;reflexivity.
                    + assert(ptx = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=ptx) (white:=pt2);eauto.
                        left.
                        reflexivity. }
                      subst ptx.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(pty = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=pty) (white:=pt2);eauto.
                        right;left.
                        reflexivity. }
                      subst pty.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity.
                    + assert(ptz = pt1).
                      { eapply equilateral_barycenter_degenerated_gen
                        with (ptopp:=pt1) (mid:=ptz) (white:=pt2);eauto.
                        right;right;left.
                        reflexivity. }
                      subst ptz.
                      rewrite middle_eq in H0.
                      rewrite H0 in hNoDup.
                      inversion hNoDup.
                      apply H4.
                      left.
                      reflexivity. }
            --- (* (ptx :: pty :: ptz :: nil) = (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)
                   contradiction with calssify_triangle = equilateral *)
              assert (PermutationA R2.eq (ptx :: pty :: ptz :: nil) (R2.middle pt1 pt2 :: pt1 :: pt2 :: nil)).
              { apply inclA_skip in H0;autoclass.
                - symmetry.
                  apply NoDupA_inclA_length_PermutationA with (1:=R2.eq_equiv);auto.
                  + rewrite <- H.
                    apply Spect.support_NoDupA;auto.
                  + rewrite <- Hsec.
                    apply on_SEC_NoDupA;auto.
                    apply Spect.support_NoDupA;auto.
                - rewrite InA_Leibniz.
                  assumption. }
              assert (classify_triangle (R2.middle pt1 pt2) pt1 pt2 = Equilateral).
              { rewrite PermutationA_Leibniz in H1. now rewrite (classify_triangle_compat H1) in Htriangle. }
              functional inversion H2. clear H2.
              rewrite -> ?Rdec_bool_true_iff in *.
              rewrite R2.dist_sym in H3.
              rewrite R2dist_middle in H3.
              assert (R2.dist pt1 pt2 = 0%R).
              { lra. }
              apply R2.dist_defined in H2.
              assert (hNoDup:NoDupA R2.eq (pt1 :: pt2 :: nil)).
              { rewrite <- Hsec'.
                apply on_SEC_NoDupA.
                apply Spect.support_NoDupA. }

              rewrite H2 in hNoDup.
              inversion hNoDup.
              apply H7. left;reflexivity.
         ** rewrite <- dirty_next_on_SEC_same in Hsec;auto.
            rewrite Hsec' in Hsec.
            assert (length (pt1 :: pt2 :: nil) = length (ptx :: pty :: ptz :: nil)).
            { rewrite Hsec.
              reflexivity. }
            simpl in H0;omega.

      -- (* Valid case: the center of the SEC is not on a diameter *)
         left. repeat split; trivial; eauto.
         assert (h_clean_conf:is_clean (!! conf) = true).
         { destruct (bool_dec (is_clean (!! conf)) true) as [ heq_clean_true | heq_clean_false].
           - assumption.
           - exfalso.
             apply not_true_is_false in heq_clean_false.
             assert (hdirty:=@dirty_next_SEC_same da conf Hmaj heq_clean_false).
             setoid_rewrite <- (@dirty_next_on_SEC_same da conf Hmaj heq_clean_false) in Hsec.
             rewrite Hsec' in Hsec.
             apply PermutationA_length in Hsec.
             simpl in Hsec.
             omega. }

         assert (hincl_round:inclA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                   (target (!! conf) :: on_SEC (Spect.support (!! conf)))).
         { eapply incl_clean_next ;eauto. }
         rewrite Htarget in hincl_round.
         rewrite Hsec in hincl_round.
         assert (h_incl_pt1_pt2 : inclA R2.eq (pt1 :: pt2 :: nil)
                                              (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)).
         { transitivity (Spect.support (!! (round gatherR2 da conf))).
           -  rewrite <- Hsec'.
             unfold on_SEC.
             unfold inclA.
             intros x H1.
             rewrite filter_InA in H1.
             destruct H1.
             assumption.
             autoclass. 
           - assumption. }

         assert (hnodup: NoDupA R2.eq (pt1 :: pt2 :: nil)).
         { rewrite <- Hsec'. 
           apply on_SEC_NoDupA.
           apply Spect.support_NoDupA. }

         assert (hnodupxyz: NoDupA R2.eq (ptx :: pty :: ptz :: nil)).
         { rewrite <- Hsec. 
           apply on_SEC_NoDupA.
           apply Spect.support_NoDupA. }
         inv_nodup hnodupxyz.
         inv_nodup hnodup.
         destruct (R2.eq_dec pt1 (barycenter_3_pts ptx pty ptz)) as [heq_pt1_bary | hneq_pt1_bary].
         ++ { exfalso.
              assert(hpermut_conf: PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                                      (pt1 :: pt2 :: nil)).
              { rewrite heq_pt1_bary in heq2, h_incl_pt1_pt2.
                apply inclA_cons_inv in h_incl_pt1_pt2; autoclass.
                + red in h_incl_pt1_pt2.
                  assert (h_pt2:InA R2.eq pt2 (pt2 :: nil)).
                  { left;reflexivity. }
                  specialize (h_incl_pt1_pt2 pt2 h_pt2).
                  clear h_pt2.
                  inversion h_incl_pt1_pt2 as [pt lpt heq_pt2_ptx [__h heq_lpt]| pt lpt h_in_pt2_lpt [__h heq_lpt]].
                  (* pt2 = ptx *)
                  * unfold R2.eq, R2def.eq in heq_pt2_ptx.
                    subst.
                    assert (hpermut:PermutationA R2.eq (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                 (pty :: ptz :: barycenter_3_pts ptx pty ptz :: ptx :: nil))
                      by permut_3_4.
                    rewrite hpermut in hincl_round;clear hpermut.
                    assert (h_ynotin:~ InA R2.eq pty (Spect.support (!! (round gatherR2 da conf)))).
                    { eapply SEC_3_to_2;eauto.
                      - repeat econstructor; reflexivity.
                      - rewrite Hsec'.
                        reflexivity. }
                    assert (h_znotin:~ InA R2.eq ptz (Spect.support (!! (round gatherR2 da conf)))).
                    { eapply SEC_3_to_2;eauto.
                      - repeat econstructor; reflexivity.
                      - rewrite Hsec'.
                        reflexivity. }
                    do 2 (apply inclA_skip in hincl_round; autoclass).
                    apply NoDupA_inclA_length_PermutationA; autoclass.
                    -- apply Spect.support_NoDupA.
                    -- now rewrite heq_pt1_bary.
                    -- simpl.
                       transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                       ++ now rewrite Hsec'.
                       ++ unfold on_SEC.
                          rewrite filter_length.
                          omega.

                  * { (* InA R2.eq pt2 (pt2 :: nil)  *)
                      subst pt.
                      subst lpt.
                      inversion h_in_pt2_lpt
                        as [pt lpt heq_pt2_pty [__h heq_lpt] | pt lpt h_in_pt2_lpt' [__h heq_lpt]].
                      (* pt2 = pty *)
                      * unfold R2.eq, R2def.eq in heq_pt2_pty.
                        subst.
                        assert (Hperm:PermutationA R2.eq (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                         (ptx :: ptz :: barycenter_3_pts ptx pty ptz :: pty :: nil))
                          by permut_3_4.
                        rewrite Hperm in hincl_round;clear Hperm.
                        assert (h_ynotin:~ InA R2.eq ptx (Spect.support (!! (round gatherR2 da conf)))).
                        { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                        assert (h_znotin:~ InA R2.eq ptz (Spect.support (!! (round gatherR2 da conf)))).
                        { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                        apply inclA_skip in hincl_round;autoclass.
                        apply inclA_skip in hincl_round;autoclass.
                        apply NoDupA_inclA_length_PermutationA;autoclass.
                        -- apply Spect.support_NoDupA.                   
                        -- rewrite heq_pt1_bary.
                           assumption.
                        -- simpl.
                           transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                           ++ rewrite Hsec'.
                              reflexivity.
                           ++ unfold on_SEC.
                              rewrite filter_length.
                              omega.
                      * subst pt.
                        subst lpt.
                        { inversion h_in_pt2_lpt'
                            as [pt lpt heq_pt2_pty [__h heq_lpt] | pt lpt h_in_pt2_lpt'' [__h heq_lpt]].
                          (* pt2 = pty *)
                          * unfold R2.eq, R2def.eq in heq_pt2_pty.
                            subst.
                            assert (Hperm : PermutationA R2.eq
                                      (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                      (ptx :: pty :: barycenter_3_pts ptx pty ptz :: ptz :: nil))
                              by permut_3_4.
                            rewrite Hperm in hincl_round;clear Hperm.
                            assert (h_ynotin:~ InA R2.eq ptx (Spect.support (!! (round gatherR2 da conf)))).
                            { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                            assert (h_znotin:~ InA R2.eq pty (Spect.support (!! (round gatherR2 da conf)))).
                            { eapply SEC_3_to_2;eauto.
                          - repeat econstructor; reflexivity. 
                          - rewrite Hsec'.
                            reflexivity. }
                            apply inclA_skip in hincl_round;autoclass.
                            apply inclA_skip in hincl_round;autoclass.
                            apply NoDupA_inclA_length_PermutationA;autoclass.
                            -- apply Spect.support_NoDupA.                   
                            -- now rewrite heq_pt1_bary.
                            -- simpl.
                               transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                               ++ rewrite Hsec'.
                                  reflexivity.
                               ++ unfold on_SEC.
                                  rewrite filter_length.
                                  omega.
                          * inversion h_in_pt2_lpt''. } }
                  + intro Hin. apply heq2. now inversion Hin. }
                - rewrite Spect.size_spec in Hlen'.
                  rewrite hpermut_conf in Hlen'.
                  simpl in Hlen'.
                  omega. }
         ++ { destruct (R2.eq_dec pt2 (barycenter_3_pts ptx pty ptz)) as [heq_pt2_bary | hneq_pt2_bary].
              ++ { exfalso.
                   assert(hpermut_conf: PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                                           (pt2 :: pt1 :: nil)).
                   { assert (hpermut12:PermutationA R2.eq (pt1 :: pt2 :: nil) (pt2 :: pt1 :: nil))  by permut_3_4.
                     rewrite hpermut12 in h_incl_pt1_pt2.
                     rewrite heq_pt2_bary in heq2, h_incl_pt1_pt2.
                     apply inclA_cons_inv in h_incl_pt1_pt2;autoclass.
                     + red in h_incl_pt1_pt2.
                       assert (h_pt1:InA R2.eq pt1 (pt1 :: nil)).
                       { left;reflexivity. }
                       specialize (h_incl_pt1_pt2 pt1 h_pt1).
                       clear h_pt1.
                       inversion h_incl_pt1_pt2 as [pt lpt heq_pt1_ptx [__h heq_lpt]
                                                  | pt lpt h_in_pt1_lpt [__h heq_lpt]].
                       (* pt1 = ptx *)
                       * unfold R2.eq, R2def.eq in heq_pt1_ptx.
                         subst ptx.
                         subst pt.
                         assert (Hperm:PermutationA R2.eq (barycenter_3_pts pt1 pty ptz :: pt1 :: pty :: ptz :: nil)
                                                      (pty :: ptz :: barycenter_3_pts pt1 pty ptz :: pt1 :: nil))
                           by permut_3_4.
                         rewrite Hperm in hincl_round;clear Hperm.
                         assert (h_ynotin:~ InA R2.eq pty (Spect.support (!! (round gatherR2 da conf)))).
                         { eapply SEC_3_to_2;eauto.
                           - repeat econstructor; reflexivity.
                           - rewrite Hsec'.
                             permut_3_4. }
                         assert (h_znotin:~ InA R2.eq ptz (Spect.support (!! (round gatherR2 da conf)))).
                         { eapply SEC_3_to_2;eauto.
                           - repeat econstructor; reflexivity.
                           - rewrite Hsec'.
                             permut_3_4. }
                         apply inclA_skip in hincl_round;autoclass.
                         apply inclA_skip in hincl_round;autoclass.
                         apply NoDupA_inclA_length_PermutationA;autoclass.
                         -- apply Spect.support_NoDupA.                   
                         -- repeat constructor.
                            ++ intro Habs.
                               inversion_clear Habs.
                               ** congruence.
                               ** now rewrite InA_nil in *.
                            ++ now rewrite InA_nil.
                         -- now rewrite heq_pt2_bary.
                         -- simpl.
                            transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                            ++ now rewrite Hsec'.
                            ++ unfold on_SEC.
                               rewrite filter_length.
                               omega.

                       * { (* InA R2.eq pt1 (pt1 :: nil)  *)
                           subst pt.
                           subst lpt.
                           inversion h_in_pt1_lpt as [pt lpt heq_pt1_pty [__h heq_lpt]
                                                     | pt lpt h_in_pt1_lpt' [__h heq_lpt]].
                           (* pt1 = pty *)
                           * unfold R2.eq, R2def.eq in heq_pt1_pty.
                             subst.
                             assert (Hperm : PermutationA R2.eq
                                       (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                       (ptx :: ptz :: barycenter_3_pts ptx pty ptz :: pty :: nil))
                               by permut_3_4.
                             rewrite Hperm in hincl_round;clear Hperm.
                             assert (h_xnotin:~ InA R2.eq ptx (Spect.support (!! (round gatherR2 da conf)))).
                             { eapply SEC_3_to_2;eauto.
                               - repeat econstructor; reflexivity.
                               - rewrite Hsec'.
                                 permut_3_4. }
                             assert (h_znotin:~ InA R2.eq ptz (Spect.support (!! (round gatherR2 da conf)))).
                             { eapply SEC_3_to_2;eauto.
                               - repeat econstructor; reflexivity.
                               - rewrite Hsec'.
                                 permut_3_4. }
                             apply inclA_skip in hincl_round;autoclass.
                             apply inclA_skip in hincl_round;autoclass.
                             apply NoDupA_inclA_length_PermutationA;autoclass.
                             -- apply Spect.support_NoDupA.                   
                             -- repeat constructor.
                                ++ intro Habs.
                                   inversion_clear Habs.
                                   ** congruence.
                                   ** now rewrite InA_nil in *.
                                ++ now rewrite InA_nil.
                             -- rewrite heq_pt2_bary.
                                assumption.
                             -- simpl.
                                transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                                ++ rewrite Hsec'.
                                   reflexivity.
                                ++ unfold on_SEC.
                                   rewrite filter_length.
                                   omega.
                           * subst pt.
                             subst lpt.
                             { inversion h_in_pt1_lpt'
                                as [pt lpt heq_pt1_ptz [__h heq_lpt] | pt lpt h_in_pt1_lpt'' [__h heq_lpt]].
                               (* pt1 = pty *)
                               * unfold R2.eq, R2def.eq in heq_pt1_ptz.
                                 subst.
                                 assert (hpermut : PermutationA R2.eq
                                                     (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)
                                                     (ptx :: pty :: barycenter_3_pts ptx pty ptz :: ptz :: nil))
                                   by permut_3_4.
                                 rewrite hpermut in hincl_round;clear hpermut.
                                 assert (h_xnotin:~ InA R2.eq ptx (Spect.support (!! (round gatherR2 da conf)))).
                                 { eapply SEC_3_to_2;eauto.
                                   - repeat econstructor; reflexivity.
                                   - rewrite Hsec'.
                                     permut_3_4. }
                                 assert (h_ynotin:~ InA R2.eq pty (Spect.support (!! (round gatherR2 da conf)))).
                                 { eapply SEC_3_to_2; eauto.
                                   - repeat econstructor; reflexivity.
                                   - rewrite Hsec'.
                                     permut_3_4. }

                                 do 2 (apply inclA_skip in hincl_round; autoclass).
                                 apply NoDupA_inclA_length_PermutationA; autoclass.
                                 -- apply Spect.support_NoDupA.
                                 -- repeat constructor.
                                    ++ intro Habs.
                                       inversion_clear Habs.
                                       ** congruence.
                                       ** now rewrite InA_nil in *.
                                    ++ now rewrite InA_nil.
                                 -- now rewrite heq_pt2_bary.
                                 -- simpl.
                                    transitivity (length (on_SEC (Spect.support (!! (round gatherR2 da conf))))).
                                    ++ rewrite Hsec'.
                                       reflexivity.
                                    ++ unfold on_SEC.
                                       rewrite filter_length.
                                       omega.
                               * inversion h_in_pt1_lpt''. } }
                     + intro abs.
                       inversion abs.
                       * apply heq2.
                         symmetry.
                         assumption.
                       * rewrite <- InA_nil.
                         eauto. }
                   + rewrite Spect.size_spec in Hlen'.
                     rewrite hpermut_conf in Hlen'.
                     simpl in Hlen'.
                     omega. }

              ++ rewrite Hsec.
                 intros pt hin.
                 assert (h:=h_incl_pt1_pt2 _ hin).
                 inversion_clear h.
                 ** inversion hin.
                    --- subst.
                        rewrite H1 in H.
                        contradiction.
                    --- subst.
                        inversion H1.
                        +++ rewrite H2 in H.
                            contradiction.
                        +++ inversion H2.
                 ** assumption. }

    * (* Valid case: SEC is a triangle *)
      right. split; trivial.
      rewrite <- Hsec'.
      (* TODO: the SEC has not changed *)
      destruct (is_clean (!! conf)) eqn:Hclean.
      -- destruct (moving gatherR2 da conf) as [| gmove ?] eqn:Hmoving.
         ++ apply no_moving_same_conf in Hmoving. now rewrite Hmoving.
         ++ assert (Hperm' : PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                                (barycenter_3_pts ptx pty ptz :: ptx :: pty :: ptz :: nil)).
            { assert ((!! (round gatherR2 da conf))[target (!! conf)] > 0).
              { apply le_lt_trans with ((!! conf)[target (!! conf)]); try omega.
                rewrite increase_move_iff.
                exists gmove. split.
                - apply destination_is_target; trivial.
                  rewrite Hmoving. now left.
                - now rewrite <- moving_spec, Hmoving; left. }
              apply (NoDupA_inclA_length_PermutationA _).
              - apply Spect.support_NoDupA.
              - apply equilateral_barycenter_NoDupA; trivial.
                assert (Hnodup : NoDupA R2.eq (on_SEC (Spect.support (!! conf)))).
                { apply on_SEC_NoDupA, Spect.support_NoDupA. }
                rewrite Hsec in Hnodup. inversion Hnodup. intuition.
              - rewrite <- Htarget, <- Hsec. now apply incl_clean_next.
              - rewrite <- Spect.size_spec.
                destruct (Spect.size (!! (round gatherR2 da conf))) as [| [| [| [| ?]]]] eqn:Hlen; simpl; try omega.
                exfalso.
                assert (l = nil).
                { destruct l as [| pt4 l]; trivial.
                  cut (4 + length l <= 3); try omega.
                  change (4 + length l) with (length (pt1 :: pt2 :: pt3 :: pt4 :: l)).
                  rewrite <- Hsec', <- Hlen, Spect.size_spec.
                  apply (NoDupA_inclA_length R2.eq_equiv).
                  - apply on_SEC_NoDupA, Spect.support_NoDupA.
                  - unfold on_SEC. intro. rewrite (filter_InA _). intuition. }
                subst.
                assert (Hperm' : PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                                    (pt1 :: pt2 :: pt3 :: nil)).
                { symmetry.
                  apply (NoDupA_inclA_length_PermutationA _).
                  - rewrite <- Hsec'. apply on_SEC_NoDupA, Spect.support_NoDupA.
                  - apply Spect.support_NoDupA.
                  - rewrite <- Hsec'. unfold on_SEC. intro. rewrite (filter_InA _). intuition.
                  - rewrite <- Spect.size_spec. cbn. omega. }
                rewrite <- Hsec' in Hperm'.
                (* Triangle equilatéral: comme qqchose bouge et que on est encore avec 3
                   colonne après, une colonne s'est déplacée vers le barycentre, contradiction:
                   le barycentre ne peut pas être sur le SEC. *)
                assert (Hnodup : NoDupA R2.eq (ptx :: pty :: ptz :: nil)).
                { rewrite <- Hsec. apply on_SEC_NoDupA, Spect.support_NoDupA. }
                assert (Hex : exists pta ptb ptc,
                              PermutationA R2.eq (pta :: ptb :: ptc :: nil) (ptx :: pty :: ptz :: nil)
                              /\ PermutationA R2.eq (barycenter_3_pts ptx pty ptz :: pta :: ptb ::nil)
                                                    (pt1 :: pt2 :: pt3 :: nil)).
                { assert (hincl:=incl_clean_next da conf Hclean).
                  rewrite Hsec in hincl.
                  rewrite Hperm', Hsec' in hincl.
                  assert (hbary : InA R2.eq (barycenter_3_pts ptx pty ptz)
                                            (Spect.support (!! (round gatherR2 da conf)))).
                  { rewrite Spect.support_In.
                    rewrite <- Htarget.
                    assumption. }
                  rewrite Hperm',Hsec' in hbary.
                  apply PermutationA_split in hbary; autoclass.
                  destruct hbary as [l hpermut_l].
                  setoid_rewrite hpermut_l.
                  assert (Hlength := PermutationA_length hpermut_l).
                  destruct l as [| pta [| ptb [| ? ?]]]; simpl in Hlength; omega || clear Hlength.
                  inv_nodup Hnodup.
                  assert (Hnodup' := equilateral_barycenter_NoDupA _ Htriangle ltac:(auto)).
                  assert (Hnodup123 : NoDupA R2.eq (pt1 :: pt2 :: pt3 :: nil)).
                  { rewrite <- Hsec'. apply on_SEC_NoDupA, Spect.support_NoDupA. }
                  inv_nodup Hnodup'.
                  rewrite hpermut_l in Hnodup123. inv_nodup Hnodup123.
                  assert (Hpta : InA R2.eq pta (ptx :: pty :: ptz :: nil)).
                  { rewrite hpermut_l, Htarget in hincl. apply (inclA_cons_inv _ h_notin4) in hincl.
                    apply hincl. now constructor. }
                  assert (Hptb : InA R2.eq ptb (ptx :: pty :: ptz :: nil)).
                  { rewrite hpermut_l, Htarget in hincl. apply (inclA_cons_inv _ h_notin4) in hincl.
                    apply hincl. now do 2 constructor. }
                  rewrite InA_Leibniz in Hpta, Hptb. simpl in Hpta, Hptb.
                  exists pta, ptb.
                  cut (exists ptc, PermutationA R2.eq (pta :: ptb :: ptc :: nil) (ptx :: pty :: ptz :: nil)).
                  - intros [ptc Hptc]. exists ptc. now split.
                  - decompose [or False] Hpta; decompose [or False] Hptb;
                    lazymatch goal with
                      | Ha : ?pt = pta, Hb : ?pt = ptb |- _ => congruence
                      | Ha : ?pt = pta, Hb : ?pt' = ptb |- _ =>
                          match goal with
                            | H : pt <> ?ptc, H' : pt' <> ?ptc |- _ => exists ptc
                            | H : ?ptc <> pt, H' : pt' <> ?ptc |- _ => exists ptc
                            | H : pt <> ?ptc, H' : ?ptc <> pt' |- _ => exists ptc
                            | H : ?ptc <> pt, H' : ?ptc <> pt' |- _ => exists ptc
                          end
                    end; subst; permut_3_4. }
                destruct Hex as [pta [ptb [ptc [Hpermxyz Hperm]]]].
                pose (better_SEC := {| center := R2.middle pta ptb; radius := /2 * R2.dist pta ptb |}).
                assert (Hbary_strict : (R2.dist (barycenter_3_pts ptx pty ptz) (center better_SEC)
                                        < radius better_SEC)%R).
                { rewrite PermutationA_Leibniz in Hpermxyz. rewrite <- (barycenter_3_pts_compat Hpermxyz).
                  unfold better_SEC. simpl. rewrite R2norm_dist. unfold barycenter_3_pts, R2.middle.
                  replace (/ 3 * (pta + (ptb + ptc)) - 1 / 2 * (pta + ptb))%R2
                    with (/6 * (ptc + ptc - (pta + ptb)))%R2 by (destruct pta, ptb, ptc; simpl; f_equal; field).
                  rewrite R2norm_mul. rewrite Rabs_pos_eq; try lra; [].
                  rewrite <- R2norm_dist.
                  cut (R2.dist (ptc + ptc) (pta + ptb) < 3 * R2.dist pta ptb)%R; try lra; [].
                  eapply Rle_lt_trans.
                  - apply (R2.triang_ineq _ (ptc + pta)%R2).
                  - setoid_rewrite R2.add_comm at 2 4. do 2 rewrite R2add_dist.
                    rewrite <- (classify_triangle_compat Hpermxyz) in Htriangle.
                    rewrite classify_triangle_Equilateral_spec in Htriangle.
                    destruct Htriangle as [Heq1 Heq2].
                    setoid_rewrite R2.dist_sym at 1 2. rewrite Heq1, Heq2.
                    assert (Hle' := R2.dist_pos ptb ptc).
                    rewrite <- PermutationA_Leibniz in Hpermxyz. rewrite <- Hpermxyz in Hnodup. inv_nodup Hnodup.
                    rewrite <- R2.dist_defined in heq1. lra. }
                assert (enclosing_circle better_SEC (barycenter_3_pts ptx pty ptz :: pta :: ptb :: nil)).
                { intros pt hin.
                  simpl in hin.
                  decompose [or False] hin;subst pt;clear hin.
                  - apply Rlt_le. 
                    assumption.
                  - unfold better_SEC ; simpl.
                    rewrite R2dist_middle.
                    reflexivity.
                  - unfold better_SEC ; simpl.
                    rewrite middle_comm.
                    rewrite R2dist_middle.
                    rewrite R2.dist_sym.
                    reflexivity. }
                assert (better_SEC = (SEC (Spect.support (!! (round gatherR2 da conf))))).
                { rewrite PermutationA_Leibniz in Hperm',Hperm.
                  rewrite Hperm',Hsec',<-Hperm.
                  apply SEC_unicity.
                  - assumption.
                  - unfold better_SEC.
                    simpl.
                    apply SEC_min_radius; intuition. }
                absurd (on_circle better_SEC (barycenter_3_pts  ptx pty ptz)=true).
                + rewrite on_circle_true_iff.
                  apply Rlt_not_eq.
                  assumption.
                + rewrite H1.
                  eapply proj2.
                  rewrite <- filter_InA;autoclass.
                  unfold on_SEC in Hsec'.
                  rewrite Hsec'.
                  rewrite <- Hperm.
                  constructor.
                  reflexivity.
                }
            apply (NoDupA_equivlistA_PermutationA _).
            ** apply on_SEC_NoDupA, Spect.support_NoDupA.
            ** apply on_SEC_NoDupA, Spect.support_NoDupA.
            ** rewrite Hperm', Hsec.
               rewrite on_SEC_barycenter_triangle, <- Hsec, on_SEC_idempotent; try reflexivity.
               intros [? ?]. subst.
               assert (Hnodup : NoDupA R2.eq (on_SEC (Spect.support (!! conf)))).
               { apply on_SEC_NoDupA, Spect.support_NoDupA. }
               rewrite Hsec in Hnodup. inversion Hnodup. intuition.
      -- now apply dirty_next_on_SEC_same.
  + (* Isosceles case *)
    assert (Htarget := isosceles_target conf Hsec Htriangle).
    right. split; trivial.
    destruct (is_clean (!! conf)) eqn:Hclean.
    -- destruct (moving gatherR2 da conf) as [| gmove ?] eqn:Hmoving.
       ++ apply no_moving_same_conf in Hmoving. now rewrite Hmoving.
       ++ assert (Hperm' : PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                        (ptx :: pty :: ptz :: nil)).
          { assert (forall x, In x (gmove :: l) -> (round gatherR2 da conf) x = vertex).
            { rewrite <- Htarget.
              intros x H3.
              apply destination_is_target; auto.
              rewrite Hmoving.
              assumption. }
            assert (h_vertex:=isoscele_vertex_is_vertex _ _ _ Htriangle).
            assert (H_supp: PermutationA R2.eq (Spect.support (!! conf)) (ptx :: pty :: ptz :: nil)).
            { rewrite is_clean_spec in Hclean.
              unfold SECT in Hclean.
              rewrite Hsec in Hclean.
              apply inclA_cons_InA in Hclean;autoclass;auto.
              - apply NoDupA_inclA_length_PermutationA;autoclass.
                + apply Spect.support_NoDupA;auto.
                + rewrite <- Hsec.
                  apply on_SEC_NoDupA.
                  apply Spect.support_NoDupA;auto.
                + transitivity (length (on_SEC (Spect.support (!! conf)))).
                  -- rewrite Hsec.
                     reflexivity.
                  -- unfold on_SEC. 
                     rewrite filter_length.
                     omega.
              - rewrite Htarget.
                assumption. }

            apply NoDupA_inclA_length_PermutationA; autoclass.
            - apply Spect.support_NoDupA.
            - rewrite <- Hsec.
              apply on_SEC_NoDupA, Spect.support_NoDupA.
            - transitivity (target (!! conf) :: ptx :: pty :: ptz :: nil).
              + rewrite <- H_supp.
                apply incl_next.
              + apply inclA_Leibniz.
                apply incl_cons.
                * rewrite Htarget.
                  apply InA_Leibniz.
                  assumption.
                * apply inclA_Leibniz.
                  reflexivity.
            - rewrite Spect.size_spec in Hlen'.
              apply Hlen'. }
          rewrite Hperm'.
          rewrite <- Hsec.
          apply on_SEC_idempotent.
    -- now apply dirty_next_on_SEC_same.
  + (* Scalene case *)
    assert (Htarget := scalene_target conf Hsec Htriangle).
    right. split; trivial.
    (* TODO: the SEC has not changed, same thing? *)
    destruct (is_clean (!! conf)) eqn:Hclean.
    -- destruct (moving gatherR2 da conf) as [| gmove ?] eqn:Hmoving.
       ++ apply no_moving_same_conf in Hmoving. now rewrite Hmoving.
       ++
         remember (opposite_of_max_side ptx pty ptz) as vertex.
         assert (Hperm' : PermutationA R2.eq (Spect.support (!! (round gatherR2 da conf)))
                                        (ptx :: pty :: ptz :: nil)).
          { assert (forall x, In x (gmove :: l) -> (round gatherR2 da conf) x = vertex).
            { rewrite <- Htarget.
              intros x H3.
              apply destination_is_target;auto.
              rewrite Hmoving.
              assumption. }
            assert (h_vertex:=scalene_vertex_is_vertex _ _ _ Htriangle).
            assert (H_supp: PermutationA R2.eq (Spect.support (!! conf)) (ptx :: pty :: ptz :: nil)).
            { rewrite is_clean_spec in Hclean.
              unfold SECT in Hclean.
              rewrite Hsec in Hclean.
              apply inclA_cons_InA in Hclean;autoclass;auto.
              - apply NoDupA_inclA_length_PermutationA;autoclass.
                + apply Spect.support_NoDupA;auto.
                + rewrite <- Hsec.
                  apply on_SEC_NoDupA.
                  apply Spect.support_NoDupA;auto.
                + transitivity (length (on_SEC (Spect.support (!! conf)))).
                  -- rewrite Hsec.
                     reflexivity.
                  -- unfold on_SEC. 
                     rewrite filter_length.
                     omega.
              - subst.
                rewrite Htarget.
                assumption. }

            apply NoDupA_inclA_length_PermutationA; autoclass.
            - apply Spect.support_NoDupA.
            - rewrite <- Hsec.
              apply on_SEC_NoDupA, Spect.support_NoDupA.
            - transitivity (target (!! conf) :: ptx :: pty :: ptz :: nil).
              + rewrite <- H_supp.
                apply incl_next.
              + apply inclA_Leibniz.
                apply incl_cons.
                * subst.
                  rewrite Htarget.
                  apply InA_Leibniz.
                  assumption.
                * apply inclA_Leibniz.
                  reflexivity.
            - rewrite Spect.size_spec in Hlen'.
              apply Hlen'. }
          rewrite Hperm'.
          rewrite <- Hsec.
          apply on_SEC_idempotent.
    -- now apply dirty_next_on_SEC_same.
Qed.

(** ***  Lemmas about the generic case  **)

Lemma clean_generic_next_generic_same_SEC : forall da config,
  generic_case config ->
  generic_case (round gatherR2 da config) ->
  SEC (Spect.support (!! (round gatherR2 da config))) = SEC (Spect.support (!! config)).
Proof.
intros da config Hcase Hcase'.
destruct (is_clean (!! config)) eqn:Hclean; try (now destruct Hcase; apply dirty_next_SEC_same); [].
assert (Hincl' := incl_clean_next da config Hclean).
destruct Hcase' as [Hmaj' [pt1' [pt2' [pt3' [pt4' [l' Hperm']]]]]].
(* These positions are different *)
assert (Hnodup : NoDupA R2.eq (pt1' :: pt2' :: pt3' :: pt4' :: l')).
{ rewrite <- Hperm'. apply on_SEC_NoDupA, Spect.support_NoDupA. }
inv_nodup Hnodup.
inversion_clear Hnodup. inversion_clear H0. inversion_clear H2.
assert (Hneq12 : pt1' <> pt2') by intuition.
assert (Hneq13 : pt1' <> pt3') by intuition.
assert (Hneq14 : pt1' <> pt4') by intuition.
assert (Hneq23 : pt2' <> pt3') by intuition.
assert (Hneq24 : pt2' <> pt4') by intuition.
assert (Hneq34 : pt3' <> pt4') by intuition.
clear H H0 H1 H3.
(* There are robots occupying these positions *)
assert (Hid1 : exists id1, round gatherR2 da config id1 = pt1').
{ rewrite <- Spect.from_config_In,  <- Spect.support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid2 : exists id2, round gatherR2 da config id2 = pt2').
{ rewrite <- Spect.from_config_In,  <- Spect.support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid3 : exists id3, round gatherR2 da config id3 = pt3').
{ rewrite <- Spect.from_config_In,  <- Spect.support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
assert (Hid4 : exists id4, round gatherR2 da config id4 = pt4').
{ rewrite <- Spect.from_config_In,  <- Spect.support_In.
  unfold on_SEC in Hperm'. eapply proj1. rewrite <- filter_InA, Hperm'; intuition. }
destruct Hid1 as [id1 Hid1], Hid2 as [id2 Hid2], Hid3 as [id3 Hid3], Hid4 as [id4 Hid4].
destruct Hcase as [Hmaj _].
rewrite round_simplify_clean in Hid1, Hid2, Hid3, Hid4; trivial; [].
(* These robots are different *)
assert (Hneqid12 : id1 <> id2). { intro. subst id1. rewrite Hid1 in Hid2. subst pt1'. R2dec. }
assert (Hneqid13 : id1 <> id3). { intro. subst id1. rewrite Hid1 in Hid3. subst pt1'. R2dec. }
assert (Hneqid14 : id1 <> id4). { intro. subst id1. rewrite Hid1 in Hid4. subst pt1'. R2dec. }
assert (Hneqid23 : id2 <> id3). { intro. subst id2. rewrite Hid2 in Hid3. subst pt2'. R2dec. }
assert (Hneqid24 : id2 <> id4). { intro. subst id2. rewrite Hid2 in Hid4. subst pt2'. R2dec. }
assert (Hneqid34 : id3 <> id4). { intro. subst id3. rewrite Hid3 in Hid4. subst pt3'. R2dec. }
(* At most one of these robots was activated during the round *)
assert (Hex : forall id id' f,
                In id (id1 :: id2 :: id3 :: id4 :: nil) -> In id' (id1 :: id2 :: id3 :: id4 :: nil) ->
                id <> id' -> step da id = Some f -> step da id' = None).
{ intros id id' f Hid Hid' Hneq Hstep. simpl in *.
  destruct (step da id') eqn:Hstep'; trivial; exfalso.
  decompose [or] Hid; decompose [or] Hid'; try subst id; try subst id';
  (now elim Hneq) || rewrite Hstep in *; rewrite Hstep' in *;
  rewrite ?Hid1, ?Hid2, ?Hid3, ?Hid4 in *; R2dec. }
(* Therefore, at least three were not activated and not on the target *)
assert (Hperm_id : exists id1' id2' id3' id4',
      Permutation (id1 :: id2 :: id3 :: id4 :: nil) (id1' :: id2' :: id3' :: id4' :: nil)
      /\ step da id2' = None /\ step da id3' = None /\ step da id4' = None
      /\ NoDup (config id2' :: config id3' :: config id4' :: nil)
      /\ config id2' <> target (!!config) /\ config id3' <> target (!!config) /\ config id4' <> target (!!config)).
{ destruct (step da id1) as [f |] eqn:Hstep1.
  * exists id1, id2, id3, id4. split; trivial.
    repeat split; try (now generalize Hstep1; apply Hex; intuition).
    -- assert (Heq2 : step da id2 = None) by (generalize Hstep1; apply Hex; intuition).
       assert (Heq3 : step da id3 = None) by (generalize Hstep1; apply Hex; intuition).
       assert (Heq4 : step da id4 = None) by (generalize Hstep1; apply Hex; intuition).
       rewrite Heq2, Heq3, Heq4 in *. subst. clear Heq2 Heq3 Heq4.
       assert (Hnodup : NoDup (target (!! config) :: config id2 :: config id3 :: config id4 :: l')).
       { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, Spect.support_NoDupA. }
       inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
    -- intro. apply Hneq12. rewrite (Hex id1 id2 f) in Hid2; trivial; subst; intuition.
    -- intro. apply Hneq13. rewrite (Hex id1 id3 f) in Hid3; trivial; subst; intuition.
    -- intro. apply Hneq14. rewrite (Hex id1 id4 f) in Hid4; trivial; subst; intuition.
  * destruct (step da id2) as [f |] eqn:Hstep2.
    + exists id2, id1, id3, id4. split; [now do 3 econstructor|].
      repeat split; try now generalize Hstep2; apply Hex; intuition.
      -- assert (Heq1 : step da id1 = None) by (generalize Hstep2; apply Hex; intuition).
         assert (Heq3 : step da id3 = None) by (generalize Hstep2; apply Hex; intuition).
         assert (Heq4 : step da id4 = None) by (generalize Hstep2; apply Hex; intuition).
         rewrite Heq1, Heq3, Heq4 in *. subst. clear Heq1 Heq3 Heq4.
         assert (Hnodup : NoDup (config id1 :: target (!! config) :: config id3 :: config id4 :: l')).
         { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, Spect.support_NoDupA. }
         inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
      -- intro. apply Hneq12. now subst.
      -- intro. apply Hneq23. rewrite (Hex id2 id3 f) in Hid3; trivial; subst; intuition.
      -- intro. apply Hneq24. rewrite (Hex id2 id4 f) in Hid4; trivial; subst; intuition.
    + destruct (step da id3) as [f |] eqn:Hstep3.
      - exists id3, id1, id2, id4. split; [now do 3 econstructor|].
        repeat split; try now generalize Hstep3; apply Hex; intuition.
        -- assert (Heq1 : step da id1 = None) by (generalize Hstep3; apply Hex; intuition).
           assert (Heq2 : step da id2 = None) by (generalize Hstep3; apply Hex; intuition).
           assert (Heq4 : step da id4 = None) by (generalize Hstep3; apply Hex; intuition).
           rewrite Heq1, Heq2, Heq4 in *. subst. clear Heq1 Heq2 Heq4.
           assert (Hnodup : NoDup (config id1 :: config id2 :: target (!! config) :: config id4 :: l')).
           { rewrite <- NoDupA_Leibniz. rewrite <- Hperm'. apply on_SEC_NoDupA, Spect.support_NoDupA. }
           inversion_clear Hnodup. inversion_clear H0. inversion_clear H2. repeat constructor; cbn in *; intuition.
        -- intro. apply Hneq13. now subst.
        -- intro. apply Hneq23. now subst.
        -- intro. apply Hneq34. rewrite (Hex id3 id4 f) in Hid4; trivial; subst; intuition.
      - destruct (step da id4) as [f |] eqn:Hstep4.
        ** exists id4, id1, id2, id3. repeat split; trivial; [now do 4 econstructor| ..]; try (now subst); [].
           subst. repeat constructor; cbn in *; intuition.
        ** destruct (R2.eq_dec (config id1) (target (!! config))) as [Heq1 | Heq1].
           ++ exists id1, id2, id3, id4. rewrite <- Heq1. subst. repeat split; trivial; intuition; [].
              repeat constructor; cbn in *; intuition.
           ++ destruct (R2.eq_dec (config id2) (target (!! config))) as [Heq2 | Heq2].
              -- exists id2, id1, id3, id4. rewrite <- Heq2. subst.
                 repeat split; trivial; intuition;
                 solve [repeat constructor; cbn in *; intuition | now do 3 econstructor].
              -- destruct (R2.eq_dec (config id3) (target (!! config))) as [Heq3 | Heq3].
                 *** exists id3, id1, id2, id4. rewrite <- Heq3. subst.
                     repeat split; trivial; intuition;
                     solve [repeat constructor; cbn in *; intuition | now do 3 econstructor].
                 *** exists id4, id1, id2, id3. subst. repeat split; trivial; intuition;
                     solve [repeat constructor; cbn in *; intuition | now do 4 econstructor]. }
(* Finally, the old and new SEC are defined by the unchanging locations of these three robots *)
destruct Hperm_id as [id1' [id2' [id3' [id4' [Hperm_id [Hstep2' [Hstep3' [Hstep4' [Hnodup [? [? ?]]]]]]]]]]].
apply three_points_same_circle with (config id2') (config id3') (config id4').
+ assumption.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : In id2' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id2' || easy; clear Hin; rewrite Hstep2' in *; subst; intuition.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : In id3' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id3' || easy; clear Hin; rewrite Hstep3' in *;subst; intuition.
+ eapply proj2. rewrite <- (filter_InA _).
  assert (Hin : In id4' (id1 :: id2 :: id3 :: id4 :: nil)) by (rewrite Hperm_id; intuition).
  simpl in Hin. unfold on_SEC in Hperm'. rewrite Hperm'.
  decompose [or] Hin; subst id4' || easy; clear Hin; rewrite Hstep4' in *; subst; intuition.
+ assert (Hin : InA R2.eq (config id2') (Spect.support (!! config))).
  { rewrite Spect.support_In. apply Spect.pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
+ assert (Hin : InA R2.eq (config id3') (Spect.support (!! config))).
  { rewrite Spect.support_In. apply Spect.pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
+ assert (Hin : InA R2.eq (config id4') (Spect.support (!! config))).
  { rewrite Spect.support_In. apply Spect.pos_in_config. }
  rewrite is_clean_spec in Hclean. apply Hclean in Hin. inversion_clear Hin; try contradiction; [].
  unfold on_SEC in H2. now rewrite (filter_InA _) in H2.
Qed.

Lemma clean_generic_next_generic_same_target_and_clean : forall da config,
  generic_case config ->
  is_clean (!! config) = true ->
  generic_case (round gatherR2 da config) ->
  is_clean (!! (round gatherR2 da config)) = true
  /\ target (!! (round gatherR2 da config)) = target (!! config).
Proof.
intros da config Hcase Hclean Hcase'.
assert (HSEC := clean_generic_next_generic_same_SEC Hcase Hcase').
assert (Hincl' := incl_clean_next da config Hclean).
rewrite is_clean_spec.
assert (Htarget : target (!! (round gatherR2 da config)) = target (!! config)).
{ do 2 (rewrite generic_target; trivial). now rewrite HSEC. }
split; trivial.
intros pt Hin. unfold SECT. rewrite Htarget. unfold on_SEC. rewrite HSEC.
assert (Hpt := Hincl' _ Hin). unfold on_SEC in Hpt. inversion_clear Hpt.
- now left.
- right. rewrite (filter_InA _). split; trivial. now rewrite  (filter_InA _) in H. 
Qed.

(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Theorem round_lt_config : forall da conf,
  ~forbidden conf -> moving gatherR2 da conf <> nil ->
  lt_config (round gatherR2 da conf) conf.
Proof.
  intros da conf Hforbidden Hmove. unfold lt_config.
  unfold measure at 2.
  destruct (Spect.support (Spect.max (!! conf))) as [| pt [| pt' smax]] eqn:Hmax.
  - (* No robots *)
    rewrite Spect.support_nil, Spect.max_empty in Hmax. elim (spect_non_nil _ Hmax).
  - (* A majority tower *)
    get_case conf.
    apply (MajTower_at_forever da) in Hcase.
    rewrite MajTower_at_equiv in Hcase.
    unfold measure. rewrite Hcase.
    right.
    assert (Hle := multiplicity_le_nG pt (round gatherR2 da conf)).
    cut ((!! conf)[pt] < (!! (round gatherR2 da conf))[pt]); try omega; [].
    apply not_nil_In in Hmove. destruct Hmove as [gmove Hmove].
    assert (Hstep : step da gmove <> None).
    { apply moving_active in Hmove. now rewrite active_spec in Hmove. }
    rewrite moving_spec in Hmove.
    rewrite increase_move_iff. exists gmove. split; trivial.
    get_case conf.
    rewrite (round_simplify_Majority _ Hcase0). destruct (step da gmove); trivial. now elim Hstep.
  - (* Computing the SEC *)
    get_case conf. clear Hmax pt pt' smax.
    destruct (is_clean (!! conf)) eqn:Hclean.
    (* Clean case *)
    + assert (Hle := no_Majority_on_SEC_length Hmaj).
      destruct (on_SEC (Spect.support (!! conf))) as [| pt1 [| pt2 [| pt3 [| pt4 sec]]]] eqn:Hsec;
      cbn in Hle; try omega; [| |].
      * (* Diameter case *)
        assert (Htarget : target (!! conf) = R2.middle pt1 pt2) by now apply diameter_target.
        assert (Hperm := diameter_clean_support Hforbidden Hmaj Hclean Hsec).
        destruct (clean_diameter_next_maj_or_diameter da Hforbidden Hmaj Hclean Hsec)
          as [[pt Hmaj'] | [Hmaj' HpermSEC']].
        -- (* A majority is present after one round *)
           unfold measure.
           rewrite MajTower_at_equiv in Hmaj'.
           rewrite Hmaj'.
           left. omega.
        -- (* Still in a diameter case after one round *)
           assert (Hperm' := diameter_round_same Hmaj' Hperm).
           assert (Hcase : clean_diameter_case conf).
           { repeat split; trivial; setoid_rewrite Hsec; do 2 eexists; reflexivity. }
           assert (Htarget' := diameter_next_target_same Hforbidden Hcase Hmaj').
           rewrite no_Majority_equiv in Hmaj'.
           destruct Hmaj' as [? [? [? Hmaj']]].
           unfold measure. rewrite Hmaj'.
           assert (Hlen' : length (on_SEC (Spect.support (!! (round gatherR2 da conf)))) = 2).
           { now rewrite HpermSEC'. }
           destruct (on_SEC (Spect.support (!! (round gatherR2 da conf)))) as [| ? [| ? [| ? ?]]] eqn:Hsec';
           cbn in Hlen'; omega || clear Hlen'.
           assert (Hclean' : is_clean (!! (round gatherR2 da conf)) = true).
           { rewrite is_clean_spec. unfold SECT. now rewrite Hsec', HpermSEC', Hperm', Htarget', Htarget. }
           rewrite Hclean'.
           right.
           now apply solve_measure_clean.
      * (* Triangle cases *)
        get_case conf.
        assert (HnextSEC := triangle_next_maj_or_diameter_or_triangle da Hforbidden Hcase).
        rewrite Hsec in HnextSEC.
        destruct HnextSEC as [HnextSEC | [[Hmaj' [Htriangle [Hlen [Hclean' Hincl]]]] | [Hmaj' HpermSEC']]].
        -- (* There is a majority tower on the next round *)
           unfold measure.
           destruct (Spect.support (Spect.max (!! (round gatherR2 da conf)))) as [| ? [| ? ?]];
           cbn in HnextSEC; try discriminate.
           destruct (classify_triangle pt1 pt2 pt3); left; omega.
        -- (* Equilateral case with the SEC changing *)
           unfold measure.
           assert (Hmax' := Hmaj'). rewrite no_Majority_equiv in Hmax'.
           destruct Hmax' as [? [? [? Hmax']]]. rewrite Hmax'.
           destruct (on_SEC (Spect.support (!! (round gatherR2 da conf)))) as [| ? [| ? [| ? ?]]];
           cbn in Hlen; omega || clear Hlen.
           rewrite Hclean'.
           left. omega.
        -- (* Still the same triangle after one round *)
           unfold measure.
           assert (Hmax' := Hmaj'). rewrite no_Majority_equiv in Hmax'.
           destruct Hmax' as [? [? [? Hmax']]]. rewrite Hmax'.
           assert (Hlen' : length (on_SEC (Spect.support (!! (round gatherR2 da conf)))) = 3)
             by now rewrite HpermSEC'.
           destruct (on_SEC (Spect.support (!! (round gatherR2 da conf)))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec';
           cbn in Hlen'; omega || clear Hlen'.
           assert (Htarget' : target (!! (round gatherR2 da conf)) = target (!! conf)).
           { apply same_on_SEC_same_target. now rewrite Hsec, Hsec'. }
           assert (Hclean' : is_clean (!! (round gatherR2 da conf)) = true).
           { assert (Hincl' := incl_clean_next da conf Hclean).
             rewrite is_clean_spec. unfold SECT.
             now rewrite Hsec', HpermSEC', <- Hsec, Htarget'. }
           rewrite Hclean'.
           right.
           now apply solve_measure_clean.
      * (* Generic case *)
        unfold measure.
        destruct (Spect.support (Spect.max (!! (round gatherR2 da conf)))) as [| pt [| ? ?]] eqn:Hmax';
        try (now left; omega); [].
        get_case conf.
        get_case (round gatherR2 da conf).
        destruct (on_SEC (Spect.support (!! (round gatherR2 da conf))))
          as [| pt1' [| pt2' [| pt3' [| pt4' ?]]]] eqn:Hsec';
        try (now destruct (is_clean (!! (round gatherR2 da conf))); left; omega); [].
        (* Still in the generic case after one round *)
        get_case (round gatherR2 da conf).
        assert (Hgeneric := clean_generic_next_generic_same_target_and_clean Hcase Hclean Hcase0).
        destruct Hgeneric as [Hclean' Htarget'].
        rewrite Hclean'.
        right.
        now apply solve_measure_clean.
    (* Dirty case *)
    + assert (HsameSEC := dirty_next_on_SEC_same da Hmaj Hclean).
      assert (Hle := no_Majority_on_SEC_length Hmaj).
      unfold measure.
      destruct (Spect.support (Spect.max (!! (round gatherR2 da conf)))) as [| ? [| ? ?]] eqn:Hmax'.
      * (* Absurd: no robot after one round *)
        rewrite Spect.support_nil, Spect.max_empty in Hmax'. elim (spect_non_nil _ Hmax').
      * (* A majority tower after one round *)
        destruct (on_SEC (Spect.support (!! conf))) as [| ? [| ? [| ? [| ? ?]]]];
        cbn in Hle; omega || left; omega.
      * (* Still no majority tower after one round *)
        get_case (round gatherR2 da conf). rename Hmaj0 into Hmaj'.
        assert (Hle' := no_Majority_on_SEC_length Hmaj').
        assert (Hlen := PermutationA_length HsameSEC).
        destruct (on_SEC (Spect.support (!! conf))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec,
                 (on_SEC (Spect.support (!! (round gatherR2 da conf)))) as [| ? [| ? [| ? [| ? ?]]]] eqn:Hsec';
        cbn in Hle, Hle', Hlen; try omega; [| |];
        destruct (is_clean (!! (round gatherR2 da conf))) eqn:Hclean';
        solve [ left; omega | right; now apply solve_measure_dirty ].
Qed.

(** ***  With the termination, the rest of the proof is easy  **)

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (config id) config.
Proof.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. destruct id as [? | b]. apply Hgather. apply Fin.case0. exact b.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, config id <> pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => R2dec_bool (config x) pt) Names.names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite R2dec_bool_true_iff in Hall. hnf. repeat rewrite Hall; trivial; apply Names.In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, R2dec_bool_false_iff in Hid'. now exists id'.
Qed.

(** [FirstMove r d config] gives the number of rounds before one robot moves. *)
Inductive FirstMove r d config : Prop :=
  | MoveNow : moving r (Streams.hd d) config <> nil -> FirstMove r d config
  | MoveLater : moving r (Streams.hd d) config = nil ->
                FirstMove r (Streams.tl d) (round r (Streams.hd d) config) -> FirstMove r d config.

Instance FirstMove_compat : Proper (req ==> deq ==> Config.eq ==> iff) FirstMove.
Proof.
intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst.
* revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc.
  + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc.
  + apply MoveLater.
    - rewrite <- Hr, <- Hd, <- Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
* revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc.
  + apply MoveNow. now rewrite Hr, Hd, Hc.
  + apply MoveLater.
    - rewrite Hr, Hd, Hc. assumption.
    - destruct Hd. apply IHHfirst; trivial. now apply round_compat.
Qed.

(** Correctness proof: given a non-gathered, non forbidden configuration, then some robot will move some day. *)
Theorem OneMustMove : forall config id, ~ forbidden config -> ~gathered_at (config id) config ->
  exists gmove, forall da, In gmove (active da) -> In gmove (moving gatherR2 da config).
Proof.
intros config id Hforbidden Hgather.
destruct (Spect.support (Spect.max (!! config))) as [| pt [| pt' lmax]] eqn:Hmax.
* elim (support_max_non_nil _ Hmax).
* rewrite <- MajTower_at_equiv in Hmax.
  apply not_gathered_generalize with _ _ pt in Hgather.
  apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
  exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
  rewrite (round_simplify_Majority _ Hmax). destruct (step da gmove); auto; now elim Hactive.
* (* No majority tower *)
  get_case config.
  destruct (is_clean (!! config)) eqn:Hclean.
  + (* clean case *)
    apply not_gathered_generalize with _ _ (target (!! config)) in Hgather.
    apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite round_simplify_clean; trivial.
    destruct (step da gmove); try (now elim Hactive); [].
    intuition.
  + (* dirty case *)
    assert (Hclean' := Hclean). unfold is_clean in Hclean'. clear Hmax pt pt' lmax.
    destruct (inclA_bool _ R2.eq_dec (Spect.support (!! config)) (SECT (!! config))) eqn:Hincl;
    try discriminate; [].
    rewrite inclA_bool_false_iff, (not_inclA _ R2.eq_dec) in Hincl.
    destruct Hincl as [pt [Hin Hin']].
    rewrite Spect.support_In, Spect.from_config_In in Hin.
    destruct Hin as [gmove Hmove].
    exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec.
    rewrite round_simplify_dirty; trivial.
    destruct (step da gmove); try (now elim Hactive); [].
    destruct (mem R2.eq_dec (config gmove) (SECT (!! config))) eqn:Htest.
    - rewrite mem_true_iff, Hmove in Htest.
      contradiction.
    - rewrite mem_false_iff, Hmove in Htest.
      assert (Htarget : InA R2.eq (target (!! config)) (SECT (!! config))) by now left.
      intro Habs. rewrite Habs, Hmove in *.
      contradiction.
Qed.

(** Given a k-fair demon, in any non gathered, non forbidden configuration, a robot will be the first to move. *)
Theorem Fair_FirstMove : forall d, Fair d ->
  forall config id, ~forbidden config -> ~gathered_at (config id) config -> FirstMove gatherR2 d config.
Proof.
intros d Hfair config id Hforbidden Hgathered.
destruct (OneMustMove id Hforbidden Hgathered) as [gmove Hmove].
destruct Hfair as [locallyfair Hfair].
revert config Hforbidden Hgathered Hmove Hfair.
specialize (locallyfair gmove).
induction locallyfair; intros config Hforbidden Hgathered Hmove Hfair.
+ apply MoveNow. intro Habs. rewrite <- active_spec in H. apply Hmove in H. rewrite Habs in H. inversion H.
+ destruct (moving gatherR2 (Streams.hd d) config) eqn:Hnil.
  - apply MoveLater. exact Hnil.
    rewrite (no_moving_same_conf _ _ _ Hnil).
    apply (IHlocallyfair); trivial.
    now destruct Hfair.
  - apply MoveNow. rewrite Hnil. discriminate.
Qed.

(** Define one robot to get the location whenever they are gathered. *)
Definition g1 : Fin.t nG.
Proof.
destruct nG eqn:HnG. abstract (pose(Hle := Hyp_nG); omega).
apply (@Fin.F1 n).
Defined.

Lemma gathered_at_forever : forall da conf pt, gathered_at pt conf -> gathered_at pt (round gatherR2 da conf).
Proof.
intros da conf pt Hgather. rewrite (round_simplify_Majority).
+ intro g. destruct (step da (Good g)); reflexivity || apply Hgather.
+ intros pt' Hdiff.
  assert (H0 : (!! conf)[pt'] = 0).
  { rewrite Spect.from_config_spec, Spect.Config.list_spec.
    induction Spect.Names.names as [| id l].
    + reflexivity.
    + cbn. R2dec_full.
      - elim Hdiff. rewrite <- Heq. destruct id as [g | b]. apply Hgather. apply Fin.case0. exact b.
      - apply IHl. }
  rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply Spect.pos_in_config.
Qed.

Lemma gathered_at_OK : forall d conf pt, gathered_at pt conf -> Gather pt (execute gatherR2 d conf).
Proof.
cofix Hind. intros d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.

(** The final theorem. *)
Theorem Gathering_in_R2 :
  forall d, Fair d -> ValidSolGathering gatherR2 d.
Proof.
intros d Hfair conf. revert d Hfair. pattern conf.
apply (well_founded_ind wf_lt_conf). clear conf.
intros conf Hind d Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec conf (conf (Good g1))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (conf (Good g1)). now apply Streams.Now, gathered_at_OK.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  apply (Fair_FirstMove Hfair (Good g1)) in Hmove; trivial.
  induction Hmove as [d conf Hmove | d conf Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    destruct (Hind (round gatherR2 (Streams.hd d) conf)) with (Streams.tl d) as [pt Hpt].
    - apply round_lt_config; assumption.
    - now destruct Hfair.
    - now apply never_forbidden.
    - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_conf in Heq.
    destruct Hrec as [pt Hpt].
    - setoid_rewrite Heq. apply Hind.
    - now destruct Hfair.
    - rewrite Heq. assumption.
    - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
Qed.

Print Assumptions Gathering_in_R2.


(* Let us change the assumption over the demon, it is no longer fair
   but instead activates at least a robot that should move at each round *)
CoInductive OKunfair r (d : demon) config : Prop :=
  AlwaysOKunfair : moving r (Streams.hd d) config <> nil -> 
  OKunfair r (Streams.tl d) (round gatherR2 (Streams.hd d) config) -> OKunfair r d config.

Theorem unfair_Gathering_in_R2 : forall d config,
  OKunfair gatherR2 d config -> ~forbidden config ->
  exists pt, WillGather pt (execute gatherR2 d config).
Proof.
intros d config Hunfair. revert d Hunfair. pattern config.
apply (well_founded_ind wf_lt_conf). clear config.
intros config Hind d Hunfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (config (Good g1))) as [Hmove | Hmove].
+ (* If so, not much to do *)
  exists (config (Good g1)). now apply Streams.Now, gathered_at_OK.
+ (* Otherwise, by assumption on the demon, a robot should move
     so we can use our well-founded induction hypothesis. *)
  destruct Hunfair as [Hstep Hunfair].
  destruct (Hind (round gatherR2 (Streams.hd d) config)) with (Streams.tl d) as [pt Hpt].
  - apply round_lt_config; assumption.
  - assumption.
  - now apply never_forbidden.
  - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
Qed.

End GatheringinR2.
