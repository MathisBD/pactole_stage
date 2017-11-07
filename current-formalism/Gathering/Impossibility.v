(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     P. Courtieu, L. Rieg, X. Urbain                                        
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Gathering.Definitions.
Set Implicit Arguments.


Section ImpossibilityProof.

(** There are n good robots and no byzantine ones. *)
Parameter n : nat.
(** We assume that the number of robots is even and non-null. *)
Axiom even_nG : Nat.Even n.
Axiom nG_non_0 : n <> 0.

Global Instance MyRobotsDef : NamesDef := RobotsDef n 0.
Global Instance MyRobots : Names := Robots n 0.

(** The setting is an arbitrary metric space over R. *)
Context (loc : Type).
Context {loc_Setoid : Setoid loc}.
Context {loc_EqDec : EqDec loc_Setoid}.
Context {loc_RMS : RealMetricSpace loc}.

(* These two axioms are actually equivalent to saying that we are in a eucliean space. *)
Axiom translation_hypothesis : forall z x y, dist (RealMetricSpace.add x z) (RealMetricSpace.add y z) = dist x y.
Axiom homothecy_hypothesis : forall k x y, dist (mul k x) (mul k y) = (Rabs k * dist x y)%R.
(*
(** Given two pairs of distinct points, there exists a similarity sending the first pair over the second one.
    If the lines going through both pairs of points are parallel, we just need an homothecy (to adjust the length
    of the segment) and a translation to move onto the other one.
    It the lines are not parallel, we simply add a rotation whose center is the intersection of the lines. *)
Theorem four_points_similarity : forall pt1 pt2 pt3 pt4, ~Loc.eq pt1 pt2 -> ~Loc.eq pt3 pt4 ->
  {sim : Config.Sim.t | Loc.eq (sim pt1) pt3 /\ Loc.eq (sim pt2) pt4}.
Proof.
intros pt1 pt2 pt3 pt4 Hneq12 Hneq34.
Admitted.
*)

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation "!!" := (@spect_from_config loc _ _ Datatypes.unit _ _ _ _ _ multiset_spectrum) (at level 1).
Notation spectrum := (@spectrum loc _ _ Datatypes.unit _ _ Info _ MyRobots  _).
Notation robogram := (@robogram loc Datatypes.unit _ _ _ _ _ MyRobots Info _).
Notation configuration := (@configuration loc Datatypes.unit _ _ _ _ _ _ _).
Notation config_list := (@config_list loc Datatypes.unit _ _ _ _ _ _ _).
Notation round := (@round loc Datatypes.unit _ _ _ _ _ _ _).
Notation execution := (@execution loc Datatypes.unit _ _ _ _ _).

Ltac Ldec :=
  repeat match goal with
    | |- context[equiv_dec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (equiv_dec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[equiv_dec unit origin] =>
        let Heq := fresh "Heq" in destruct (equiv_dec unit origin) as [Heq | Heq];
        [now elim non_trivial | clear Heq]
    | |- context[equiv_dec origin unit] =>
        let Heq := fresh "Heq" in destruct (equiv_dec origin unit) as [Heq | Heq];
        [now symmetry in Heq; elim non_trivial | clear Heq]
    | H : context[equiv_dec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (equiv_dec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ~equiv ?x ?x |- _ => elim H; reflexivity
  end.

Ltac Ldec_full :=
  match goal with
    | |- context[equiv_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (equiv_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac Labs :=
  match goal with
    | Hx : unit == origin |- _ => now elim non_trivial
    | Hx : origin == unit |- _ => now elim non_trivial; symmetry
    | Hx : ~?x == ?x |- _ => now elim Hx
    | Heq : ?x == ?y, Hneq : ~?y == ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Ltac Ldec_aux H :=
  match type of H with
    | context[equiv_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (equiv_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Lemma nG_ge_2 : 2 <= nG.
Proof.
assert (Heven := even_nG). assert (H0 := nG_non_0).
inversion Heven. simpl.
destruct n as [| [| ?]]; omega.
Qed.

Lemma half_size_config : Nat.div2 nG > 0.
Proof.
assert (Heven := even_nG). assert (H0 := nG_non_0).
simpl. destruct n as [| [| n]].
- omega.
- destruct Heven. omega.
- simpl. omega.
Qed.

Definition translation := translation translation_hypothesis.
Definition homothecy := homothecy translation_hypothesis homothecy_hypothesis.

Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof. intros c1 c2 Hc x. simpl. now rewrite Hc. Qed.

Instance homothecy_compat : forall ρ (Hρ : ρ <> 0%R), Proper (equiv ==> equiv) (fun c => homothecy c Hρ).
Proof. intros ρ Hρ c1 c2 Hc x. simpl. now rewrite Hc. Qed.

(* We need to unfold [spect_is_ok] for rewriting *)
Definition spect_from_config_spec : forall config l,
  (!! config)[l] = countA_occ _ equiv_dec l (List.map fst (config_list config))
 := spect_from_config_spec.

Lemma no_byz : forall (id : ident) P, (forall g, P (@Good G B g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, fst (config1 (Good g)) == fst (config2 (Good g))) -> config1 == config2.
Proof. intros config1 config2 Heq id. apply no_info, (no_byz id). intro g. apply Heq. Qed.


(** [Always_invalid e] means that (infinite) execution [e] is [invalid]
    forever. We will prove that with [bad_demon], robots are always apart. *)
Definition Always_invalid (e : execution) := Stream.forever (Stream.instant invalid) e.

Instance Always_invalid_compat : Proper (equiv ==> iff) Always_invalid.
Proof. apply Stream.forever_compat, Stream.instant_compat. apply invalid_compat. Qed.

(** ** Linking the different properties *)
Set Printing Matching.

Theorem different_no_gathering : forall (e : execution),
  Always_invalid e -> forall pt, ~WillGather pt e.
Proof.
intros e He pt Habs. induction Habs as [e Habs | e].
+ destruct Habs as [Hnow Hlater]. destruct He as [Hinvalid He].
  destruct Hinvalid as [_ [_ [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]]].
  apply Hdiff. transitivity pt.
  - assert (Hin : In pt1 (!! (Stream.hd e))).
    { unfold In. rewrite Hin1. now apply half_size_config. }
    rewrite spect_from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    apply (no_byz id). intro g. now unfold gathered_at in Hnow; specialize (Hnow g).
  - assert (Hin : In pt2 (!! (Stream.hd e))).
    { unfold In. rewrite Hin2. now apply half_size_config. }
    rewrite spect_from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. apply (no_byz id). intro g. apply Hnow.
+ inversion He. now apply IHHabs.
Qed.


(** We split robots into two halves. *)

(** Names of robots only contains good robots. *)
Lemma names_Gnames : names = List.map Good Gnames.
Proof. unfold names. simpl. now rewrite app_nil_r. Qed.

Definition left  := half1 Gnames.
Definition right := half2 Gnames.

Definition left_dec (g : G) := List.in_dec Geq_dec g left.

Lemma not_left_is_right : forall g : G, ~List.In g left -> List.In g right.
Proof.
intros g Hleft.
assert (Hin : List.In g Gnames) by apply In_Gnames.
rewrite <- merge_halves, in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, List.In g left -> List.In g right -> False.
Proof.
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption; [].
apply Gnames_NoDup.
Qed.

Lemma left_spec : forall g, List.In g left <-> proj1_sig g < Nat.div2 nG.
Proof. intro. unfold left, half1. rewrite Gnames_length. apply firstn_enum_spec. Qed.

Lemma right_spec : forall g, List.In g right <-> Nat.div2 nG <= proj1_sig g.
Proof.
intro g. unfold right, half2. rewrite Gnames_length.
rewrite (skipn_enum_spec (Nat.div2 nG) g). intuition. apply proj2_sig.
Qed.

Lemma left_right_partition : names = List.map Good left ++ List.map Good right.
Proof. unfold left, right, Gnames. rewrite <-map_app, merge_halves. apply names_Gnames. Qed.

Ltac LR_dec :=
  match goal with
    | |- context[left_dec ?g] =>
      let Hleft := fresh "Hleft" in let Hright := fresh "Hright" in
      destruct (left_dec g) as [Hleft | Hright];
      try (now exfalso; apply (left_right_exclusive g));
      try apply not_left_is_right in Hright
    | _ => fail
  end.

(** First and last robots are resp. in the first and in the second half. *)
Definition gfirst : G.
Proof. exists 0. abstract (generalize nG_non_0; omega). Defined.

Definition glast : G.
Proof. exists (pred n). abstract (generalize nG_non_0; omega). Defined.

Lemma gfirst_left : List.In gfirst left.
Proof. rewrite left_spec. simpl. apply half_size_config. Qed.

Lemma glast_right : List.In glast right.
Proof.
rewrite right_spec. simpl. assert (Heven := even_nG).
destruct n as [| [| ]]; simpl; auto; [].
apply le_n_S, Nat.div2_decr, le_n_Sn.
Qed.

Corollary gfirst_glast : gfirst <> glast.
Proof.
intro Habs. apply (firstn_skipn_nodup_exclusive Gnames_NoDup (Nat.div2 (length Gnames)) gfirst).
- apply gfirst_left.
- rewrite Habs. apply glast_right.
Qed.

Hint Resolve gfirst_left glast_right left_right_exclusive.

(* As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_config {A} (config : G -> A) : ident -> A := fun id =>
  match id with
    | Good g => config g
    | Byz b => ltac:(exfalso; now apply (Nat.nlt_0_r (proj1_sig b)), proj2_sig)
  end.

(** * Proof of the impossiblity of gathering for two robots
    From now on and until the final theorem we assume a robogram [r]. *)

Section GatheringEven.

Variable r : robogram.
Open Scope R_scope.

(* A demon that makes the robogram fail:
   - if robots go on the position of the other one (symmetrical by definition of robogram),
     activate both and they swap positions;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

(** The reference starting configuration **)
Definition config1 : configuration := fun id =>
  match id with
    | Good g => mk_info (if left_dec g then origin else unit)
    | Byz b => mk_info origin
  end.

(** The symmetrical configuration of the starting configuration **)
Definition config2 : configuration := fun id =>
  match id with
    | Good g => mk_info (if left_dec g then unit else origin)
    | Byz b => mk_info origin
  end.

Definition spectrum0 := add origin (Nat.div2 nG) (singleton unit (Nat.div2 nG)).

Theorem config1_config2_spect_equiv : !! config1 == !! config2.
Proof.
intro pt. unfold config1, config2.
do 2 rewrite spect_from_config_spec, config_list_spec. rewrite names_Gnames. do 4 rewrite map_map.
unfold left_dec, left. generalize (Gnames_NoDup).
pattern Gnames. apply first_last_even_ind.
* reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~List.In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  do 2 rewrite map_app. simpl. repeat rewrite countA_occ_app.
  rewrite half1_cons2. cbn [countA_occ]. change (sig (fun k => lt k n)) with G.
  destruct (in_dec Geq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Geq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : forall a b : loc,
                  List.map (fun x => if in_dec Geq_dec x (gl :: half1 l) then a else b) l
                = List.map (fun x => if in_dec Geq_dec x (half1 l) then a else b) l).
    { intros a b. apply map_ext_in. intros g Hg.
      destruct (in_dec Geq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Geq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Geq_dec g (half1 l)); trivial. elim Hout. intuition. }
    do 2 rewrite Heq.
    Ldec_full; subst; Ldec; try Ldec_full; subst; Ldec; setoid_rewrite plus_comm; simpl; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* rewrite Gnames_length. apply even_nG.
Qed.

Theorem spect_config1 : !! config1 == spectrum0.
Proof.
intro pt. unfold config1, spectrum0.
rewrite spect_from_config_spec, config_list_spec, names_Gnames, map_map, map_map.
cbn [fst mk_info]. unfold left_dec, left. rewrite <- Gnames_length at 1 2. generalize (Gnames_NoDup).
pattern Gnames. apply first_last_even_ind.
* intros _. now rewrite add_0, singleton_0, empty_spec.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~List.In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  rewrite app_length, plus_comm. cbn [List.map List.app countA_occ].
  repeat rewrite map_app, countA_occ_app. rewrite half1_cons2. cbn [List.map countA_occ].
  destruct (in_dec Geq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Geq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : List.map (fun x => if in_dec Geq_dec x (gl :: half1 l) then origin else unit) l
                = List.map (fun x => if in_dec Geq_dec x (half1 l) then origin else unit) l).
    { apply map_ext_in. intros g Hg.
      destruct (in_dec Geq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try (now subst; contradiction); [].
        destruct (in_dec Geq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Geq_dec g (half1 l)); trivial; []. elim Hout. intuition. }
    rewrite Heq, Hrec.
    do 2 Ldec_full; Ldec; try rewrite <- Heq0 in *; try Labs;
    repeat rewrite ?add_same, ?add_other, ?singleton_same, ?singleton_other;
    simpl; unfold complement in *; omega || auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* rewrite Gnames_length. apply even_nG.
Qed.

Corollary config1_invalid : invalid config1.
Proof.
repeat split; try (exact even_nG || exact nG_ge_2); [].
exists origin, unit. rewrite spect_config1. repeat split.
+ intro. now apply non_trivial.
+ unfold spectrum0. rewrite add_same, singleton_spec. now Ldec.
+ unfold spectrum0. rewrite add_other, singleton_spec; try apply non_trivial; []. now Ldec.
Qed.

Corollary config2_invalid : invalid config2.
Proof. split; try exact even_nG. cbn. setoid_rewrite <- config1_config2_spect_equiv. apply config1_invalid. Qed.

(** Two similarities used: the identity and the symmetry wrt a point c. *)

(** The swapping similarity *)
Definition bij_swap (c : loc) : Bijection.bijection loc.
refine {|
  Bijection.section := fun x => RealMetricSpace.add c (opp x);
  Bijection.retraction := fun x => RealMetricSpace.add c (opp x) |}.
Proof.
abstract (intros x y; split; intro Heq; rewrite <- Heq;
          now rewrite opp_distr_add, add_assoc, add_opp, opp_opp, RealMetricSpace.add_comm, add_origin).
Defined.

Lemma bij_swap_ratio : forall c x y : loc, dist (bij_swap c x) (bij_swap c y) = (1 * dist x y)%R.
Proof.
intros c x y. rewrite Rmult_1_l. simpl.
setoid_rewrite RealMetricSpace.add_comm. rewrite translation_hypothesis.
rewrite <- (translation_hypothesis (RealMetricSpace.add x y)).
rewrite add_assoc, (RealMetricSpace.add_comm _ x), add_opp, RealMetricSpace.add_comm, add_origin.
rewrite RealMetricSpace.add_comm, <- add_assoc, add_opp, add_origin.
apply dist_sym.
Qed.

(* We need to define it with a general center although only 1 will be used. *)

Definition swap (c : loc) : similarity loc.
refine {|
  sim_f := bij_swap c;
  zoom := 1;
  center := c |}.
Proof.
- abstract (compute; apply add_opp).
- exact (bij_swap_ratio c).
Defined.

Instance swap_compat : Proper (equiv ==> equiv) swap.
Proof. intros c1 c2 Hc x. simpl. now rewrite Hc. Qed.

Lemma swap_config1 : map_config (swap unit) config1 == config2.
Proof.
apply no_byz_eq. intro g. unfold swap. simpl.
destruct_match.
- now rewrite opp_origin, add_origin.
- apply add_opp.
Qed.

Lemma swap_config2 : map_config (swap unit) config2 == config1.
Proof.
apply no_byz_eq. intro g. unfold swap. simpl.
destruct_match.
- apply add_opp.
- now rewrite opp_origin, add_origin.
Qed.

(** The movement of robots in the reference configuration. *)
Definition move := r (!! config1).

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [config1].

    So, in [config1], if the robot move to [unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move == unit.

Instance da1_compat : Proper (eq ==> opt_eq (equiv ==> equiv))
  (lift_config (fun _ : G => Some (fun c : loc => if c =?= origin then id else swap c))).
Proof.
intros ? id ?; subst. apply (no_byz id).
clear id; intros g c1 c2 Hc. do 2 Ldec_full.
- reflexivity.
- elim Hneq. now rewrite <- Hc.
- elim Hneq. now rewrite Hc.
- now setoid_rewrite Hc.
Qed.

Lemma da1_ratio : forall id sim c,
  lift_config (fun _ => Some (fun c => if c =?= origin then Similarity.id else swap c)) id = Some sim ->
  zoom (sim c) <> 0%R.
Proof.
intros id sim c. apply (no_byz id). intros g Heq.
inversion_clear Heq. Ldec_full; simpl; apply R1_neq_R0.
Qed.

Lemma da1_center : forall id sim c,
  lift_config (fun _ => Some (fun c => if c =?= origin then Similarity.id else swap c)) id = Some sim ->
  center (sim c) == c.
Proof.
intros id sim c. apply (no_byz id). intros g Heq.
inversion_clear Heq. Ldec_full; simpl; try rewrite Heq; reflexivity.
Qed.

Definition da1 : demonic_action := {|
  relocate_byz := fun b => mk_info origin;
  step := lift_config (fun g => Some (fun c => if c =?= origin then Similarity.id else swap c));
  step_zoom := da1_ratio;
  step_center := da1_center |}.

Definition bad_demon1 : demon := Stream.constant da1.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof. coinduction bad_fair1. intros id1 id2. constructor. apply (no_byz id1). discriminate. Qed.

Lemma round_simplify_1_1 : round r da1 config1 == config2.
Proof.
apply no_byz_eq. intro g; unfold round; simpl.
destruct (left_dec g) as [Hleft | Hright].
- Ldec. rewrite config_list_map, map_map; autoclass.
- Ldec. rewrite <- (add_opp unit). apply RealMetricSpace.add_compat, opp_compat; try reflexivity; [].
  rewrite <- Hmove at 2. unfold move. apply pgm_compat.
  rewrite config1_config2_spect_equiv, <- swap_config1. reflexivity.
Qed.

Lemma round_simplify_1_2 : round r da1 config2 == config1.
Proof.
apply no_byz_eq. intro g; unfold round. cbn [step da1 lift_config fst mk_info config2].
destruct (left_dec g) as [Hleft | Hright].
- Ldec. rewrite swap_config2, Hmove. simpl. LR_dec. apply add_opp.
- Ldec. rewrite map_config_id, <- config1_config2_spect_equiv, Hmove. simpl. now LR_dec.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_invalid1_by_eq : forall config : configuration, config == config1 ->
  Always_invalid (execute r bad_demon1 config).
Proof.
cofix differs. intros config Heq. constructor.
+ rewrite Heq. apply config1_invalid.
+ cbn. constructor.
  -
Search Proper @round.

 rewrite Heq. , round_simplify_1_1. apply config2_invalid.
  - cbn. apply differs. now rewrite Heq, round_simplify_1_1, round_simplify_1_2. 
Qed.

Corollary Always_invalid1 : Always_invalid (execute r bad_demon1 config1).
Proof. apply Always_invalid1_by_eq. reflexivity. Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time **)


(* FIXME: We cannot reuse directly the proof on R as the situation is more complicated here:
          in addition to scaling and shift, we also need rotation to move back to config1. *)
(*
Definition conjugated config1 config2 := exists sim : similarity, map sim (!! config1) == !! config2.

Instance conjugated_equiv : Equivalence conjugated.
Proof. split.
- intro config. exists Sim.id. rewrite Spect.from_config_map; autoclass.
  simpl. now rewrite Config.app_id, Config.map_id.
- intros ? ? [sim Hconj]. exists (sim ⁻¹). rewrite <- Hconj.
  rewrite Spect.map_merge; autoclass.
  assert (Heq := Sim.compose_inverse_l sim).
  apply Sim.f_compat, Similarity.section_full_compat in Heq.
  assert (Hext : forall x, Loc.eq ((Sim.compose (sim ⁻¹) sim) x) (Sim.id x))
    by now setoid_rewrite Sim.compose_inverse_l.
  assert (Hid : Proper (Loc.eq ==> Loc.eq) Sim.id) by autoclass.
  rewrite (Spect.map_extensionality_compat _ Hid Hext).
  now rewrite (Spect.from_config_map _ _), Config.app_id, Config.map_id.
- intros ? ? ? [f Hf] [g Hg]. exists (Sim.compose g f).
  rewrite <- Hg, <- Hf. rewrite Spect.map_merge; autoclass. reflexivity.
Qed.

Lemma confi1_conf2_conjugated : conjugated conf1 conf2.
Proof. exists (swap Loc.unit). now rewrite (Spect.from_config_map _ _), swap_conf1. Qed.

Lemma conjugated_invalid_aux : forall config1 config2,
  conjugated config1 config2 -> invalid config1 -> invalid config2.
Proof.
intros config1 config2 [sim Hsim] [? [? [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]]].
repeat split; trivial; []. exists (sim pt1), (sim pt2). repeat split.
- intro Heq. now apply Sim.injective in Heq.
- rewrite <- Hsim, Spect.map_injective_spec; autoclass. apply Sim.injective.
- rewrite <- Hsim, Spect.map_injective_spec; autoclass. apply Sim.injective.
Qed.

Theorem conjugated_invalid : forall config1 config2,
  conjugated config1 config2 -> (invalid config1 <-> invalid config2).
Proof. intros. now split; apply conjugated_invalid_aux. Qed.

Theorem invalid_conjugated : forall config1 config2,
  invalid config1 -> invalid config2 -> conjugated config1 config2.
Proof.
intros config1 config2 Hconfig1 Hconfig2.
assert (Hconfig1' := Hconfig1). assert (Hconfig2' := Hconfig2).
destruct Hconfig1 as [_ [_ [pt1 [pt2 [Hneq12 [Hpt1 Hpt2]]]]]],
         Hconfig2 as [_ [_ [pt3 [pt4 [Hneq34 [Hpt3 Hpt4]]]]]].
destruct (Sim.four_points_similarity Hneq12 Hneq34) as [sim [Heq13 Heq24]].
exists sim.
assert (Hsupp1 : PermutationA Loc.eq (Spect.support (!! config1)) (pt1 :: pt2 :: nil)).
{ symmetry. apply NoDupA_inclA_length_PermutationA; autoclass.
  + repeat constructor.
    - intro Hin. inv Hin; contradiction || now rewrite InA_nil in *.
    - now rewrite InA_nil in *.
  + apply Spect.support_NoDupA.
  + intros x Hin.
    assert (Hx : Loc.eq x pt1 \/ Loc.eq x pt2).
    { inv Hin; auto; inv H0; auto; now rewrite InA_nil in *. }
    rewrite Spect.support_In. hnf. destruct Hx as [Hx | Hx]; rewrite Hx, ?Hpt1, ?Hpt2; apply half_size_conf.
  + rewrite <- Spect.size_spec, invalid_support_length; auto. }
assert (Heq1 : Spect.eq (!! config1) (Spect.M.add pt1 (Nat.div2 N.nG) (Spect.M.singleton pt2 (Nat.div2 N.nG)))).
{ intro pt. destruct (Loc.eq_dec pt pt1) as [Heq | Hneq1];
         [| destruct (Loc.eq_dec pt pt2) as [Heq | Hneq2]]; try rewrite Heq in *.
  + now rewrite Hpt1, Spect.add_same, Spect.singleton_other.
  + now rewrite Hpt2, Spect.add_other, Spect.singleton_same.
  + rewrite Spect.add_other, Spect.singleton_other; trivial; [].
    rewrite <- Spect.not_In. rewrite <- Spect.support_In, Hsupp1. intro Hin.
    inv Hin; auto; inv H0; auto; now rewrite InA_nil in *. }
assert (Hsupp2 : PermutationA Loc.eq (Spect.support (!! config2)) (pt3 :: pt4 :: nil)).
{ symmetry. apply NoDupA_inclA_length_PermutationA; autoclass.
  + repeat constructor.
    - intro Hin. inv Hin; contradiction || now rewrite InA_nil in *.
    - now rewrite InA_nil in *.
  + apply Spect.support_NoDupA.
  + intros x Hin.
    assert (Hx : Loc.eq x pt3 \/ Loc.eq x pt4).
    { inv Hin; auto; inv H0; auto; now rewrite InA_nil in *. }
    rewrite Spect.support_In. hnf. destruct Hx as [Hx | Hx]; rewrite Hx, ?Hpt3, ?Hpt4; apply half_size_conf.
  + rewrite <- Spect.size_spec, invalid_support_length; auto. }
assert (Heq2 : Spect.eq (!! config2) (Spect.M.add pt3 (Nat.div2 N.nG) (Spect.M.singleton pt4 (Nat.div2 N.nG)))).
{ intro pt. destruct (Loc.eq_dec pt pt3) as [Heq | Hneq3];
         [| destruct (Loc.eq_dec pt pt4) as [Heq | Hneq4]]; try rewrite Heq in *.
  + now rewrite Hpt3, Spect.add_same, Spect.singleton_other.
  + now rewrite Hpt4, Spect.add_other, Spect.singleton_same.
  + rewrite Spect.add_other, Spect.singleton_other; trivial; [].
    rewrite <- Spect.not_In. rewrite <- Spect.support_In, Hsupp2. intro Hin.
    inv Hin; auto; inv H0; auto; now rewrite InA_nil in *. }
rewrite Heq1, Heq2. rewrite Spect.map_add, Spect.map_singleton; autoclass; [].
rewrite Heq13, Heq24. reflexivity.
Qed.
*)

Section MoveNot1.

Hypothesis Hmove : move =/= unit.

Lemma minus_unit_move : dist unit move <> 0.
Proof. rewrite dist_defined. intro Habs. now apply Hmove. Qed.

Hint Immediate minus_unit_move.

Lemma ratio_neq_0 : forall ρ, ρ <> 0 -> (dist unit move) / ρ <> 0.
Proof.
intros ρ Hρ Habs. apply Hmove. symmetry. rewrite <- dist_defined.
apply (Rmult_eq_compat_l ρ) in Habs. unfold Rdiv in Habs.
replace (ρ * (dist unit move * / ρ)) with ((dist unit move) * (ρ * / ρ)) in Habs by ring.
rewrite Rinv_r in Habs; auto; []. now ring_simplify in Habs.
Qed.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (dist unit move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (dist Loc.unit move)) in Habs.
unfold Rdiv in Habs.
replace ((dist unit move) * (ρ * / (dist unit move)))
  with (ρ * ((dist Loc.unit move) * / (dist unit move))) in Habs by ring.
rewrite Rinv_r in Habs; auto; []. now ring_simplify in Habs.
Qed.

Instance da2_left_compat : forall ρ (Hρ : ρ <> 0), Proper (eq ==> opt_eq (equiv ==> equiv))
  (lift_conf (fun g : Names.G => if left_dec g then Some (fun c : Loc.t => homothecy c Hρ) else None)).
Proof.
intros ρ Hρ ? [g | b] ?; subst; simpl.
+ LR_dec; try reflexivity; [].
  intros c1 c2 Hc. now apply homothecy_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_ratio_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  zoom (sim c) <> 0.
Proof.
intros ρ Hρ id sim c.apply (no_byz id). clear id.
intro g. simpl. LR_dec.
- intro H. inversion_clear H. simpl. now apply Rabs_no_R0.
- discriminate.
Qed.

Lemma homothecy_center_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  center (sim c) == c.
Proof.
intros ρ Hρ id sim c.apply (no_byz id). clear id. intro g. LR_dec.
- intro H. inversion_clear H. reflexivity.
- discriminate.
Qed.

Definition da2_left (ρ : R) (Hρ : ρ <> 0) : demonic_action := {|
  relocate_byz := fun b => mk_info origin;
  step := lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None);
  step_zoom := homothecy_ratio_1 Hρ;
  step_center := homothecy_center_1 Hρ |}.
(*
Definition da2_left (pt_l pt_r : Loc.t) (Hdiff : ~Loc.eq pt_l pt_r) : demonic_action.
unshelve refine {|
  relocate_byz := fun b => mk_info Loc.origin;
  step := lift_conf (fun g => if left_dec g then Some _ else None) |}.
Proof.
* intro x. destruct (@four_points_similarity pt_l pt_r Loc.origin Loc.unit) as [sim _].
  + assumption.
  + abstract(intro; now apply Loc.non_trivial).
  + exact sim.
* intros x id ?. subst x. destruct id; simpl; try LR_dec.
  + intros pt1 pt2 Hpt. reflexivity.
  + reflexivity.
  + apply Fin.case0, b.
* intros. apply Sim.zoom_non_null.
* intros [g | b] sim c.
  + simpl. LR_dec; try discriminate; []. intro Heq. inv Heq.
    destruct (four_points_similarity Hdiff da2_left_subproof) as [sim [Hpt_l Hpt_r]].
    (* PB: the need to prove a property about the position x of the current point
           whereas we assume it is pt_l (which will be true for the counter-example) *)
  + apply Fin.case0, b.
Defined.

Lemma da2_right_compat : forall ρ (Hρ : ρ <> 0), Proper (eq ==> opt_eq (Loc.eq ==> Common.Sim.eq))
  (lift_conf (fun g => if left_dec g then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ)))).
Proof.
intros ρ Hρ ? [g | b] ?; subst; simpl.
+ LR_dec; try reflexivity; [].
  intros c1 c2 Hc. now apply homothecy_compat.
+ apply Fin.case0. exact b.
Qed. *)

Lemma homothecy_ratio_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  zoom (sim c) <> 0.
Proof.
intros ρ Hρ id sim c.apply (no_byz id). clear id. intro g. simpl. LR_dec.
- discriminate.
- intro H. inversion_clear H. simpl. now apply Rabs_no_R0, Ropp_neq_0_compat.
Qed.

Lemma homothecy_center_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  center (sim c) == c.
Proof.
intros ρ Hρ id sim c.apply (no_byz id). clear id. intro g. simpl. LR_dec.
- discriminate.
- intro H. inversion_clear H. reflexivity.
Qed.

Definition da2_right (ρ : R) (Hρ : ρ <> 0) : demonic_action := {|
  relocate_byz := fun b => mk_info origin;
  step := lift_config (fun g => if left_dec g
                                then None else Some (fun c => homothecy c (Ropp_neq_0_compat _ Hρ)));
  step_zoom := homothecy_ratio_2 Hρ;
  step_center := homothecy_center_2 Hρ |}.

CoFixpoint bad_demon2 ρ (Hρ : ρ <> 0) : demon :=
  Stream.cons (da2_left Hρ)
  (Stream.cons (da2_right (ratio_inv Hρ))
  (bad_demon2 (ratio_inv (ratio_inv Hρ)))). (* ρ updated *)
(*
Lemma bad_demon_head2_1 : forall ρ (Hρ : ρ <> 0), Stream.hd (bad_demon2 Hρ) = da2_left Hρ.
Proof. reflexivity. Qed.

Lemma bad_demon_head2_2 : forall ρ (Hρ : ρ <> 0),
  Stream.hd (Stream.tl (bad_demon2 Hρ)) = da2_right (ratio_inv Hρ).
Proof. reflexivity. Qed.

Lemma bad_demon_tail2 :
  forall ρ (Hρ : ρ <> 0), Stream.tl (Stream.tl (bad_demon2 Hρ)) = bad_demon2 (ratio_inv (ratio_inv Hρ)).
Proof. reflexivity. Qed.
*)

Lemma da_eq_step_None : forall d1 d2, d1 == d2 ->
  forall g, step (Stream.hd d1) (Good g) = None <-> step (Stream.hd d2) (Good g) = None.
Proof.
intros d1 d2 Hd g.
assert (Hopt_eq : opt_eq (equiv ==> equiv)%signature
                    (step (Stream.hd d1) (Good g)) (step (Stream.hd d2) (Good g))).
{ apply step_da_compat; trivial. now rewrite Hd. }
  split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

Theorem kFair_bad_demon2_by_eq : forall ρ (Hρ : ρ <> 0) d, d == bad_demon2 Hρ -> kFair 1 d.
Proof.
cofix fair_demon. intros ρ Hρ d Heq.
constructor; [| constructor].
* setoid_rewrite Heq.
  intros id1 id2. apply (no_byz id2), (no_byz id1). intros g1 g2.
  destruct (left_dec g1).
  + constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
  + destruct (left_dec g2).
    - constructor 2; simpl.
      -- destruct (left_dec g1); eauto. exfalso. eauto.
      -- destruct (left_dec g2); eauto. discriminate.
      -- constructor 1. simpl. LR_dec; eauto. discriminate.
    - constructor 3; simpl.
      -- destruct (left_dec g1); eauto. exfalso. eauto.
      -- destruct (left_dec g2); eauto. exfalso. eauto.
      -- constructor 1. simpl. LR_dec; eauto. discriminate.
* setoid_rewrite Heq.
  intros id1 id2. apply (no_byz id2), (no_byz id1). intros g1 g2.
  destruct (left_dec g1).
  + destruct (left_dec g2).
    - constructor 3; simpl.
      -- LR_dec; eauto. exfalso. eauto.
      -- LR_dec; eauto. exfalso. eauto.
      -- constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
    - constructor 2; simpl.
      -- LR_dec; eauto. exfalso. eauto.
      -- LR_dec; eauto. discriminate.
      -- constructor 1. simpl. LR_dec; eauto. discriminate.
  + constructor 1. simpl. LR_dec; eauto. discriminate.
* eapply fair_demon. rewrite Heq. unfold bad_demon2. simpl Stream.tl. fold bad_demon2. reflexivity.
Qed.

Theorem kFair_bad_demon2 : forall ρ (Hρ : ρ <> 0), kFair 1 (bad_demon2 Hρ).
Proof. intros. eapply kFair_bad_demon2_by_eq. reflexivity. Qed.

Lemma left_right_dist_invalid : forall (config : Config.t),
  (forall g, In g left -> Loc.eq (Config.loc (config (Good g))) (Config.loc (config (Good gfirst)))) ->
  (forall g, In g right -> Loc.eq (Config.loc (config (Good g))) (Config.loc (config (Good glast)))) ->
  Loc.dist (Config.loc (config (Good gfirst))) (Config.loc (config (Good glast))) <> 0 ->
  invalid config.
Proof.
intros config Hleft Hright Hdist.
assert (Hlist_left : eqlistA Loc.eq (map Config.loc (map config (map Good left)))
                                    (alls (Config.loc (config (Good gfirst))) (Nat.div2 N.nG))).
{ erewrite map_map, map_map, <- Names.Gnames_length, <- half1_length, <- map_length, <- (alls_caracA _).
  intros pt Hin. rewrite (InA_map_iff _ _) in Hin.
  - destruct Hin as [g [Hpt Hg]]. rewrite <- Hpt. apply Hleft. now rewrite <- InA_Leibniz.
  - intros ? ? ?. now subst. }
assert (Hlist_right : eqlistA Loc.eq (map Config.loc (map config (map Good right)))
                                     (alls (Config.loc (config (Good glast))) (Nat.div2 N.nG))).
{ do 2 rewrite map_map. rewrite <- Names.Gnames_length at 2.
  erewrite <- half2_even_length, <- map_length, <- (alls_caracA _).
  + intros pt Hin. rewrite (InA_map_iff _ _) in Hin.
    - destruct Hin as [g [Hpt Hg]]. rewrite <- Hpt. apply Hright. now rewrite <- InA_Leibniz.
    - intros ? ? ?. now subst.
  + rewrite Names.Gnames_length. apply even_nG. }
assert (Heq : eqlistA Loc.eq (map Config.loc (map config Names.names))
                      (alls (Config.loc (config (Good gfirst))) (Nat.div2 N.nG)
                       ++ alls (Config.loc (config (Good glast))) (Nat.div2 N.nG))).
{ now rewrite left_right_partition, map_app, map_app, <- Hlist_left, <- Hlist_right. }
assert (~ Loc.eq (Config.loc (config (Good gfirst))) (Config.loc (config (Good glast))))
  by now rewrite <- Loc.dist_defined.
unfold invalid. repeat split; try (now apply even_nG || apply nG_ge_2); [].
exists (Config.loc (config (Good gfirst))), (Config.loc (config (Good glast))).
repeat split.
+ assumption.
+ rewrite Spect.from_config_spec, Config.list_spec.
  rewrite Heq. rewrite countA_occ_app. rewrite (countA_occ_alls_in _), countA_occ_alls_out; try ring.
  intro Habs. now symmetry in Habs.
+ rewrite Spect.from_config_spec, Config.list_spec.
  rewrite Heq. rewrite countA_occ_app. rewrite (countA_occ_alls_in _), countA_occ_alls_out; try ring.
  assumption.
Qed.

Lemma round_da2_left_next_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Config.eq_RobotConf (config (Good g)) (config (Good gfirst))) ->
   forall g, In g left -> Config.eq_RobotConf (round r (da2_left Hρ) config (Good g))
                                              (round r (da2_left Hρ) config (Good gfirst)).
Proof.
intros config ρ Hρ Hleft g Hin.
assert (Hin' := gfirst_left).
apply no_info. unfold round. simpl. do 2 LR_dec. simpl. f_equiv.
- f_equiv. apply pgm_compat. repeat f_equiv. intros pt pt' Heq. do 2 (do 2 f_equiv; trivial). now apply Hleft.
- f_equiv. now apply Hleft.
Qed.

Lemma round_da2_left_next_right : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
   forall g, In g right -> Config.eq_RobotConf (round r (da2_left Hρ) config (Good g))
                                               (round r (da2_left Hρ) config (Good glast)).
Proof.
intros config ρ Hρ Hright g Hin.
assert (Hin' := glast_right).
unfold round. simpl. do 2 LR_dec. now apply Hright.
Qed.

Lemma dist_homothecy_spectrum_centered_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left  -> Config.eq_RobotConf (config (Good g)) (config (Good gfirst))) ->
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
  Loc.eq (Config.loc (config (Good glast))) (Loc.add (Config.loc (config (Good gfirst))) (Loc.mul (/ρ) Loc.unit)) ->
  forall g, In g left ->
    Spect.eq (!! (Config.map (Config.app (homothecy (Config.loc (config (Good g))) Hρ)) config)) (!! conf1).
Proof.
intros config ρ Hρ Hleft Hright Hdist g Hin. f_equiv.
intro id. apply no_info. simpl.
destruct id as [id | b]; try now apply Fin.case0; [].
simpl. rewrite (Hleft _ Hin). LR_dec.
- rewrite (Hleft _ Hleft0). rewrite Loc.add_opp. apply Loc.mul_origin.
- rewrite (Hright _ Hright0). rewrite Hdist. repeat rewrite Loc.mul_distr_add.
  rewrite Loc.mul_morph. replace (ρ * / ρ) with 1 by now field. rewrite Loc.mul_1.
  rewrite Loc.add_comm, Loc.add_assoc. rewrite <- Loc.mul_distr_add.
  setoid_rewrite Loc.add_comm at 2. rewrite Loc.add_opp, Loc.mul_origin.
  now rewrite Loc.add_comm, Loc.add_origin.
Qed.

Lemma round_da2_left_next_dist : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left  -> Config.eq_RobotConf (config (Good g)) (config (Good gfirst))) ->
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
  Loc.dist (Config.loc (config (Good gfirst))) (Config.loc (config (Good glast))) = Loc.dist Loc.unit move / ρ ->
  Loc.dist (Config.loc (round r (da2_left Hρ) config (Good gfirst)))
           (Config.loc (round r (da2_left Hρ) config (Good glast))) = Loc.dist Loc.unit move / ρ.
Proof.
intros config ρ Hρ Hleft Hright Hdist.
assert (Hin' := gfirst_left). assert (Hin'' := glast_right).
unfold round. simpl. do 2 LR_dec. cbn -[homothecy].
rewrite dist_homothecy_spectrum_centered_left; auto.
simpl. rewrite Hdist. setoid_rewrite Loc.add_comm at 1 2. rewrite Loc.add_assoc.
f_equiv.
(* This lemma is wrong. See FIXME *)
Admitted.

Lemma round_da2_right_next_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Config.eq_RobotConf (config (Good g)) (config (Good gfirst))) ->
  forall g, In g left ->  Config.eq_RobotConf (round r (da2_right Hρ) config (Good g))
                                              (round r (da2_right Hρ) config (Good gfirst)).
Proof.
intros config ρ Hρ Hleft g Hin.
assert (Hin' := gfirst_left).
unfold round. simpl. do 2 LR_dec. now apply Hleft.
Qed.

Lemma round_da2_right_next_right : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
   forall g, In g right -> Config.eq_RobotConf (round r (da2_right Hρ) config (Good g))
                                               (round r (da2_right Hρ) config (Good glast)).
Proof.
intros config ρ Hρ Hright g Hin.
assert (Hin' := glast_right).
unfold round. simpl. do 2 LR_dec. apply no_info. cbn -[homothecy]. f_equiv.
- apply homothecy_compat. now apply Hright.
- apply pgm_compat. do 4 f_equiv. apply homothecy_compat. now apply Hright.
Qed.

Lemma round_da2_right_next_dist : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left  -> Config.eq_RobotConf (config (Good g)) (config (Good gfirst))) ->
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
  Loc.dist (Config.loc (config (Good gfirst))) (Config.loc (config (Good glast))) = /ρ ->
  Loc.dist (Config.loc (round r (da2_right Hρ) config (Good gfirst)))
           (Config.loc (round r (da2_right Hρ) config (Good glast))) = Loc.dist Loc.unit move / ρ.
Proof.
intros config ρ Hρ Hleft Hright Hdist.
assert (Hin' := gfirst_left).
assert (Hin'' := glast_right).
unfold round. simpl. do 2 LR_dec.
(* This lemma is wrong. See FIXME *)
Admitted.


Theorem Always_invalid2 : forall ρ (Hρ : ρ <> 0) config,
  invalid config ->
  (forall g, In g left ->  Config.eq_RobotConf (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Config.eq_RobotConf (config (Good g)) (config (Good glast))) ->
  Loc.dist (Config.loc (config (Good gfirst))) (Config.loc (config (Good glast))) = /ρ ->
  Always_invalid (execute r (bad_demon2 Hρ) config).
Proof.
cofix differs. intros ρ Hρ config Hinvalid Hleft Hright Hdist.
constructor; [| constructor].
  (* Inital state *)
- cbn. assumption.
  (* State after one step *)
- cbn. apply left_right_dist_invalid.
  + intros g Hg. now apply round_da2_left_next_left.
  + intros g Hg. now apply round_da2_left_next_right.
  + cbn. rewrite round_da2_left_next_dist; trivial; []. now apply ratio_neq_0.
(* State after two steps *)
- do 2 rewrite execute_tail.
  rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  apply differs.
  + cbn. apply left_right_dist_invalid.
    * intros. apply round_da2_right_next_left; trivial.
      intros. now apply round_da2_left_next_left.
    * intros. apply round_da2_right_next_right; trivial.
      intros. now apply round_da2_left_next_right.
    * assert (Hmove' := Hmove). rewrite <- Loc.dist_defined, Loc.dist_sym in Hmove'.
      rewrite round_da2_right_next_dist.
      -- intro H. apply Rmult_integral in H. destruct H; auto; [].
         revert H. now apply Rinv_neq_0_compat, ratio_inv.
      -- intros. now apply round_da2_left_next_left.
      -- intros. now apply round_da2_left_next_right.
      -- rewrite round_da2_left_next_dist; trivial; []. now field.
  + intros. apply round_da2_right_next_left; trivial.
    intros. now apply round_da2_left_next_left.
  + intros. apply round_da2_right_next_right; trivial.
    intros. now apply round_da2_left_next_right.
  + assert (Hmove' := Hmove). rewrite <- Loc.dist_defined, Loc.dist_sym in Hmove'.
    rewrite round_da2_right_next_dist.
    * now field.
    * intros. now apply round_da2_left_next_left.
    * intros. now apply round_da2_left_next_right.
    * rewrite round_da2_left_next_dist; trivial; []. now field.
Qed.

End MoveNot1.

(** **  Merging both cases  **)

Definition bad_demon : @demon loc Datatypes.unit _ _ _ _.
Proof.
destruct (move =?= unit) as [Hmove | Hmove].
- (** Robots exchange positions **)
  exact bad_demon1.
- (** Robots do not exchange positions **)
  assert (Hneq : / dist unit origin <> 0).
  { apply Rinv_neq_0_compat. rewrite dist_defined. apply non_trivial. }
  exact (bad_demon2 Hmove Hneq).
Defined.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof.
intros. unfold bad_demon.
destruct (move =?= unit).
- apply kFair_mon with 0%nat. exact kFair_bad_demon1. omega.
- now apply kFair_bad_demon2.
Qed.

Theorem kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon; auto.
- auto.
Qed.

(** * Final theorem

Given a non empty finite even set [G] and a robogram [r] on ([G]) × ∅,
there is no (k>0)-fair demon for which the gathering problem is solved for any starting configuration. *)

Theorem noGathering :
  forall k, (1<=k)%nat -> ~(forall d, kFair k d -> FullSolGathering r d).
Proof.
intros k h Habs.
specialize (Habs bad_demon (kFair_bad_demon' h) config1).
destruct Habs as [pt Habs]. revert Habs. apply different_no_gathering.
unfold bad_demon.
destruct (move =?= unit) as [Hmove | Hmove].
+ now apply Always_invalid1.
+ apply (Always_invalid2 Hmove).
  - apply conf1_invalid.
  - assert (Hleft := gfirst_left). intros. cbn. now do 2 LR_dec.
  - assert (Hright := glast_right). intros. cbn. now do 2 LR_dec.
  - assert (Hleft := gfirst_left). assert (Hright := glast_right). intros. cbn. do 2 LR_dec.
    rewrite Rinv_involutive; apply Loc.dist_sym || (rewrite Loc.dist_defined; apply Loc.non_trivial).
Qed.

End ImpossibilityProof.

Print Assumptions noGathering.
(* FIXME: Why is there a dependency on Eqdep.Eq_rect_eq.eq_rect_eq? *)
