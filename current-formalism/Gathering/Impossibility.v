(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Gathering.Definitions.


Set Implicit Arguments.


(** The setting is an arbitrary metric space over R. *)
Declare Module Loc : RealMetricSpace.

(* These two axioms are actually equivalent to saying that we are in a eucliean space. *)
Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.
Axiom homothecy_hypothesis : forall k x y, Loc.dist (Loc.mul k x) (Loc.mul k y) = (Rabs k * Loc.dist x y)%R.

Ltac Ldec :=
  repeat match goal with
    | |- context[Loc.eq_dec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Loc.eq_dec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Loc.eq_dec Loc.unit Loc.origin] =>
        let Heq := fresh "Heq" in destruct (Loc.eq_dec Loc.unit Loc.origin) as [Heq | Heq];
        [now elim Loc.non_trivial | clear Heq]
    | |- context[Loc.eq_dec Loc.origin Loc.unit] =>
        let Heq := fresh "Heq" in destruct (Loc.eq_dec Loc.origin Loc.unit) as [Heq | Heq];
        [now symmetry in Heq; elim Loc.non_trivial | clear Heq]
    | H : context[Loc.eq_dec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Loc.eq_dec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | H : ~Loc.eq ?x ?x |- _ => elim H; reflexivity
  end.

Ltac Ldec_full :=
  match goal with
    | |- context[Loc.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Loc.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Ltac Labs :=
  match goal with
    | Hx : Loc.eq Loc.unit Loc.origin |- _ => now elim Loc.non_trivial
    | Hx : Loc.eq Loc.origin Loc.unit |- _ => now elim Loc.non_trivial; symmetry
    | Hx : ~Loc.eq ?x ?x |- _ => now elim Hx
    | Heq : Loc.eq ?x ?y, Hneq : ~Loc.eq ?y ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Ltac Ldec_aux H :=
  match type of H with
    | context[Loc.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Loc.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

(** There are nG good robots and no byzantine ones. *)
Parameter nG : nat.

Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.

(** We assume that the number of robots is even and non-null. *)
Axiom even_nG : Nat.Even N.nG.
Axiom nG_non_0 : N.nG <> 0.

Lemma nG_ge_2 : 2 <= N.nG.
Proof.
assert (Heven := even_nG). assert (H0 := nG_non_0).
inversion Heven.
destruct N.nG as [| [| ?]]; omega.
Qed.

Lemma half_size_conf : Nat.div2 N.nG > 0.
Proof.
assert (Heven := even_nG). assert (H0 := nG_non_0).
destruct N.nG as [| [| n]].
- omega.
- destruct Heven. omega.
- simpl. omega.
Qed.

(** We instantiate in our setting the generic definitions of the gathering problem. *)
Module Defs := Definitions.GatheringDefs(Loc)(N).
Export Defs.

Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

Definition translation := Sim.translation translation_hypothesis.
Definition homothecy := Sim.homothecy translation_hypothesis homothecy_hypothesis.

Instance translation_compat : Proper (Loc.eq ==> Sim.eq) translation.
Proof. intros c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.

Instance homothecy_compat : forall ρ (Hρ : ρ <> 0%R), Proper (Loc.eq ==> Sim.eq) (fun c => homothecy c Hρ).
Proof. intros ρ Hρ c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.

(** We split robots into two halves. *)

(** Names of robots only contains good robots. *)
Lemma names_Gnames : Spect.Names.names = map (@Good Spect.Names.G Spect.Names.B) Spect.Names.Gnames.
Proof.
unfold Spect.Names.names, Spect.Names.Internals.names, Spect.Names.Gnames.
cut (Spect.Names.Internals.Bnames = nil).
- intro Hnil. rewrite Hnil. simpl. now rewrite app_nil_r.
- rewrite <- length_zero_iff_nil. apply Spect.Names.Internals.fin_map_length.
Qed.

Definition left  := half1 Names.Gnames.
Definition right := half2 Names.Gnames.

Definition left_dec (e : Names.G) := List.in_dec Fin.eq_dec e left.

Lemma not_left_is_right : forall g : Names.G, ~In g left -> In g right.
Proof.
intros g Hleft.
assert (Hin : In g Names.Gnames) by apply Names.In_Gnames.
rewrite <- merge_halves, in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof.
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption.
apply Names.Gnames_NoDup.
Qed.

Lemma left_right_partition : Names.names = map Good left ++ map Good right.
Proof. unfold left, right, Names.Gnames. rewrite <-map_app, merge_halves. apply names_Gnames. Qed.

Ltac LR_dec :=
  match goal with
    | |- context[left_dec ?g] =>
      let Hleft := fresh "Hleft" in let Hright := fresh "Hright" in
      destruct (left_dec g) as [Hleft | Hright];
      try (now exfalso; apply (left_right_exclusive g));
      try apply not_left_is_right in Hright
    | _ => fail
  end.

Definition gfirst : Names.G :=
  match N.nG as n0 return (N.nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : N.nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity N.nG).

Definition glast :=
  match N.nG as n return (N.nG = n -> Fin.t n) with
    | 0 => fun Habs : N.nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity N.nG).

Lemma gfirst_left : In gfirst left.
Proof.
destruct N.nG as [| [| nG]] eqn:HnG.
+ now elim nG_non_0.
+ elim even_nG. intros. omega.
+ unfold left, gfirst.
Admitted.

Lemma glast_right : In glast right.
Proof.
Admitted.

Corollary gfirst_glast : gfirst <> glast.
Proof.
intro Habs. apply (firstn_skipn_nodup_exclusive Names.Gnames_NoDup (Nat.div2 (length Names.Gnames)) gfirst).
- apply gfirst_left.
- rewrite Habs. apply glast_right.
Qed.

Hint Immediate gfirst_left glast_right left_right_exclusive.

(* As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_conf {A} (conf : Names.G -> A) : Names.ident -> A := fun id =>
  match id with
    | Good g => conf g
    | Byz b => Fin.case0 _ b
  end.

(** * Proof of the impossiblity of gathering for two robots
    From now on and until the final theorem we give us a robogram [r]. *)

(** [Always_forbidden e] means that (infinite) execution [e] is [forbidden]
    forever. We will prove that with [bad_demon], robots are always apart. *)
CoInductive Always_forbidden (e : execution) : Prop :=
  CAF : forbidden (execution_head e) ->
        Always_forbidden (execution_tail e) -> Always_forbidden e.

Lemma Always_forbidden_compat_lemma : forall e1 e2, eeq e1 e2 -> Always_forbidden e1 -> Always_forbidden e2.
Proof.
coinduction diff.
- rewrite <- H. now destruct H0.
- destruct H. apply (diff _ _ H1). now destruct H0.
Qed.

Instance Always_forbidden_compat : Proper (eeq ==> iff) Always_forbidden.
Proof.
intros e1 e2 He; split; intro.
- now apply (Always_forbidden_compat_lemma He).
- now apply (Always_forbidden_compat_lemma (symmetry He)).
Qed.

Theorem different_no_gathering : forall (e : execution),
  Always_forbidden e -> forall pt, ~WillGather pt e.
Proof.
intros e He pt Habs. induction Habs.
+ destruct H as [Hnow Hlater]. destruct He as [Hforbidden He].
  destruct Hforbidden as [_ [_ [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]]].
  apply Hdiff. transitivity pt.
  - assert (Hin : Spect.In pt1 (!! (execution_head e))).
    { unfold Spect.In. rewrite Hin1. now apply half_size_conf. }
    rewrite Spect.from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    destruct id as [g | b]. apply Hnow. apply Fin.case0. exact b.
  - assert (Hin : Spect.In pt2 (!! (execution_head e))).
    { unfold Spect.In. rewrite Hin2. now apply half_size_conf. }
    rewrite Spect.from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. destruct id as [g | b]. apply Hnow. apply Fin.case0. exact b.
+ inversion He. now apply IHHabs.
Qed.

Section GatheringEven.
Open Scope R_scope.

Variable r : robogram.

(* A demon that makes the robogram fail:
   - if robots go on the position of the other one (symmetrical by definition of robogram),
     activate both and they swap positions;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

(** The reference starting configuration **)
Definition conf1 : Config.t := fun id =>
  match id with
    | Good g => if left_dec g then Loc.origin else Loc.unit
    | Byz b => Loc.origin
  end.

(** The symmetrical configuration of the starting configuration **)
Definition conf2 : Config.t := fun id =>
  match id with
    | Good g => if left_dec g then Loc.unit else Loc.origin
    | Byz b => Loc.origin
  end.

Definition spectrum := Spect.add Loc.origin (Nat.div2 N.nG) (Spect.singleton Loc.unit (Nat.div2 N.nG)).

Theorem conf1_conf2_spect_eq : Spect.eq (!! conf1) (!! conf2).
Proof.
intro pt. unfold conf1, conf2.
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec. rewrite names_Gnames. do 2 rewrite map_map.
unfold left_dec, left. generalize (Names.Gnames_NoDup).
apply (@first_last_even_ind _
(fun l => NoDup l ->
     countA_occ _ Loc.eq_dec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then Loc.origin else Loc.unit) l) =
     countA_occ _ Loc.eq_dec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then Loc.unit else Loc.origin) l))).
* reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  do 2 rewrite map_app. simpl. repeat rewrite countA_occ_app. simpl. rewrite half1_cons2.
  destruct (in_dec Fin.eq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Fin.eq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : forall a b : Loc.t,
                  map (fun g => if in_dec Fin.eq_dec g (gl :: half1 l) then a else b) l
                = map (fun g => if in_dec Fin.eq_dec g (half1 l) then a else b) l).
    { intros a b. apply map_ext_in. intros g Hg.
      destruct (in_dec Fin.eq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Fin.eq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Fin.eq_dec g (half1 l)); trivial. elim Hout. intuition. }
    do 2 rewrite Heq.
    Ldec_full; subst; Ldec; try Ldec_full; subst; Ldec; setoid_rewrite plus_comm; simpl; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* change (Fin.t N.nG) with Spect.Names.Internals.G. rewrite Spect.Names.Gnames_length. apply even_nG.
Qed.

Theorem spect_conf1 : Spect.eq (!! conf1) spectrum.
Proof.
intro pt. unfold conf1, spectrum.
rewrite Spect.from_config_spec, Spect.Config.list_spec. rewrite names_Gnames, map_map.
unfold left_dec, left. rewrite <- Names.Gnames_length at 1 2. generalize (Names.Gnames_NoDup).
apply (@first_last_even_ind _
(fun l => NoDup l ->
      countA_occ _ Loc.eq_dec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then Loc.origin else Loc.unit) l)
    = (Spect.add Loc.origin (Nat.div2 (length l)) (Spect.singleton Loc.unit (Nat.div2 (length l))))[pt])).
* intros _. simpl. rewrite Spect.add_0, Spect.singleton_0, Spect.empty_spec. reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  rewrite app_length, plus_comm.
  simpl. repeat rewrite map_app, countA_occ_app. simpl. rewrite half1_cons2.
  destruct (in_dec Fin.eq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Fin.eq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : map (fun x => if in_dec Fin.eq_dec x (gl :: half1 l) then Loc.origin else Loc.unit) l
                = map (fun x => if in_dec Fin.eq_dec x (half1 l) then Loc.origin else Loc.unit) l).
    { apply map_ext_in. intros g Hg.
      destruct (in_dec Fin.eq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Fin.eq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Fin.eq_dec g (half1 l)); trivial. elim Hout. intuition. }
    rewrite Heq, Hrec.
    Ldec_full; Ldec; Ldec_full; try rewrite <- Heq0 in *; try Labs;
    repeat rewrite ?Spect.add_same, ?Spect.add_other, ?Spect.singleton_same, ?Spect.singleton_other;
    trivial; omega || intro; Labs.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* change (Fin.t N.nG) with Spect.Names.Internals.G. rewrite Spect.Names.Gnames_length. apply even_nG.
Qed.

Corollary conf1_forbidden : forbidden conf1.
Proof.
repeat split; try (exact even_nG || exact nG_ge_2); [].
exists Loc.origin, Loc.unit. rewrite spect_conf1. repeat split.
+ intro. now apply Loc.non_trivial.
+ unfold spectrum. rewrite Spect.add_same, Spect.singleton_spec. now Ldec.
+ unfold spectrum. rewrite Spect.add_other, Spect.singleton_spec; try apply Loc.non_trivial; []. now Ldec.
Qed.

Corollary conf2_forbidden : forbidden conf2.
Proof. split; try exact even_nG. cbn. setoid_rewrite <- conf1_conf2_spect_eq. apply conf1_forbidden. Qed.

(** Two similarities used: the identity and the symmetry wrt a point c. *)

(** The swapping similarity *)
Definition bij_swap (c : Loc.t) : Similarity.bijection Loc.eq.
refine {|
  Similarity.section := fun x => Loc.add c (Loc.opp x);
  Similarity.retraction := fun x => Loc.add c (Loc.opp x) |}.
Proof.
abstract (intros x y; split; intro Heq; rewrite <- Heq;
          now rewrite Loc.opp_distr_add, Loc.add_assoc, Loc.add_opp, Loc.opp_opp, Loc.add_comm, Loc.add_origin).
Defined.

Lemma bij_swap_ratio : forall c x y : Loc.t, Loc.dist (bij_swap c x) (bij_swap c y) = (1 * Loc.dist x y)%R.
Proof.
intros c x y. rewrite Rmult_1_l. compute.
setoid_rewrite Loc.add_comm. rewrite translation_hypothesis.
rewrite <- (translation_hypothesis (Loc.add x y)).
rewrite Loc.add_assoc, (Loc.add_comm _ x), Loc.add_opp, Loc.add_comm, Loc.add_origin.
rewrite Loc.add_comm, <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
apply Loc.dist_sym.
Qed.

(* We need to define it with a general center although only 1 will be used. *)
Definition swap (c : Loc.t) : Sim.t.
refine {|
  Sim.sim_f := bij_swap c;
  Sim.zoom := 1;
  Sim.center := c |}.
Proof.
- abstract (compute; apply Loc.add_opp).
- exact (bij_swap_ratio c).
Defined.

Instance swap_compat : Proper (Loc.eq ==> Sim.eq) swap.
Proof. intros c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.

Lemma swap_conf1 : Config.eq (Config.map (swap Loc.unit) conf1) conf2.
Proof.
intros [g | b].
+ unfold Config.map. simpl. LR_dec.
  - now rewrite Loc.opp_origin, Loc.add_origin.
  - apply Loc.add_opp.
+ apply Fin.case0. exact b.
Qed.

Lemma swap_conf2 : Config.eq (Config.map (swap Loc.unit) conf2) conf1.
Proof.
intros [g | b].
+ unfold Config.map. simpl. LR_dec.
  - apply Loc.add_opp.
  - now rewrite Loc.opp_origin, Loc.add_origin.
+ apply Fin.case0. exact b.
Qed.

(** The movement of robots in the reference configuration. **)
Definition move := r (!! conf1).

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : Loc.eq move Loc.unit.

Lemma da1_compat : Proper (eq ==> opt_eq (Loc.eq ==> Common.Sim.eq))
  (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => if Loc.eq_dec c Loc.origin then Sim.id else swap c))).
Proof.
intros ? [g | b] ?; subst; simpl.
+ intros c1 c2 Hc. do 2 Ldec_full.
  - reflexivity.
  - elim Hneq. now rewrite <- Hc.
  - elim Hneq. now rewrite Hc.
  - now rewrite Hc.
+ apply Fin.case0. exact b.
Qed.

Lemma da1_ratio : forall id sim c,
  lift_conf (fun _ => Some (fun c => if Loc.eq_dec c Loc.origin then Sim.id else swap c)) id = Some sim ->
  Sim.zoom (sim c) <> 0%R.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Ldec_full; simpl; apply R1_neq_R0.
- apply Fin.case0. exact b.
Qed.

Lemma da1_center : forall id sim c,
  lift_conf (fun _ => Some (fun c => if Loc.eq_dec c Loc.origin then Sim.id else swap c)) id = Some sim ->
  Loc.eq (Sim.center (sim c)) c.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Ldec_full; simpl; try rewrite Heq; reflexivity.
- apply Fin.case0. exact b.
Qed.

Definition da1 : demonic_action.
refine {|
  relocate_byz := fun b => Loc.origin;
  step := lift_conf (fun g => Some (fun c => if Loc.eq_dec c Loc.origin then Sim.id else swap c)) |}.
Proof.
- exact da1_compat.
- exact da1_ratio.
- exact da1_center.
Defined.

CoFixpoint bad_demon1 : demon := NextDemon da1 bad_demon1.

Lemma bad_demon1_tail : demon_tail bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.

Lemma bad_demon1_head : demon_head bad_demon1 = da1.
Proof. reflexivity. Qed.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof.
coinduction bad_fair1.
intros id1 id2. constructor. destruct id1; simpl. discriminate. apply Fin.case0. exact b.
Qed.

Lemma round_simplify_1_1 : Config.eq (round r da1 conf1) conf2.
Proof.
intros [g | b]; unfold round; simpl.
+ LR_dec.
  - Ldec. simpl. rewrite Config.map_id. fold move. apply Hmove.
  - Ldec. setoid_rewrite swap_conf1. simpl. rewrite <- (Loc.add_opp Loc.unit).
    setoid_rewrite Loc.add_comm. do 2 f_equiv. rewrite <- conf1_conf2_spect_eq. apply Hmove.
+ apply Fin.case0. exact b.
Qed.

Lemma round_simplify_1_2 : Config.eq (round r da1 conf2) conf1.
Proof.
intros [g | b]; unfold round; simpl.
+ LR_dec.
  - Ldec. rewrite swap_conf2. simpl. rewrite <- (Loc.add_opp Loc.unit).
    setoid_rewrite Loc.add_comm. do 2 f_equiv. apply Hmove.
  - Ldec. simpl. rewrite Config.map_id.
    rewrite <- conf1_conf2_spect_eq. fold move. apply Hmove.
+ apply Fin.case0. exact b.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_forbidden1_by_eq : forall conf : Config.t, Config.eq conf conf1 ->
  Always_forbidden (execute r bad_demon1 conf).
Proof.
cofix differs. intros conf Heq. constructor.
+ simpl. rewrite Heq. apply conf1_forbidden.
+ cbn. constructor.
  - simpl. rewrite Heq, round_simplify_1_1. apply conf2_forbidden.
  - cbn. apply differs. now rewrite Heq, round_simplify_1_1, round_simplify_1_2. 
Qed.

Corollary Always_forbidden1 : Always_forbidden (execute r bad_demon1 conf1).
Proof. apply Always_forbidden1_by_eq. reflexivity. Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time **)

(* FIXME: We cannot reuse directly the proof on R as the situation is more complicated here:
          in addition to scaling and shift, we also need rotation to move back to conf1. *)

Definition conjugated config1 config2 := exists sim : Sim.t, Spect.eq (Spect.map sim (!! config1)) (!! config2).

Instance conjugated_equiv : Equivalence conjugated.
Proof. split.
- intro config. exists Sim.id. rewrite Spect.from_config_map; autoclass.
  simpl. now rewrite Config.map_id.
- intros ? ? [sim Hconj]. exists (sim ⁻¹). rewrite <- Hconj.
  rewrite Spect.map_merge; autoclass.
  assert (Heq := Sim.compose_inverse_l sim).
  apply Sim.f_compat, Similarity.section_full_compat in Heq.
  assert (Hext : forall x, Loc.eq ((Sim.compose (sim ⁻¹) sim) x) (Sim.id x))
    by now setoid_rewrite Sim.compose_inverse_l.
  assert (Hid : Proper (Loc.eq ==> Loc.eq) Sim.id) by autoclass.
  rewrite (Spect.map_extensionality_compat _ Hid Hext).
  now rewrite (Spect.from_config_map _ _), Config.map_id.
- intros ? ? ? [f Hf] [g Hg]. exists (Sim.compose g f).
  rewrite <- Hg, <- Hf. rewrite Spect.map_merge; autoclass. reflexivity.
Qed.

Lemma confi1_conf2_conjugated : conjugated conf1 conf2.
Proof. exists (swap Loc.unit). now rewrite (Spect.from_config_map _ _), swap_conf1. Qed.

Lemma conjugated_forbidden_aux : forall config1 config2,
  conjugated config1 config2 -> forbidden config1 -> forbidden config2.
Proof.
intros config1 config2 [sim Hsim] [? [? [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]]].
repeat split; trivial; []. exists (sim pt1), (sim pt2). repeat split.
- intro Heq. now apply Sim.injective in Heq.
- rewrite <- Hsim, Spect.map_injective_spec; autoclass. apply Sim.injective.
- rewrite <- Hsim, Spect.map_injective_spec; autoclass. apply Sim.injective.
Qed.

Theorem Conjugated_forbidden : forall config1 config2,
  conjugated config1 config2 -> (forbidden config1 <-> forbidden config2).
Proof. intros. now split; apply conjugated_forbidden_aux. Qed.


Section MoveNot1.

Hypothesis Hmove : ~Loc.eq move Loc.unit.

Lemma minus_unit_move : Loc.dist Loc.unit move <> 0.
Proof. rewrite Loc.dist_defined. intro Habs. now apply Hmove. Qed.

Hint Immediate minus_unit_move.

Lemma ratio_neq_0 : forall ρ, ρ <> 0 -> (Loc.dist Loc.unit move) / ρ <> 0.
Proof.
intros ρ Hρ Habs. apply Hmove. symmetry. rewrite <- Loc.dist_defined.
apply (Rmult_eq_compat_l ρ) in Habs. unfold Rdiv in Habs.
replace (ρ * (Loc.dist Loc.unit move * / ρ)) with ((Loc.dist Loc.unit move) * (ρ * / ρ)) in Habs by ring.
rewrite Rinv_r in Habs; auto; []. now ring_simplify in Habs.
Qed.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (Loc.dist Loc.unit move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (Loc.dist Loc.unit move)) in Habs.
unfold Rdiv in Habs.
replace ( (Loc.dist Loc.unit move) * (ρ * / (Loc.dist Loc.unit move)))
  with (ρ * ((Loc.dist Loc.unit move) * / (Loc.dist Loc.unit move))) in Habs by ring.
rewrite Rinv_r in Habs; auto; []. now ring_simplify in Habs.
Qed.

Lemma da2_left_compat : forall ρ (Hρ : ρ <> 0), Proper (eq ==> opt_eq (Loc.eq ==> Common.Sim.eq))
  (lift_conf (fun g : Names.G => if left_dec g then Some (fun c : Loc.t => homothecy c Hρ) else None)).
Proof.
intros ρ Hρ ? [g | b] ?; subst; simpl.
+ LR_dec; try reflexivity; [].
  intros c1 c2 Hc. now apply homothecy_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_ratio_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_conf (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  Sim.zoom (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. LR_dec.
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_conf (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  Loc.eq (Sim.center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. LR_dec.
  - intro H. inversion_clear H. reflexivity.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Definition da2_left (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => Loc.origin;
  step := lift_conf (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) |}.
Proof.
+ apply da2_left_compat.
+ apply homothecy_ratio_1.
+ apply homothecy_center_1.
Defined.

Lemma da2_right_compat : forall ρ (Hρ : ρ <> 0), Proper (eq ==> opt_eq (Loc.eq ==> Common.Sim.eq))
  (lift_conf (fun g => if left_dec g then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ)))).
Proof.
intros ρ Hρ ? [g | b] ?; subst; simpl.
+ LR_dec; try reflexivity; [].
  intros c1 c2 Hc. now apply homothecy_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_ratio_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_conf (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  Sim.zoom (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. LR_dec.
  - discriminate.
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0, Ropp_neq_0_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_conf (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  Loc.eq (Sim.center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. LR_dec.
  - discriminate.
  - intro H. inversion_clear H. reflexivity.
+ apply Fin.case0. exact b.
Qed.

Definition da2_right (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => Loc.origin;
  step := lift_conf (fun g => if left_dec g
                             then None else Some (fun c => homothecy c (Ropp_neq_0_compat _ Hρ))) |}.
Proof.
+ apply da2_right_compat.
+ apply homothecy_ratio_2.
+ apply homothecy_center_2.
Defined.

CoFixpoint bad_demon2 ρ (Hρ : ρ <> 0) : demon :=
  NextDemon (da2_left Hρ)
  (NextDemon (da2_right (ratio_inv Hρ))
  (bad_demon2 (ratio_inv (ratio_inv Hρ)))). (* ρ updated *)

Lemma bad_demon_head2_1 : forall ρ (Hρ : ρ <> 0), demon_head (bad_demon2 Hρ) = da2_left Hρ.
Proof. reflexivity. Qed.

Lemma bad_demon_head2_2 : forall ρ (Hρ : ρ <> 0),
  demon_head (demon_tail (bad_demon2 Hρ)) = da2_right (ratio_inv Hρ).
Proof. reflexivity. Qed.

Lemma bad_demon_tail2 :
  forall ρ (Hρ : ρ <> 0), demon_tail (demon_tail (bad_demon2 Hρ)) = bad_demon2 (ratio_inv (ratio_inv Hρ)).
Proof. reflexivity. Qed.

Lemma da_eq_step_None : forall d1 d2, deq d1 d2 ->
  forall g, step (demon_head d1) (Good g) = None <-> step (demon_head d2) (Good g) = None.
Proof.
intros d1 d2 Hd g.
assert (Hopt_eq : opt_eq (Loc.eq ==> Sim.eq)%signature
                    (step (demon_head d1) (Good g)) (step (demon_head d2) (Good g))).
{ apply step_da_compat; trivial. now rewrite Hd. }
  split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

Theorem kFair_bad_demon2_by_eq : forall ρ (Hρ : ρ <> 0) d, deq d (bad_demon2 Hρ) -> kFair 1 d.
Proof.
cofix fair_demon. intros ρ Hρ d Heq.
constructor; [| constructor].
* setoid_rewrite Heq.
  intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_dec g1).
  + constructor 1. rewrite bad_demon_head2_1. simpl. destruct (left_dec g1); eauto. discriminate.
  + destruct (left_dec g2).
    - constructor 2.
      -- rewrite bad_demon_head2_1. simpl. now LR_dec.
      -- rewrite bad_demon_head2_1. simpl. LR_dec. discriminate.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. LR_dec. discriminate.
    - constructor 3.
      -- rewrite bad_demon_head2_1. simpl. now LR_dec.
      -- rewrite bad_demon_head2_1. simpl. now LR_dec.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. LR_dec. discriminate.
* setoid_rewrite Heq.
  intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_dec g1).
  + destruct (left_dec g2).
    - constructor 3.
      -- rewrite bad_demon_head2_2. simpl. now LR_dec.
      -- rewrite bad_demon_head2_2. simpl. now LR_dec.
      -- rewrite bad_demon_tail2. constructor 1. simpl. LR_dec. discriminate.
    - constructor 2.
      -- rewrite bad_demon_head2_2. simpl. now LR_dec.
      -- rewrite bad_demon_head2_2. simpl. LR_dec. discriminate.
      -- rewrite bad_demon_tail2. constructor 1. simpl. LR_dec. discriminate.
  + constructor 1. rewrite bad_demon_head2_2. simpl. LR_dec. discriminate.
* eapply fair_demon. now rewrite Heq, bad_demon_tail2.
Qed.

Theorem kFair_bad_demon2 : forall ρ (Hρ : ρ <> 0), kFair 1 (bad_demon2 Hρ).
Proof. intros. eapply kFair_bad_demon2_by_eq. reflexivity. Qed.

Lemma left_right_dist_forbidden : forall (config : Config.t),
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  Loc.dist (config (Good gfirst)) (config (Good glast)) <> 0 ->
  forbidden config.
Proof.
intros config Hleft Hright Hdist.
assert (Hlist_left : eqlistA Loc.eq (map config (map Good left)) (alls (config (Good gfirst)) (Nat.div2 N.nG))).
{ erewrite map_map, <- Spect.Names.Gnames_length, <- half1_length, <- map_length, <- (alls_caracA _).
  intros pt Hin. rewrite (InA_map_iff _ _) in Hin.
  - destruct Hin as [g [Hpt Hg]]. rewrite <- Hpt. apply Hleft. now rewrite <- InA_Leibniz.
  - intros ? ? ?. now subst. }
assert (Hlist_right : eqlistA Loc.eq (map config (map Good right)) (alls (config (Good glast)) (Nat.div2 N.nG))).
{ rewrite map_map. rewrite <- Spect.Names.Gnames_length at 2.
  erewrite <- half2_even_length, <- map_length, <- (alls_caracA _).
  + intros pt Hin. rewrite (InA_map_iff _ _) in Hin.
    - destruct Hin as [g [Hpt Hg]]. rewrite <- Hpt. apply Hright. now rewrite <- InA_Leibniz.
    - intros ? ? ?. now subst.
  + rewrite Spect.Names.Gnames_length. apply even_nG. }
assert (Heq : eqlistA Loc.eq (map config Spect.Names.names)
                      (alls (config (Good gfirst)) (Nat.div2 N.nG) ++ alls (config (Good glast)) (Nat.div2 N.nG))).
{ now rewrite left_right_partition, map_app, <- Hlist_left, <- Hlist_right. }
assert (~ Loc.eq (config (Good gfirst)) (config (Good glast))) by now rewrite <- Loc.dist_defined.
unfold forbidden. repeat split; try (now apply even_nG || apply nG_ge_2); [].
exists (config (Good gfirst)), (config (Good glast)).
repeat split.
+ assumption.
+ rewrite Spect.from_config_spec, Spect.Config.list_spec.
  rewrite Heq. rewrite countA_occ_app. rewrite (countA_occ_alls_in _), countA_occ_alls_out; try ring.
  intro Habs. now symmetry in Habs.
+ rewrite Spect.from_config_spec, Spect.Config.list_spec.
  rewrite Heq. rewrite countA_occ_app. rewrite (countA_occ_alls_in _), countA_occ_alls_out; try ring.
  assumption.
Qed.

Lemma round_da2_left_next_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  forall g, In g left -> Loc.eq (round r (da2_left Hρ) config (Good g))
                                (round r (da2_left Hρ) config (Good gfirst)).
Proof.
intros config ρ Hρ Hleft g Hin.
assert (Hin' := gfirst_left).
unfold round. simpl. do 2 LR_dec. f_equiv.
- f_equiv. apply homothecy_compat. now apply Hleft.
- apply pgm_compat. do 4 f_equiv. apply homothecy_compat. now apply Hleft.
Qed.

Lemma round_da2_left_next_right : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  forall g, In g right -> Loc.eq (round r (da2_left Hρ) config (Good g))
                                 (round r (da2_left Hρ) config (Good glast)).
Proof.
intros config ρ Hρ Hright g Hin.
assert (Hin' := glast_right).
unfold round. simpl. do 2 LR_dec. now apply Hright.
Qed.

Lemma dist_homothecy_spectrum_centered_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  Loc.eq (config (Good glast)) (Loc.add (config (Good gfirst)) (Loc.mul (/ρ) Loc.unit)) ->
  forall g, In g left -> Spect.eq (!! (Config.map (homothecy (config (Good g)) Hρ) config)) (!! conf1).
Proof.
intros config ρ Hρ Hleft Hright Hdist g Hin. f_equiv. intro id. unfold Config.map.
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
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  Loc.dist (config (Good gfirst)) (config (Good glast)) = /ρ ->
  Loc.dist (round r (da2_left Hρ) config (Good gfirst))
           (round r (da2_left Hρ) config (Good glast)) = Loc.dist Loc.unit move / ρ.
Proof.
intros config ρ Hρ Hleft Hright Hdist.
assert (Hin' := gfirst_left). assert (Hin'' := glast_right).
unfold round. simpl. do 2 LR_dec.
(*rewrite dist_homothecy_spectrum_centered_left; auto; [].
simpl. rewrite Hdist. setoid_rewrite Loc.add_comm at 1 2. rewrite Loc.add_assoc.
f_equiv.*)
(* This lemma is wrong. See FIXME *)
Admitted.

Lemma round_da2_right_next_left : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  forall g, In g left -> Loc.eq (round r (da2_right Hρ) config (Good g))
                                (round r (da2_right Hρ) config (Good gfirst)).
Proof.
intros config ρ Hρ Hleft g Hin.
assert (Hin' := gfirst_left).
unfold round. simpl. do 2 LR_dec. now apply Hleft.
Qed.

Lemma round_da2_right_next_right : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  forall g, In g right -> Loc.eq (round r (da2_right Hρ) config (Good g))
                                 (round r (da2_right Hρ) config (Good glast)).
Proof.
intros config ρ Hρ Hright g Hin.
assert (Hin' := glast_right).
unfold round. simpl. do 2 LR_dec. f_equiv.
- f_equiv. apply homothecy_compat. now apply Hright.
- apply pgm_compat. do 4 f_equiv. apply homothecy_compat. now apply Hright.
Qed.


Lemma round_da2_right_next_dist : forall (config : Config.t) ρ (Hρ : ρ <> 0),
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  Loc.dist (config (Good gfirst)) (config (Good glast)) = /ρ ->
  Loc.dist (round r (da2_right Hρ) config (Good gfirst))
           (round r (da2_right Hρ) config (Good glast)) = Loc.dist Loc.unit move / ρ.
Proof.
intros config ρ Hρ Hleft Hright Hdist.
assert (Hin' := gfirst_left).
assert (Hin'' := glast_right).
unfold round. simpl. do 2 LR_dec.
(* This lemma is wrong. See FIXME *)
Admitted.


Theorem Always_forbidden2 : forall ρ (Hρ : ρ <> 0) config,
  forbidden config ->
  (forall g, In g left -> Loc.eq (config (Good g))(config (Good gfirst))) ->
  (forall g, In g right -> Loc.eq (config (Good g)) (config (Good glast))) ->
  Loc.dist (config (Good gfirst)) (config (Good glast)) = /ρ ->
  Always_forbidden (execute r (bad_demon2 Hρ) config).
Proof.
cofix differs. intros ρ Hρ config Hforbidden Hleft Hright Hdist.
constructor; [| constructor].
  (* Inital state *)
- cbn. assumption.
  (* State after one step *)
- cbn. apply left_right_dist_forbidden.
  + intros g Hg. now apply round_da2_left_next_left.
  + intros g Hg. now apply round_da2_left_next_right.
  + rewrite round_da2_left_next_dist; trivial; []. now apply ratio_neq_0.
(* State after two steps *)
- do 2 rewrite execute_tail.
  rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  apply differs.
  + cbn. apply left_right_dist_forbidden.
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

Definition bad_demon : demon.
  destruct (Loc.eq_dec move Loc.unit) as [Hmove | Hmove].
  (** Robots exchange positions **)
  - exact bad_demon1.
    (** Robots do no exchange positions **)
  - assert (Hneq : / Loc.dist Loc.unit Loc.origin <> 0).
    { apply Rinv_neq_0_compat. rewrite Loc.dist_defined. apply Loc.non_trivial. }
    exact (bad_demon2 Hmove Hneq).
Defined.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof.
intros. unfold bad_demon.
destruct (Loc.eq_dec move Loc.unit).
- apply kFair_mon with 0%nat. exact kFair_bad_demon1. omega.
- now apply kFair_bad_demon2.
Qed.

Theorem kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon;auto.
- auto.
Qed.

(** * Final theorem

Given a non empty finite even set [G] and a robogram [r] on ([G]) × ∅,
there is no (k>0)-fair demon  for which the gathering problem is solved for any starting configuration. *)

Theorem noGathering :
  forall k, (1<=k)%nat -> ~(forall d, kFair k d -> FullSolGathering r d).
Proof.
intros k h Habs.
specialize (Habs bad_demon (kFair_bad_demon' h) conf1).
(* specialize (Habs 1%nat (bad_demon 1) (kFair_bad_demon R1_neq_R0) gconf1). *)
destruct Habs as [pt Habs]. revert Habs. apply different_no_gathering.
unfold bad_demon.
destruct (Loc.eq_dec move Loc.unit) as [Hmove | Hmove].
+ now apply Always_forbidden1.
+ apply (Always_forbidden2 Hmove).
  - apply conf1_forbidden.
  - assert (Hleft := gfirst_left). intros. cbn. now do 2 LR_dec.
  - assert (Hright := glast_right). intros. cbn. now do 2 LR_dec.
  - assert (Hleft := gfirst_left). assert (Hright := glast_right). intros. cbn. do 2 LR_dec.
    rewrite Rinv_involutive; apply Loc.dist_sym || (rewrite Loc.dist_defined; apply Loc.non_trivial).
Qed.

End GatheringEven.

Print Assumptions noGathering.
