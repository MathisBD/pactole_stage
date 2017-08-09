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
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.    *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Spaces.R.
Require Import Pactole.Gathering.Definitions.
Set Implicit Arguments.
Close Scope R_scope.


Section ImpossibilityProof.

(** There are n good robots and no byzantine ones. *)
Parameter n : nat.
(** We assume that the number of robots is even and non-null. *)
Axiom even_nG : Nat.Even n.
Axiom nG_non_0 : n <> 0.

Global Instance MyRobotsDef : NamesDef := RobotsDef n 0.
Global Instance MyRobots : Names := Robots n 0.

(* BUG?: To help finding correct instances, loops otherwise! *)
Existing Instance R_Setoid.
Existing Instance R_EqDec.
Existing Instance R_RMS.

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation "!!" := (@spect_from_config R Datatypes.unit _ _ _ _ _ _ _ multiset_spectrum) (at level 1).
Notation spectrum := (@spectrum R Datatypes.unit _ _ _ _ Info _ MyRobots _).
Notation robogram := (@robogram R Datatypes.unit _ _ _ _ Info _ MyRobots _).
Notation configuration := (@configuration R Datatypes.unit _ _ _ _ _ _ _).
Notation config_list := (@config_list R Datatypes.unit _ _ _ _ _ _ _).
Notation round := (@round R Datatypes.unit _ _ _ _ _ _ _).
Notation execution := (@execution R Datatypes.unit _ _ _ _ _).


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


(** *  Proof of the impossiblity of gathering for two robots  **)

(** From now on and until the final theorem we assume given a robogram [r]. *)

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
    | Good g => mk_info (if left_dec g then 0 else 1)
    | Byz b => mk_info 0
  end.

(** The symmetrical configuration of the starting configuration **)
Definition config2 : configuration := fun id =>
  match id with
    | Good g => mk_info (if left_dec g then 1 else 0)
    | Byz b => mk_info 0
  end.

Definition spectrum0 := add 0 (Nat.div2 nG) (singleton 1 (Nat.div2 nG)).

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
    assert (Heq : forall a b : R,
                  List.map (fun x => if in_dec Geq_dec x (gl :: half1 l) then a else b) l
                = List.map (fun x => if in_dec Geq_dec x (half1 l) then a else b) l).
    { intros a b. apply map_ext_in. intros g Hg.
      destruct (in_dec Geq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Geq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Geq_dec g (half1 l)); trivial. elim Hout. intuition. }
    do 2 rewrite Heq.
    Rdec_full; subst; Rdec; try Rdec_full; subst; Rdec; setoid_rewrite plus_comm; simpl; auto.
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
    assert (Heq : List.map (fun x => if in_dec Geq_dec x (gl :: half1 l) then 0 else 1) l
                = List.map (fun x => if in_dec Geq_dec x (half1 l) then 0 else 1) l).
    { apply map_ext_in. intros g Hg.
      destruct (in_dec Geq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try (now subst; contradiction); [].
        destruct (in_dec Geq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Geq_dec g (half1 l)); trivial; []. elim Hout. intuition. }
    rewrite Heq, Hrec.
    assert (0 <> 1) by (auto using R1_neq_R0). assert (1 <> 0) by auto using R1_neq_R0.
    do 2 Rdec_full; hnf in *; subst; Rdec; try congruence;
    repeat rewrite ?add_same, ?add_other, ?singleton_same, ?singleton_other; simpl; trivial;
    omega || intro; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* rewrite Gnames_length. apply even_nG.
Qed.

Corollary config1_invalid : invalid config1.
Proof.
repeat split; try (exact even_nG || exact nG_ge_2); [].
exists 0, 1. rewrite spect_config1. repeat split.
+ intro. now apply R1_neq_R0.
+ unfold spectrum0. rewrite add_same, singleton_spec. now compute; Rdec.
+ unfold spectrum0. rewrite add_other, singleton_spec; try apply R1_neq_R0. now compute; Rdec.
Qed.

Corollary config2_invalid : invalid config2.
Proof. split; try exact even_nG. cbn. setoid_rewrite <- config1_config2_spect_equiv. apply config1_invalid. Qed.

(** Two similarities used: the identity and the symmetry wrt a point c. *)

(** The swapping similarity *)
Definition bij_swap (c : R) : Bijection.bijection R.
refine {|
  Bijection.section := fun x => c - x;
  Bijection.retraction := fun x => c - x |}.
Proof.
abstract (intros; simpl; split; intro; subst; field).
Defined.

Lemma bij_swap_ratio : forall c x y : R, dist (bij_swap c x) (bij_swap c y) = 1 * dist x y.
Proof.
intros c x y. rewrite Rmult_1_l. compute.
destruct (Rcase_abs (x + - y)), (Rcase_abs (c + - x + - (c + - y))); lra.
Qed.

(* We need to define it with a general center although only 1 will be used. *)
Definition swap (c : R) : similarity R.
refine {|
  sim_f := bij_swap c;
  zoom := 1;
  center := c |}.
Proof.
- abstract (compute; field).
- exact (bij_swap_ratio c).
Defined.

Lemma swap_config1 : map_config (swap 1) config1 == config2.
Proof. apply no_byz_eq. intro g. unfold swap. simpl. destruct (left_dec g); simpl; hnf; ring. Qed.

Lemma swap_config2 : map_config (swap 1) config2 == config1.
Proof. apply no_byz_eq. intro g. unfold swap. simpl. destruct (left_dec g); simpl; hnf; ring. Qed.

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

Hypothesis Hmove : move = 1.

Lemma da1_ratio : forall id sim c,
  lift_config (fun _ => Some (fun c => if Rdec c 0 then Similarity.id else swap c)) id = Some sim ->
  zoom (sim c) <> 0.
Proof.
intros id sim c. apply (no_byz id). intros g Heq.
inversion_clear Heq. Rdec_full; simpl; apply R1_neq_R0.
Qed.

Lemma da1_center : forall id sim c,
  lift_config (fun _ => Some (fun c => if Rdec c 0 then Similarity.id else swap c)) id = Some sim ->
  center (sim c) = c.
Proof.
intros id sim c. apply (no_byz id). intros g Heq.
inversion_clear Heq. Rdec_full; simpl; subst; reflexivity.
Qed.

Definition da1 : demonic_action := {|
  relocate_byz := fun b => mk_info 0;
  step := lift_config (fun g => Some (fun c => if Rdec c 0 then Similarity.id else swap c));
  step_zoom := da1_ratio;
  step_center := da1_center |}.

Definition bad_demon1 : demon := Stream.constant da1.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof. coinduction bad_fair1. intros id1 id2. constructor. apply (no_byz id1). discriminate. Qed.

Lemma round_simplify_1_1 : round r da1 config1 == config2.
Proof.
apply no_byz_eq. intro g; unfold round; simpl.
destruct (left_dec g) as [Hleft | Hright].
- Rdec. rewrite map_config_id. apply Hmove.
- Rdec. setoid_rewrite swap_config1. simpl.
  rewrite <- config1_config2_spect_equiv. fold move. rewrite Hmove. ring.
Qed.

Lemma round_simplify_1_2 : round r da1 config2 == config1.
Proof.
apply no_byz_eq. intro g; unfold round. simpl. cbn [step da1 lift_config fst config2].
destruct (left_dec g) as [Hleft | Hright].
- Rdec. rewrite swap_config2. simpl. replace 0 with (1 - 1) by ring. f_equal. apply Hmove.
- Rdec. rewrite map_config_id. simpl. rewrite <- config1_config2_spect_equiv. apply Hmove.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_invalid1_by_eq : forall config : configuration, config == config1 ->
  Always_invalid (execute r bad_demon1 config).
Proof.
cofix differs. intros config Heq. constructor.
+ rewrite Heq. apply config1_invalid.
+ cbn. constructor.
  - simpl. eapply round_compat in Heq; try reflexivity.
    rewrite Heq, round_simplify_1_1. apply config2_invalid.
  - (* FIXME: slow! [rewrite Heq, round_simplify_1_1, round_simplify_1_2] should work*)
    cbn. apply differs. rewrite <- round_simplify_1_2.
    apply round_compat; try reflexivity; []. rewrite <- round_simplify_1_1.
    now apply round_compat.
Qed.

Corollary Always_invalid1 : Always_invalid (execute r bad_demon1 config1).
Proof. apply Always_invalid1_by_eq. reflexivity. Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time **)

Section MoveNot1.

Hypothesis Hmove : move <> 1.

Lemma minus_1_move : 1 - move <> 0.
Proof. apply Rminus_eq_contra. intro. now apply Hmove. Qed.

Hint Immediate minus_1_move.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (1 - move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (1 - move)) in Habs.
unfold Rdiv in Habs.
replace ( (1 - move) * (ρ * / (1 - move))) with (ρ * ((1 - move) * / (1 - move))) in Habs by ring.
rewrite Rinv_r in Habs.
- now ring_simplify in Habs.
- auto.
Qed.
Print Assumptions ratio_inv.
(* FIXME: Why is there a dependency on Eqdep.Eq_rect_eq.eq_rect_eq? *)

Lemma homothecy_ratio_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  zoom (sim c) <> 0.
Proof.
intros ρ Hρ id sim c. apply (no_byz id). clear id.
intro g. simpl. destruct_match.
- intro H. inversion_clear H. simpl. now apply Rabs_no_R0.
- discriminate.
Qed.

Lemma homothecy_center_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  center (sim c) == c.
Proof.
intros ρ Hρ id sim c. apply (no_byz id). clear id.
intro g. simpl. destruct_match.
- intro H. inversion_clear H. reflexivity.
- discriminate.
Qed.

Definition da2_left (ρ : R) (Hρ : ρ <> 0) : demonic_action := {|
  relocate_byz := fun b => mk_info 0;
  step := lift_config (fun g => if left_dec g then Some (fun c => homothecy c Hρ) else None);
  step_zoom := homothecy_ratio_1 Hρ;
  step_center := homothecy_center_1 Hρ |}.

Lemma homothecy_ratio_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  zoom (sim c) <> 0.
Proof.
intros ρ Hρ id sim c. apply (no_byz id). clear id.
intro g. simpl. destruct_match.
- discriminate.
- intro H. inversion_clear H. simpl. now apply Rabs_no_R0, Ropp_neq_0_compat.
Qed.

Lemma homothecy_center_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_config (fun g => if left_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  center (sim c) == c.
Proof.
intros ρ Hρ id sim c. apply (no_byz id). clear id.
intro g. simpl. destruct_match.
- discriminate.
- intro H. inversion_clear H. reflexivity.
Qed.

Definition da2_right (ρ : R) (Hρ : ρ <> 0) : demonic_action := {|
  relocate_byz := fun b => mk_info 0;
  step := lift_config (fun g => if left_dec g
                                then None else Some (fun c => homothecy c (Ropp_neq_0_compat _ Hρ)));
  step_zoom := homothecy_ratio_2 Hρ;
  step_center := homothecy_center_2 Hρ |}.

CoFixpoint bad_demon2 ρ (Hρ : ρ <> 0) : demon :=
  Stream.cons (da2_left Hρ)
  (Stream.cons (da2_right (ratio_inv Hρ))
  (bad_demon2 (ratio_inv (ratio_inv Hρ)))). (* ρ updated *)

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
      -- constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
    - constructor 3; simpl.
      -- destruct (left_dec g1); eauto. exfalso. eauto.
      -- destruct (left_dec g2); eauto. exfalso. eauto.
      -- constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
* setoid_rewrite Heq.
  intros id1 id2. apply (no_byz id2), (no_byz id1). intros g1 g2.
  destruct (left_dec g1).
  + destruct (left_dec g2).
    - constructor 3; simpl.
      -- destruct (left_dec g1); eauto. exfalso. eauto.
      -- destruct (left_dec g2); eauto. exfalso. eauto.
      -- constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
    - constructor 2; simpl.
      -- destruct (left_dec g1); eauto. exfalso. eauto.
      -- destruct (left_dec g2); eauto. discriminate.
      -- constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
  + constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
* eapply fair_demon. rewrite Heq. unfold bad_demon2. simpl Stream.tl. fold bad_demon2. reflexivity.
Qed.

Theorem kFair_bad_demon2 : forall ρ (Hρ : ρ <> 0), kFair 1 (bad_demon2 Hρ).
Proof. intros. eapply kFair_bad_demon2_by_eq. reflexivity. Qed.

(* In an invalid configuration, half of the robots are in the same place. *)
Lemma dist_left : forall d (Hd : d <> 0) (config : configuration),
  (forall gr gl, List.In gr right -> List.In gl left -> fst (config (Good gr)) - fst (config (Good gl)) = d) ->
  forall g, List.In g left -> fst (config (Good g)) = fst (config (Good gfirst)).
Proof.
intros d Hd config Hconfig g Hg.
cut (fst (config (Good glast)) - fst (config (Good g)) = fst (config (Good glast)) - fst (config (Good gfirst))).
+ intro Heq. unfold Rminus in Heq. apply Rplus_eq_reg_l in Heq. setoid_rewrite <- Ropp_involutive.
  now apply Ropp_eq_compat.
+ assert (Hright := glast_right). repeat rewrite Hconfig; auto.
Qed.

Lemma dist_right : forall d (Hd : d <> 0) (config : configuration),
  (forall gr gl, List.In gr right -> List.In gl left -> fst (config (Good gr)) - fst (config (Good gl)) = d) ->
  forall g, List.In g right -> fst (config (Good g)) = fst (config (Good glast)).
Proof.
intros d Hd config Hconfig g Hg.
cut (fst (config (Good g)) - fst (config (Good gfirst))
     = fst (config (Good glast)) - fst (config (Good gfirst))).
+ intro Heq. unfold Rminus in Heq. now apply Rplus_eq_reg_r in Heq.
+ assert (Hleft := gfirst_left). repeat rewrite Hconfig; auto.
Qed.


Lemma dist_homothecy_spectrum_centered_left : forall ρ (Hρ : ρ <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g, List.In g left -> !! (map_config (fun x : R => ρ * (x - fst (config (Good g)))) config) == !! config1.
Proof.
intros ρ Hρ config Hconfig g Hg. apply @spect_from_config_compat. intro id.
apply no_info, (no_byz id). intro g'. simpl. destruct_match.
+ setoid_rewrite (dist_left (Rinv_neq_0_compat _ Hρ) _ Hconfig); trivial; []. ring.
+ rewrite Hconfig; trivial; [|].
  - now rewrite Rinv_r.
  - now apply not_left_is_right.
Qed.

(** To prove this equality, we go through [!! config1], using an homothecy to get it. *)
Lemma dist_spectrum : forall d (Hd : d <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = d) ->
  !! config == add (fst (config (Good gfirst))) (Nat.div2 nG)
                   (singleton (fst (config (Good glast))) (Nat.div2 nG)).
Proof.
intros d Hd config Hconfig.
rewrite <- (Rinv_involutive d) in Hconfig; trivial; [].
assert (Hd' := Rinv_neq_0_compat _ Hd).
rewrite <- map_config_id at 1.
change (@Datatypes.id R) with (Bijection.section (sim_f Similarity.id)).
rewrite <- (compose_inverse_l (homothecy (fst (config (Good gfirst))) Hd')).
unfold compose, Bijection.bij_compose; cbn [sim_f Bijection.section].
rewrite <- map_config_merge, <- spect_from_config_map; autoclass; [].
transitivity (map (homothecy (fst (config (Good gfirst))) Hd' ⁻¹) spectrum0).
+ apply map_compat; autoclass; []. rewrite <- spect_config1.
  apply (dist_homothecy_spectrum_centered_left Hd' _ Hconfig gfirst); auto.
+ unfold spectrum0. rewrite map_add, map_singleton; autoclass; []. f_equiv.
  - simpl. ring.
  - f_equiv. simpl. rewrite <- (Hconfig glast gfirst); auto; []. compute; ring.
Qed.

Lemma dist_invalid : forall d (Hd : d <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = d) ->
  invalid config.
Proof.
intros d Hd config Hconfig. unfold invalid. repeat split; try apply even_nG || apply nG_ge_2; [].
assert (Hdiff : fst (config (Good gfirst)) <> fst (config (Good glast))).
{ apply Rminus_not_eq_right. rewrite Hconfig; auto. }
exists (fst (config (Good gfirst))), (fst (config (Good glast))). repeat split.
- assumption.
- rewrite dist_spectrum; try eassumption; []. rewrite add_same, singleton_other; auto.
- rewrite dist_spectrum; try eassumption; []. rewrite add_other, singleton_same; try intro; auto.
Qed.

Lemma round_dist2_left : forall ρ (Hρ : ρ <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g1 g2, List.In g1 right -> List.In g2 left ->
    fst (round r (da2_left Hρ) config (Good g1)) - fst (round r (da2_left Hρ) config (Good g2)) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_dec g1), (left_dec g2); try (now exfalso; eauto); [].
cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
rewrite <- (Hconfig _ _ Hg1 Hg2) at 2. ring_simplify.
replace (fst (config (Good g1)) - fst (config (Good g2)) - move / ρ)
  with (fst (config (Good g1)) - move / ρ - fst (config (Good g2))) by ring.
field_simplify; trivial; []. do 2 f_equal; try (now cbn; field); [].
unfold move. change eq with equiv. apply pgm_compat. now apply dist_homothecy_spectrum_centered_left.
Qed.

Corollary round2_left_right : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g1 g2, List.In g1 right -> List.In g2 right ->
    round r (da2_left Hρ) config (Good g1) == round r (da2_left Hρ) config (Good g2).
Proof.
intros. apply no_info. apply Rplus_eq_reg_l with (- fst (round r (da2_left Hρ) config (Good gfirst))).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_left : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g1 g2, List.In g1 left -> List.In g2 left ->
    round r (da2_left Hρ) config (Good g1) == round r (da2_left Hρ) config (Good g2).
Proof.
intros. apply no_info. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_r with (fst (round r (da2_left Hρ) config (Good glast))).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_invalid : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  invalid (round r (da2_left Hρ) config).
Proof.
intros ρ Hρ config Hconfig.
apply (dist_invalid (d := (1 - move) / ρ)).
- rewrite <- Rinv_Rdiv; trivial. now apply Rinv_neq_0_compat, ratio_inv. lra.
- intros. now apply round_dist2_left.
Qed.

Lemma dist_homothecy_spectrum_centered_right : forall ρ (Hρ : ρ <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g, List.In g right -> !! (map_config (homothecy (fst (config (Good g))) (Ropp_neq_0_compat _ Hρ)) config)
                               == !! config2.
Proof.
intros ρ Hρ config Hconfig g Hg. apply @spect_from_config_compat.
apply no_byz_eq. intro g'. simpl.
change (sig (fun k => lt k n)) with G. change (sig (fun k => lt k 0)) with B.
destruct (left_dec g') as [Hg' | Hg'].
+ replace (- ρ * (fst (config (Good g')) + - fst (config (Good g))))
    with (ρ * (fst (config (Good g)) - fst (config (Good g')))) by ring.
  rewrite Hconfig; trivial; []. now rewrite Rinv_r.
+ setoid_rewrite (dist_right (Rinv_neq_0_compat _ Hρ) _ Hconfig); trivial; [|].
  - ring.
  - now apply not_left_is_right.
Qed.

Lemma round_dist2_right : forall ρ (Hρ : ρ <> 0) (config : configuration),
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  forall g1 g2, List.In g1 right -> List.In g2 left ->
  fst (round r (da2_right Hρ) config (Good g1)) - fst (round r (da2_right Hρ) config (Good g2)) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_dec g1), (left_dec g2); try (now exfalso; eauto); [].
cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
rewrite <- (Hconfig _ _ Hg1 Hg2), <- Ropp_inv_permute; trivial; [].
field_simplify; trivial; []. do 3 f_equal.
unfold move. change eq with equiv. apply pgm_compat. rewrite config1_config2_spect_equiv.
now apply (dist_homothecy_spectrum_centered_right Hρ).
Qed.

Theorem Always_invalid2 : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, List.In g1 right -> List.In g2 left -> fst (config (Good g1)) - fst (config (Good g2)) = /ρ) ->
  Always_invalid (execute r (bad_demon2 Hρ) config).
Proof.
cofix differs. intros ρ Hρ config Hconfig.
constructor; [| constructor].
- (* Inital state *)
  cbn. apply (dist_invalid (Rinv_neq_0_compat _ Hρ)). assumption.
- (* State after one step *)
  cbn. now apply round2_left_invalid.
- (* State after two steps *)
  cbn. apply differs. intros g1 g2 Hg1 Hg2.
  replace (/ (ρ / (1 - move) / (1 - move))) with ((1 - move) / (ρ / (1 - move))) by (field; auto).
  apply round_dist2_right; trivial.
  replace (/ (ρ / (1 - move))) with ((1 - move) / ρ) by (field; auto).
  now apply round_dist2_left.
Qed.

End MoveNot1.

(** **  Merging both cases  **)

Definition bad_demon : @demon R Datatypes.unit _ _ _ _.
Proof.
destruct (Rdec move 1) as [Hmove | Hmove].
- (** Robots exchange positions **)
  exact bad_demon1.
- (** Robots do not exchange positions **)
  exact (bad_demon2 Hmove R1_neq_R0).
Defined.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof.
intros. unfold bad_demon.
destruct (Rdec move 1).
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
destruct (Rdec move 1) as [Hmove | Hmove].
+ now apply Always_invalid1.
+ apply (Always_invalid2 Hmove R1_neq_R0 config1); try reflexivity; [].
  intros. simpl. destruct (left_dec g1), (left_dec g2); simpl; field || exfalso; eauto.
Qed.

End ImpossibilityProof.

Print Assumptions noGathering.
(* FIXME: Why is there a dependency on Eqdep.Eq_rect_eq.eq_rect_eq? *)
