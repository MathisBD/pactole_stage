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

Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.EuclideanSpace.
Require Import Pactole.CaseStudies.Gathering.Definitions.
Require Pactole.CaseStudies.Gathering.WithMultiplicity.
Import Pactole.Observations.MultisetObservation.
Require Import Pactole.Models.Rigid.
Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.
Import Datatypes. (* To recover Datatypes.id *)
Typeclasses eauto := (bfs).
Remove Hints eq_setoid : typeclass_instances.
(* TODO: make equiv not unfolded everywhere. *)
Arguments equiv : simpl never.


Section ImpossibilityProof.

(** There are n good robots and no byzantine ones. *)
Variable n : nat.
Instance MyRobots : Names := Robots n 0.

(** We assume that the number of robots is even and non-null. *)
Hypothesis even_nG : Nat.Even n.
Hypothesis nG_non_0 : n <> 0.

Local Transparent G B.

(** The setting is an arbitrary metric space over R. *)
Context `{Location}.
(* Instance St : State location := OnlyLocation (fun _ => True). *)
Context {VS : RealVectorSpace location}.
Context {ES : EuclideanSpace location}.

(** We assume that the space is equipped with a [build_similarity] function
    that can map any pair of distinct points to any other pair. *)
Variable build_similarity : forall {pt1 pt2 pt3 pt4 : location},
  pt1 =/= pt2 -> pt3 =/= pt4 -> similarity location.
Hypothesis build_similarity_compat : forall pt1 pt1' pt2 pt2' pt3 pt3' pt4 pt4'
  (H12 : pt1 =/= pt2) (H34 : pt3 =/= pt4) (H12' : pt1' =/= pt2') (H34' : pt3' =/= pt4'),
  pt1 == pt1' -> pt2 == pt2' -> pt3 == pt3' -> pt4 == pt4' ->
  build_similarity H12 H34 == build_similarity H12' H34'.

Hypothesis build_similarity_eq1 : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity Hdiff12 Hdiff34 pt1 == pt3.
Hypothesis build_similarity_eq2 : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity Hdiff12 Hdiff34 pt2 == pt4.
Hypothesis build_similarity_inverse : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  inverse (build_similarity Hdiff12 Hdiff34) == build_similarity Hdiff34 Hdiff12.
Hypothesis build_similarity_swap : forall pt1 pt2 pt3 pt4 (Hdiff12 : pt1 =/= pt2) (Hdiff34 : pt3 =/= pt4),
  build_similarity (symmetry Hdiff12) (symmetry Hdiff34) == build_similarity Hdiff12 Hdiff34.

(** We are in a rigid formalism with no other info than the location,
    so the demon makes no choice and robots compute a target destination in the considered space. *)
Instance ActiveChoice : update_choice unit := NoChoice.
Instance InactiveChoice : inactive_choice unit := { inactive_choice_EqDec := unit_eqdec }.
Instance RobotChoice : robot_choice location := { robot_choice_Setoid := location_Setoid }.
Instance Info : State location := OnlyLocation (fun _ => True).
Instance UpdFun : update_function location (Similarity.similarity location) unit := {
  update := fun _ _ _ target _ => target;
  update_compat := ltac:(now repeat intro) }.
Instance InaFun : inactive_function unit := {
  inactive := fun config id _ => config id;
  inactive_compat := ltac:(repeat intro; subst; auto) }.

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation obs_from_config := (@obs_from_config _ _ _ _ multiset_observation).
Notation "!! config" := (obs_from_config config origin) (at level 10).

(* FIXME: why is this instance not taken from Similarity from Definition *)
Instance Frame : frame_choice (similarity location) := FrameChoiceSimilarity.

Implicit Type config : configuration.
Implicit Type da : demonic_action.


Lemma nG_ge_2 : 2 <= nG.
Proof.
assert (Heven := even_nG). assert (HnG0 := nG_non_0).
inversion Heven. simpl.
destruct n as [| [| ?]]; omega.
Qed.

Lemma half_size_config : Nat.div2 nG > 0.
Proof using even_nG nG_non_0.
assert (Heven := even_nG). assert (HnG0 := nG_non_0).
simpl. destruct n as [| [| ?]].
- omega.
- destruct Heven. omega.
- simpl. omega.
Qed.

(* We need to unfold [obs_is_ok] for rewriting *)
Definition obs_from_config_spec : forall config (pt : location),
  (!! config)[pt] = countA_occ _ equiv_dec pt (List.map get_location (config_list config))
  := WithMultiplicity.obs_from_config_spec.

Lemma no_byz : forall (id : ident) P, (forall g, P (Good g)) -> P id.
Proof using nG_non_0.
intros [g | b] P HP.
+ apply HP.
+ destruct b. omega.
Qed.

Lemma no_byz_eq : forall config1 config2,
  (forall g, get_location (config1 (Good g)) == get_location (config2 (Good g))) -> config1 == config2.
Proof using nG_non_0. intros config1 config2 Heq id. apply (no_byz id), Heq. Qed.

Definition mk_info : location -> location := id.
Arguments mk_info _%VectorSpace_scope.
Lemma mk_info_get_location : forall pt, get_location (mk_info pt) == pt.
Proof using . reflexivity. Qed.
(* 
(** We only assume that we know how to build a state from a position and this is compatible with [get_location]. *)
Variable mk_info : R -> info.
Hypothesis mk_info_get_location : forall pt, get_location (mk_info pt) == pt.
Instance mk_info_compat : Proper (equiv ==> equiv) mk_info.
Proof. simpl. repeat intro. now subst. Qed.
*)

(* To avoid passing the [nB = 0] argument each time. *)
Definition invalid_dec := WithMultiplicity.invalid_dec (reflexivity nB).

(** From [elements], we can rebuild the [config_list]. *)
Lemma obs_makes_config_list : forall config : configuration,
  PermutationA equiv (List.map get_location (config_list config))
                     (List.fold_right (fun '(x, n) acc => alls x n ++ acc) nil (elements (!! config))).
Proof using nG_non_0.
intro config.
unfold obs_from_config. cbn -[get_location config_list elements equiv location].
unfold make_multiset.
induction (List.map get_location (config_list config)) as [| e l]; try reflexivity; [].
(* maybe only the second arg is useful *)
assert (Hcompat : Proper (PermutationA equiv ==> PermutationA equiv ==> PermutationA equiv)
                         (fold_right (fun '(x, n) (acc : list location) => alls x n ++ acc))).
{ clear IHl l. intros l1 l1' Hl1 l2 l2' Hl2.
  revert l1 l1' Hl1. pattern l2, l2'.
  apply PermutationA_ind_bis with equiv; autoclass.
  + intros [] [] ? ? [Hl Hn] Hperm Hrec ? ? ?. simpl in *.
    rewrite Hn, Hl at 1. unfold equiv. now rewrite Hrec.
  + intros [] [] ? ? Hperm Hrec ? ? ?. simpl. rewrite Hrec, 2 app_assoc; try eassumption; [].
    f_equiv. apply PermutationA_app_comm; autoclass.
  + intros ? ? ? Hperm1 Hperm2 Hperm Hrec ? ? ?.
    rewrite Hperm2; try eassumption; []. now apply Hrec. }
cbn [List.map]. rewrite from_elements_cons.
rewrite IHl at 1.
assert (H01 : 0 < 1) by omega.
assert (Hperm := elements_add (x := e) (m := from_elements (List.map (fun x : location => (x, 1)) l))
                              (or_introl H01)).
rewrite (Hcompat _ _ (reflexivity _) _ _ Hperm).
cbn [fold_right alls plus app]. constructor; try reflexivity; [].
destruct (Nat.eq_dec (from_elements (List.map (fun x : location => (x, 1)) l))[e] 0) as [Heq | ?].
* (* [e] is not present in the observation *)
  rewrite Heq. cbn [alls app].
  rewrite Preliminary.removeA_out; try reflexivity; []. (* TODO: put it also in Util/Preliminary *)
  rewrite elements_spec. simpl. intuition.
* (* [e] does appear in the observation *)
  change (alls e (from_elements (List.map (fun x : location => (x, 1)) l))[e] ++
          fold_right (fun '(x, n) (acc : list location) => alls x n ++ acc) nil
            (removeA (eqA:=eq_pair) pair_dec (e, (from_elements (List.map (fun x : location => (x, 1)) l))[e])
              (elements (from_elements (List.map (fun x : location => (x, 1)) l)))))
    with (fold_right (fun '(x, n) (acc : list location) => alls x n ++ acc) nil
           ((e, (from_elements (List.map (fun x : location => (x, 1)) l))[e])
            :: (removeA (eqA:=eq_pair) pair_dec (e, (from_elements (List.map (fun x : location => (x, 1)) l))[e])
               (elements (from_elements (List.map (fun x : location => (x, 1)) l)))))).
  apply Hcompat; try reflexivity; [].
  apply NoDupA_equivlistA_PermutationA; autoclass.
  + eapply NoDupA_strengthen, elements_NoDupA. apply subrelation_pair_elt.
  + constructor.
    - rewrite removeA_InA; autoclass; []. intuition.
    - eapply removeA_NoDupA, NoDupA_strengthen, elements_NoDupA; autoclass.
  + intro x. split; intro Hin.
    - change (InA eq_pair x (elements (from_elements (List.map (fun x : location => (x, 1)) l)))) in Hin.
      destruct (fst x =?= e) as [Heq | Heq].
      -- rewrite elements_spec in Hin. rewrite Heq in *. left. destruct x. simpl in *. intuition.
      -- right. rewrite removeA_InA; autoclass; [].
         split; trivial; [].
         intros [? _]. now apply Heq.
    - inv Hin.
      -- revert_one @equiv. intro Hx. rewrite Hx.
         change (InA eq_pair (e, (from_elements (List.map (fun y => (y, 1)) l))[e])
                             (elements (from_elements (List.map (fun y => (y, 1)) l)))).
         rewrite elements_spec; simpl.
         split; trivial; []. apply neq_0_lt. auto.
      -- revert_all.
         rewrite removeA_InA; autoclass. tauto.
Qed.

(** [Always_invalid e] means that (infinite) execution [e] is [invalid]
    forever. We will prove that with [bad_demon], robots are always apart. *)
Definition Always_invalid (e : execution) := Stream.forever (Stream.instant WithMultiplicity.invalid) e.

Instance Always_invalid_compat : Proper (equiv ==> iff) Always_invalid.
Proof using . apply Stream.forever_compat, Stream.instant_compat. apply WithMultiplicity.invalid_compat. Qed.

(** **  Linking the different properties  **)

Theorem different_no_gathering : forall (e : execution),
  Always_invalid e -> ~WillGather e.
Proof using even_nG nG_non_0.
intros e He Habs. induction Habs as [e Habs | e].
+ destruct Habs as [pt [Hnow Hlater]]. destruct He as [Hinvalid He].
  destruct Hinvalid as [_ [_ [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]]].
  apply Hdiff. transitivity pt.
  - assert (Hin : In pt1 (!! (Stream.hd e))).
    { unfold In. setoid_rewrite Hin1. now apply half_size_config. }
    rewrite obs_from_config_In in Hin.
    destruct Hin as [id Hin]. rewrite <- Hin.
    apply (no_byz id). intro g. now unfold gathered_at in Hnow; specialize (Hnow g).
  - assert (Hin : In pt2 (!! (Stream.hd e))).
    { unfold In. setoid_rewrite Hin2. now apply half_size_config. }
    rewrite obs_from_config_In in Hin.
    destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. apply (no_byz id). intro g. apply Hnow.
+ inversion He. now apply IHHabs.
Qed.

Hint Resolve half_size_config : core.

(** As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_config {A} (config : G -> A) : ident -> A := fun id =>
  match id with
    | Good g => config g
    | Byz b => ltac:(exfalso; now apply (Nat.nlt_0_r (proj1_sig b)), proj2_sig)
  end.

Local Opaque G B.

(** We define a particular robot [g0] that will help us distinguish two towers:
    the first one will be the one that [g0] belongs to.
    The actual value of g0 is irrelevant so we make its body opaque.  *)
Definition g0 : G.
Proof using nG_non_0. exists 0. generalize nG_non_0. intro. omega. Qed.

(** *  Proof of the impossiblity of gathering  **)

(** From now on and until the final theorem we assume given a robogram [r]. *)

Variable r : robogram.
Open Scope R_scope.

(* A demon that makes the robogram fail on any invalid configuration:
   - if robots go on the position of the other one (symmetrical by definition of robogram),
     activate both and they swap positions;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

Definition observation0 : observation := add origin (Nat.div2 nG) (singleton one (Nat.div2 nG)).
Arguments observation0 : simpl never.

Theorem invalid_obs : forall config, WithMultiplicity.invalid config -> forall g,
  { sim : similarity location | !! config == map sim observation0 & sim origin == get_location (config (Good g)) }.
Proof.
intros config Hconfig g.
destruct (WithMultiplicity.invalid_strengthen (reflexivity _) Hconfig) as [pt1 [pt2 Hdiff Hobs]].
destruct (get_location (config (Good g)) =?= pt1) as [Heq1 | Heq1].
+ (* we map origin to pt1 and unit to pt2 *)
  exists (build_similarity (symmetry non_trivial) Hdiff).
  - unfold observation0.
    rewrite Hobs, map_add, map_singleton,
            build_similarity_eq1, build_similarity_eq2; autoclass.
  - now rewrite build_similarity_eq1.
+ (* we map origin to pt2 and unit to pt1 *)
  symmetry in Hdiff.
  exists (build_similarity (symmetry non_trivial) Hdiff).
  - unfold observation0.
    rewrite Hobs, map_add, map_singleton, 
            build_similarity_eq1, build_similarity_eq2; autoclass; [].
    intro. rewrite 2 add_spec, 2 singleton_spec. do 2 destruct_match; simpl in *; omega.
  - rewrite build_similarity_eq1. symmetry.
    assert (Hin := pos_in_config config origin (Good g)).
    rewrite Hobs, add_In, In_singleton in Hin. hnf in Heq1. tauto.
Defined.

Definition proj1_sig2 {A : Type} {P Q : A -> Prop} (e : {x : A | P x & Q x}) := let (a, _, _) := e in a.

(* This proof is different that the one for R and requires invalid_obs to be transparent. *)
Lemma invalid_obs_compat : forall config1 config2 (H1 : WithMultiplicity.invalid config1) (H2 : WithMultiplicity.invalid config2),
  config1 == config2 ->
  forall g h, get_location (config1 (Good g)) == get_location (config2 (Good h)) ->
  proj1_sig2 (invalid_obs H1 g) == proj1_sig2 (invalid_obs H2 h).
Proof using build_similarity_compat even_nG.
intros config1 config2 H1 H2 Heq g h Hgh.
unfold invalid_obs.
destruct (WithMultiplicity.invalid_strengthen (reflexivity 0%nat) H1) as [pt1 [pt2 Hdiff Hobs]],
         (WithMultiplicity.invalid_strengthen (reflexivity 0%nat) H2) as [pt3 [pt4 Hdiff' Hobs']].
assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (pt3 :: pt4 :: nil)).
{ rewrite Heq, Hobs' in Hobs. apply support_compat in Hobs.
  revert Hobs. rewrite 2 support_add; auto; [].
  destruct (In_dec pt3 (singleton pt4 (Nat.div2 nG))) as [Habs |];
  [| destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Habs |]].
  - rewrite In_singleton in Habs. now elim Hdiff'.
  - rewrite In_singleton in Habs. now elim Hdiff.
  - rewrite 2 support_singleton; auto; []. now symmetry. }
repeat destruct_match; simpl; rewrite Hgh in *; intro.
+ assert (Heq1 : pt1 == pt3) by now transitivity (get_location (config2 (Good h))).
  rewrite Heq1 in Hperm. apply PermutationA_cons_inv in Hperm; autoclass; [].
  rewrite PermutationA_1 in Hperm; autoclass; [].
  now apply build_similarity_compat.
+ assert (Heqpt : pt1 == pt4 /\ pt2 == pt3).
  { rewrite PermutationA_2 in Hperm; autoclass; [].
    destruct Hperm as [[Heq1 Heq2] |?]; trivial; [].
    rewrite Heq1 in *. simpl complement in *. contradiction. }
  destruct Heqpt as [Heq1 Heq2].
  now apply build_similarity_compat.
+ assert (Heqpt : pt1 == pt4 /\ pt2 == pt3).
  { rewrite PermutationA_2 in Hperm; autoclass; [].
    destruct Hperm as [[Heq1 Heq2] |?]; trivial; [].
    rewrite Heq1 in *. simpl complement in *. contradiction. }
  destruct Heqpt as [Heq1 Heq2].
  now apply build_similarity_compat.
+ assert (Heq2 : pt2 == pt4).
  { transitivity (get_location (config2 (Good h))).
    - assert (Hin := pos_in_config config1 origin (Good h)).
      rewrite Hobs, Heq, add_In, In_singleton in Hin.
      simpl complement in *. symmetry. tauto.
    - assert (Hin := pos_in_config config2 origin (Good h)).
      rewrite Hobs', add_In, In_singleton in Hin.
      simpl complement in *. tauto. }
  rewrite Heq2 in Hperm. setoid_rewrite permA_swap in Hperm.
  apply PermutationA_cons_inv in Hperm; autoclass; [].
  rewrite PermutationA_1 in Hperm; autoclass; [].
  now apply build_similarity_compat.
Qed.

Global Opaque invalid_obs.

Theorem invalid_reverse : forall (sim : similarity location) config,
  !! config == map sim observation0 -> WithMultiplicity.invalid config.
Proof using even_nG nG_non_0.
intros sim config Hsim.
assert (Hcardinal := cardinal_obs_from_config config origin).
assert (Heven : Nat.Even nG).
{ rewrite <- Nat.even_spec.
  cut (Nat.odd nG = false).
  + unfold Nat.odd. now rewrite Bool.negb_false_iff.
  + apply Bool.not_true_is_false. intro Hodd.
    rewrite Hsim, map_cardinal in Hcardinal; autoclass; [].
    unfold observation0 in Hcardinal. rewrite cardinal_add, cardinal_singleton in Hcardinal.
    rewrite (Nat.div2_odd nG) in Hcardinal at 3. rewrite Hodd in *. simpl in *. omega. }
repeat split; trivial; [|].
+ rewrite <- Nat.even_spec in Heven.
  assert (HnG := nG_non_0). simpl nG in *.
  destruct n as [| [| ?]]; simpl; discriminate || omega || now elim HnG.
+ exists (sim origin), (sim one).
  repeat split.
  - intro Heq. apply Similarity.injective in Heq. symmetry in Heq. revert Heq. apply non_trivial.
  - rewrite Hsim, map_injective_spec; autoclass; try apply Similarity.injective; [].
    unfold observation0. rewrite add_same, singleton_other; try omega; [].
    symmetry. apply non_trivial.
  - rewrite Hsim, map_injective_spec; autoclass; try apply Similarity.injective; [].
    unfold observation0. rewrite add_other, singleton_same; try omega; [].
    apply non_trivial.
Qed.

(** The movement of robots in the reference configuration. *)
Definition move := get_location (r observation0).

(** The key idea is to prove that we can always make robots see the same observation in any invalid configuration.
    If they do not gather in one step, then they will never do so.

    So, in [config1], if the robot move to [one], we activate all robots and they swap locations.
    If it does not, we activate only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move == one.

Definition change_frame1 config (g : G) :=
  match invalid_dec config with
    | Specif.left  H => inverse (proj1_sig2 (invalid_obs H g))
    | Specif.right H => Similarity.id (* this second case will never be used *)
  end.

Instance change_frame1_compat : Proper (equiv ==> Logic.eq ==> equiv) change_frame1.
Proof using build_similarity_compat even_nG.
unfold change_frame1. intros config1 config2 Heq gg g ?. subst gg.
destruct (invalid_dec config1) as [H1 | ?],
         (invalid_dec config2) as [H2 | ?];
  try reflexivity || (apply WithMultiplicity.invalid_compat in Heq; tauto); [].
apply inverse_compat, invalid_obs_compat; trivial; now rewrite Heq.
Qed.

(** A demon swapping both towers *)
Definition da1 : demonic_action := {|
  activate := fun _ => true;
  relocate_byz := fun _ b => mk_info origin;
  change_frame := change_frame1;
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt;
  
  precondition_satisfied := fun _ _ => I;
  precondition_satisfied_inv := fun _ _ => I;
  
  activate_compat := ltac:(now repeat intro);
  relocate_byz_compat := ltac:(now repeat intro; f_equiv);
  change_frame_compat := change_frame1_compat;
  choose_update_compat := ltac:(now repeat intro);
  choose_inactive_compat := ltac:(now repeat intro) |}.

Definition bad_demon1 : demon := Stream.constant da1.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof using . coinduction bad_fair1. intros id1 id2. now constructor. Qed.

(* It is a more restricted version where we assume that the starting configuration is invalid. *)
Lemma round_simplify1 : forall config pt1 pt2,
  pt1 =/= pt2 ->
  !! config == add pt1 (Nat.div2 nG) (singleton pt2 (Nat.div2 nG)) ->
  round r da1 config == fun id => match id with
                          | Good g => mk_info (if get_location (config (Good g)) =?= pt1 then pt2 else pt1)
                          | Byz b => mk_info origin
                        end.
Proof using Hmove.
intros config pt1 pt2 Hdiff Hobs.
assert (Hcase : forall id, get_location (config id) == pt1 \/ get_location (config id) == pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hobs, add_In, In_singleton in Hin. subst. tauto. }
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
unfold round. cbn -[equiv equiv_dec get_location map_config lift].
rewrite get_location_lift. unfold map_config at 2. cbn [projT1]. simpl get_location at 2. unfold id.
rewrite <- obs_from_config_map, obs_from_config_ignore_snd; autoclass; [].
unfold change_frame1.
destruct (invalid_dec config) as [Hvalid | Hvalid].
* (* invalid configuration *)
  destruct (invalid_obs Hvalid g) as [sim Hobs1 Horigin1].
  simpl proj1_sig2.
  rewrite Hobs1, map_merge; autoclass; [].
  rewrite map_extensionality_compat, map_id; autoclass; try apply Similarity.compose_inverse_l; [].
  rewrite Hmove.
  assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (sim origin :: sim one :: nil)).
  { apply support_compat in Hobs1. revert Hobs1.
    rewrite Hobs. unfold observation0.
    rewrite map_add, map_singleton; autoclass; [].
    rewrite 2 support_add; auto; [].
    destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Hin | Hin],
             (In_dec (sim origin) (singleton (sim one) (Nat.div2 nG))) as [Hin' | Hin'];
    rewrite In_singleton in Hin, Hin';
    try solve [ simpl in *; tauto ]; [|].
    - destruct Hin' as [Hin' _]. apply Similarity.injective in Hin'.
      symmetry in Hin'. elim (non_trivial Hin').
    - rewrite 2 support_singleton; auto. }
  rewrite PermutationA_2 in Hperm; autoclass; [].
  destruct_match.
  + assert (Hpt1 : sim origin == pt1) by (etransitivity; eauto).
    assert (Hpt2 : sim one == pt2).
    { decompose [and or] Hperm; auto; []. rewrite Hpt1 in *. now elim Hdiff. }
    now rewrite <- Hpt2.
  + assert (Hpt2 : sim origin == pt2).
    { destruct (Hcase (Good g)); try contradiction; []. etransitivity; eauto. }
    assert (Hpt1 : sim one == pt1).
    { decompose [and or] Hperm; auto; []. rewrite Hpt2 in *. now elim Hdiff. }
    now rewrite <- Hpt1.
* elim Hvalid.
  apply (invalid_reverse (build_similarity non_trivial Hdiff)).
  rewrite Hobs. unfold observation0.
  rewrite map_add, map_singleton, build_similarity_eq1, build_similarity_eq2; autoclass; [].
  apply add_singleton_comm.
Qed.

Lemma invalid_da1_next : forall config, WithMultiplicity.invalid config -> WithMultiplicity.invalid (round r da1 config).
Proof using Hmove.
intros config Hvalid.
destruct (WithMultiplicity.invalid_strengthen (reflexivity _) Hvalid) as [pt1 [pt2 Hdiff Hobs]].
(* As [config] is invalid, all robots are only on two locations. *)
assert (Hcase : forall id, get_location (config id) == pt1 \/ get_location (config id) == pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hobs, add_In, In_singleton in Hin. subst. tauto. }
(* We build the similarity that performs the swap. *)
assert (Hdiff' : pt2 =/= pt1) by now symmetry.
pose (sim := build_similarity Hdiff Hdiff' : similarity location).
assert (Hconfig : round r da1 config == map_config (lift (existT precondition sim I)) config).
{ rewrite (round_simplify1 config Hdiff Hobs).
  apply no_byz_eq. intro g.
  cbn [map_config]. rewrite get_location_lift, mk_info_get_location.
  destruct (get_location (config (Good g)) =?= pt1) as [Hg | Hg];
  destruct (Hcase (Good g)) as [Hg' | Hg']; rewrite Hg' in *;
  solve [ symmetry; apply build_similarity_eq1
        | symmetry; apply build_similarity_eq2
        |  auto; now elim Hg ]. }
(* Let us pick an arbitrary robot (here [g0]) and consider a similarity [sim1]
   that maps [!! config] to [observation0] and such that [sim1 g0 = origin]. *)
destruct (invalid_obs Hvalid g0) as [sim1 Hsim1 ?].
apply (invalid_reverse (sim ∘ sim1)).
rewrite Hconfig.
rewrite <- obs_from_config_ignore_snd, <- obs_from_config_map, Hsim1, map_merge; autoclass.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_invalid1 : forall config, WithMultiplicity.invalid config ->
  Always_invalid (execute r bad_demon1 config).
Proof using Hmove.
coinduction differs.
+ now simpl.
+ cbn. now apply invalid_da1_next.
Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time  **)

(* TODO: clean the proofs in this case, there are way to complicated
         (in particular the lemmas and uses of change_frame2) *)
Section MoveNot1.

Hypothesis Hmove : move =/= one.

(** A function that return different results depending on which tower the robot is.
    Both results are parametrized by the ordered locations of the towers.
    The first function argument is the one for the tower where [g0] is. *)
Definition select_tower {A} (b_g0 b : forall pt1 pt2 : location, pt1 =/= pt2 -> A)
                            (default : A) (config : configuration) (id : ident) :=
  match invalid_dec config with
    | Specif.left  H =>
        match WithMultiplicity.invalid_strengthen (reflexivity _) H with
        | existT _ pt1 (exist2 _ _ pt2 Hdiff Hobs) =>
          if get_location (config (Good g0)) =?= pt1
          then if get_location (config id) =?= get_location (config (Good g0))
               then b_g0 pt1 pt2 Hdiff
               else b pt1 pt2 Hdiff
          else if get_location (config id) =?= get_location (config (Good g0))
               then b_g0 pt2 pt1 (symmetry Hdiff)
               else b pt2 pt1 (symmetry Hdiff)
        end
    | Specif.right H => default (* this second case will never be used *)
  end.

Instance select_tower_compat : forall A (eqA : relation A) b_g0 b,
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> eqA (b_g0 pt1 pt2 Hdiff) (b_g0 pt1' pt2' Hdiff')) ->
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> eqA (b pt1 pt2 Hdiff) (b pt1' pt2' Hdiff')) ->
  Proper (eqA ==> @equiv configuration _ ==> eq ==> eqA) (select_tower b_g0 b).
Proof using even_nG.
intros A eqA b_g0 b Hb_g0 Hb default1 default2 Hdefault config1 config2 Hconfig gg g ?. subst gg.
unfold select_tower.
destruct (invalid_dec config1) as [Hvalid1 | Hvalid1],
         (invalid_dec config2) as [Hvalid2 | Hvalid2];
try (exfalso; revert Hvalid1 Hvalid2; rewrite Hconfig; tauto); trivial; [].
change 0%nat with nB.
destruct (WithMultiplicity.invalid_strengthen (reflexivity nB) Hvalid1) as [pt1  [pt2  Hdiff  Hobs ]],
         (WithMultiplicity.invalid_strengthen (reflexivity nB) Hvalid2) as [pt1' [pt2' Hdiff' Hobs']].
assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (pt1' :: pt2' :: nil)).
{ apply support_compat in Hobs'. revert Hobs'.
  rewrite <- Hconfig, Hobs.
  rewrite 2 support_add; auto; [].
  destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Hin |];
  try (rewrite In_singleton in Hin; destruct Hin as [Hin _]; contradiction); [].
  destruct (In_dec pt1' (singleton pt2' (Nat.div2 nG))) as [Hin |];
  try (rewrite In_singleton in Hin; destruct Hin as [Hin _]; contradiction); [].
  rewrite 2 support_singleton; auto. }
apply PermutationA_2 in Hperm; autoclass; [].
assert (Hcase1 : forall id, get_location (config1 id) == pt1 \/ get_location (config1 id) == pt2).
{ intro id. assert (Hin := pos_in_config config1 origin id).
  rewrite Hobs, add_In, In_singleton in Hin. tauto. }
assert (Hcase2 : forall id, get_location (config2 id) == pt1' \/ get_location (config2 id) == pt2').
{ intro id. assert (Hin := pos_in_config config2 origin id).
  rewrite Hobs', add_In, In_singleton in Hin. tauto. }
clear Hobs Hobs' Hvalid1 Hvalid2.
Time repeat destruct_match; rewrite Hconfig in *; try (first [ assert (Heq : pt1 == pt1' /\ pt2 == pt2')
               by (destruct Hperm as [? | [Heq1 Heq2]]; trivial; [];
                   rewrite Heq1, Heq2 in *;
                   split; transitivity (get_location (config2 (Good g0))); auto)
           | assert (Heq : pt1 == pt2' /\ pt2 == pt1')
               by (destruct Hperm as [[Heq1 Heq2] | ?]; trivial; [];
                   rewrite Heq1, Heq2 in *;
                   split; transitivity (get_location (config2 (Good g0))); auto) ];
     destruct Heq as [Heq1 Heq2]; rewrite Heq1, Heq2 in *;
     (now apply Hb_g0) || (now apply Hb) || contradiction); [|].
- assert (Heq : pt1 == pt1' /\ pt2 == pt2').
  { destruct Hperm as [? | [Heq1 Heq2]]; trivial; [].
    destruct (Hcase2 (Good g0)); rewrite Heq1 in *; contradiction. }
  now apply Hb_g0.
- assert (Heq : pt1 == pt1' /\ pt2 == pt2').
  { destruct Hperm as [? | [Heq1 Heq2]]; trivial; [].
    destruct (Hcase2 (Good g0)); rewrite Heq1 in *; contradiction. }
  now apply Hb.
Qed.

(** General properties about [select_tower] *)
Lemma select_tower_case_1 : forall {A} `{Setoid A} b1 b2 (d : A) config id,
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> b1 pt1 pt2 Hdiff == b1 pt1' pt2' Hdiff') ->
  WithMultiplicity.invalid config ->
  get_location (config id) == get_location (config (Good g0)) ->
  exists pt Hdiff, select_tower b1 b2 d config id == b1 (get_location (config (Good g0))) pt Hdiff
                /\ In pt (!! config).
Proof using even_nG.
intros A ? b1 b2 d config id Hb1 ? Hcase.
unfold select_tower.
destruct (invalid_dec config) as [Hvalid | Hvalid].
* destruct (WithMultiplicity.invalid_strengthen (reflexivity 0%nat) Hvalid) as [pt1 [pt2 Hdiff Hobs]].
  repeat destruct_match; try contradiction; [|].
  + assert (Hdiff' : get_location (config (Good g0)) =/= pt2).
    { intro. apply Hdiff. now transitivity (get_location (config (Good g0))). }
    exists pt2, Hdiff'. split.
    - now apply Hb1.
    - rewrite Hobs, add_In, In_singleton. auto.
  + assert (Heq : get_location (config (Good g0)) == pt2).
    { assert (Hin := pos_in_config config origin (Good g0)).
      rewrite Hobs in Hin. rewrite add_In, In_singleton in Hin.
      destruct Hin as [[] | []]; trivial. contradiction. }
    revert_one @complement. intro Hdiff'.
    exists pt1, Hdiff'. split.
    - now apply Hb1.
    - rewrite Hobs, add_In, In_singleton. auto.
* contradiction.
Qed.

(* NB: If we have unicity of inquality proof, we can replace Hdiff with the assumption. *)
Lemma select_tower_case_2 : forall {A} `{Setoid A} b1 b2 (d : A) config id,
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> b2 pt1 pt2 Hdiff == b2 pt1' pt2' Hdiff') ->
  WithMultiplicity.invalid config ->
  get_location (config id) =/= get_location (config (Good g0)) ->
  exists Hdiff,
    select_tower b1 b2 d config id == b2 (get_location (config (Good g0))) (get_location (config id)) Hdiff.
Proof using .
intros A ? b1 b2 d config id Hb2 ? Hdiff.
unfold select_tower.
destruct (invalid_dec config) as [Hvalid | Hvalid].
+ destruct (WithMultiplicity.invalid_strengthen (reflexivity 0%nat) Hvalid) as [pt1 [pt2 Hdiff' Hobs']].
  assert (Hcase : get_location (config (Good g0)) == pt1 /\ get_location (config id) == pt2
               \/ get_location (config (Good g0)) == pt2 /\ get_location (config id) == pt1).
  { assert (Hin0 := pos_in_config config origin (Good g0)).
    assert (Hin := pos_in_config config origin id).
    rewrite Hobs', add_In,In_singleton in Hin0, Hin.
    destruct Hin as [[] | []], Hin0 as [[] | []]; 
    tauto || elim Hdiff; etransitivity; eauto. }
  exists (symmetry Hdiff).
  repeat destruct_match; simpl in *; destruct Hcase as [[] | []];
  unfold Datatypes.id in *;
  try solve [ congruence
        | now apply Hb2; auto
        | elim Hdiff'; transitivity (config (Good g0)); auto ].
+ contradiction.
Qed.

Lemma select_tower_default : forall {A} b1 b2 (d : A) config id,
  ~WithMultiplicity.invalid config -> select_tower b1 b2 d config id = d.
Proof using . intros A b1 b2 d config id Hvalid. unfold select_tower. destruct_match; tauto. Qed.

(** Using [select_tower], we define activation and change of frame. *)
Definition activate2 (b1 b2 : bool) := select_tower (fun _ _ _ => b1) (fun _ _ _ => b2) true.

Instance activate2_compat : forall b1 b2, Proper (equiv ==> eq ==> eq) (activate2 b1 b2).
Proof using even_nG. intros. unfold activate2. now apply select_tower_compat. Qed.

Lemma activate2_spec1 : forall b config id, WithMultiplicity.invalid config ->
  (activate2 b (negb b) config id = b <-> get_location (config id) == get_location (config (Good g0))).
Proof using Hmove even_nG.
intros b config id Hcase. unfold activate2.
destruct (get_location (config id) =?= get_location (config (Good g0))) as [Hloc | Hloc].
+ destruct (select_tower_case_1 (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => b)
                                (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => negb b)
                                true id ltac:(reflexivity) Hcase Hloc) as [pt [Hdiff [Heq Hin]]].
  rewrite Heq. tauto.
+ destruct (select_tower_case_2 (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => b)
                                (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => negb b)
                                true id ltac:(reflexivity) Hcase Hloc) as [Hdiff Heq].
  rewrite Heq. assert (Habs := Bool.no_fixpoint_negb b). intuition.
Qed.

Lemma activate2_spec2 : forall b config id, WithMultiplicity.invalid config ->
  (activate2 b (negb b) config id = negb b <-> get_location (config id) =/= get_location (config (Good g0))).
Proof using Hmove even_nG.
intros b config id Hinvalid. unfold activate2.
destruct (get_location (config id) =?= get_location (config (Good g0))) as [Hcase | Hcase].
+ destruct (select_tower_case_1 (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => b)
                                (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => negb b)
                                true id ltac:(reflexivity) Hinvalid Hcase) as [pt [Hdiff [Heq Hin]]].
  rewrite Heq. assert (Habs := Bool.no_fixpoint_negb b). intuition.
+ destruct (select_tower_case_2 (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => b)
                                (fun (pt1 pt2 : location) (_ : pt1 =/= pt2) => negb b)
                                true id ltac:(reflexivity) Hinvalid Hcase) as [Hdiff Heq].
  rewrite Heq. tauto.
Qed.

(* [change_frame2] maps the configuration to the canonical one,
   that is, one tower on [origin] and one on [one]. *)
Definition change_frame2 (config : configuration) (g : G) : similarity location :=
  @select_tower (similarity location)
    (fun pt1 pt2 (Hdiff : pt1 =/= pt2) => build_similarity Hdiff (symmetry non_trivial))
    (fun pt1 pt2 (Hdiff : pt1 =/= pt2) => build_similarity Hdiff non_trivial)
    Similarity.id
    config
    (Good g).

Instance change_frame2_compat : Proper (equiv ==> eq ==> equiv) change_frame2.
Proof using build_similarity_compat even_nG.
intros config1 config2 Hconfig g1 g2 Hg. unfold change_frame2.
cut (Good g1 = Good g2); try congruence; [].
generalize (Good g1), (Good g2). revert config1 config2 Hconfig.
apply select_tower_compat; reflexivity || intros; now apply build_similarity_compat.
Qed.

Local Definition Hcompat1 :=
  fun pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2') Heq1 Heq2 =>
    build_similarity_compat Hdiff (symmetry non_trivial) Hdiff' (symmetry non_trivial)
                            Heq1 Heq2 (reflexivity _) (reflexivity _).

Local Definition Hcompat2 :=
  fun pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2') Heq1 Heq2 =>
    build_similarity_compat Hdiff non_trivial Hdiff' non_trivial
                            Heq1 Heq2 (reflexivity _) (reflexivity _).

Lemma center_change_frame2 : forall config g, WithMultiplicity.invalid config ->
  Similarity.center (change_frame2 config g) == get_location (config (Good g)).
Proof using build_similarity_compat build_similarity_eq1 build_similarity_eq2 build_similarity_inverse even_nG.
intros config g Hinvalid. unfold change_frame2.
destruct (get_location (config (Good g)) =?= get_location (config (Good g0))) as [Hcase | Hcase].
+ destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                Similarity.id _ Hcompat1 Hinvalid Hcase) as [pt [Hdiff [Heq Hin]]].
  rewrite Heq. unfold Similarity.center.
  rewrite build_similarity_inverse. now rewrite build_similarity_eq1.
+ destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                Similarity.id _ Hcompat2 Hinvalid Hcase) as [Hdiff Heq].
  rewrite Heq. unfold Similarity.center.
  rewrite build_similarity_inverse. now rewrite build_similarity_eq2.
Qed.

Lemma change_frame2_eq : forall config g1 g2, WithMultiplicity.invalid config ->
  get_location (config (Good g1)) == get_location (config (Good g2)) <->
  change_frame2 config g1 == change_frame2 config g2.
Proof using build_similarity_compat build_similarity_eq1 build_similarity_eq2 build_similarity_inverse even_nG.
intros config g1 g2 Hinvalid. split; intro Hg1g2.
* unfold change_frame2.
  destruct (get_location (config (Good g1)) =?= get_location (config (Good g0))) as [Hcase | Hcase].
  + destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id _ Hcompat1 Hinvalid Hcase) as [pt [Hdiff [Heq Hin]]].
    rewrite Hg1g2 in Hcase.
    destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id _ Hcompat1 Hinvalid Hcase) as [pt' [Hdiff' [Heq' Hin']]].
    rewrite Heq, Heq'. apply Hcompat1; try reflexivity; [].
    apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := get_location (config (Good g0))));
    eauto using pos_in_config; now symmetry.
  + destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id _ Hcompat2 Hinvalid Hcase) as [Hdiff Heq].
    rewrite Hg1g2 in Hcase.
    destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id _ Hcompat2 Hinvalid Hcase) as [Hdiff' Heq'].
    rewrite Heq, Heq'. apply Hcompat2; auto.
* setoid_rewrite <- center_change_frame2; trivial; [].
  now rewrite Hg1g2.
Qed.

Lemma change_frame2_case : forall config g1, WithMultiplicity.invalid config ->
  get_location (config (Good g1)) =/= get_location (config (Good g0)) ->
  forall g, change_frame2 config g == change_frame2 config g0
         \/ change_frame2 config g == change_frame2 config g1.
Proof using build_similarity_compat even_nG.
intros config g1 Hinvalid Hneq g.
unfold change_frame2.
destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                              (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                              Similarity.id _ Hcompat1 Hinvalid (reflexivity _)) as [pt [Hdiff0 [Heq0 Hin]]].
destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                              (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                              Similarity.id _ Hcompat2 Hinvalid Hneq) as [Hdiff1 Heq1].
rewrite Heq0, Heq1.
destruct (get_location (config (Good g)) =?= get_location (config (Good g0))) as [Hg | Hg].
+ destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                Similarity.id _ Hcompat1 Hinvalid Hg) as [pt' [Hdiff' [Heq ?]]].
  left. rewrite Heq. apply build_similarity_compat; try reflexivity; [].
  apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := get_location (config (Good g0))));
  auto using pos_in_config; now symmetry.
+ destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                Similarity.id _ Hcompat2 Hinvalid Hg) as [Hdiff Heq].
  right. rewrite Heq. apply build_similarity_compat; try reflexivity; [].
  apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := get_location (config (Good g0))));
  auto using pos_in_config; now symmetry.
Qed.

Lemma change_frame2_obs : forall config g, WithMultiplicity.invalid config ->
  !! config == map (change_frame2 config g ⁻¹) observation0.
Proof using build_similarity_compat build_similarity_eq1 build_similarity_eq2 build_similarity_inverse even_nG.
intros config g Hinvalid.
pose (sim := change_frame2 config g). fold sim.
unfold observation0. rewrite map_add, map_singleton; autoclass; [].
assert (Hdiff_sim : sim⁻¹ origin =/= sim⁻¹ one).
{ intro Habs. apply Similarity.injective in Habs. now apply non_trivial. }
destruct (WithMultiplicity.invalid_strengthen (reflexivity _) Hinvalid) as [pt1 [pt2 Hdiff Hobs]].
assert (Hin0 : In (sim⁻¹ origin) (!! config)).
{ change (In (Similarity.center sim) (!! config)).
  unfold sim. rewrite center_change_frame2; auto using pos_in_config. }
assert (Hin1 : In (sim⁻¹ one) (!! config)).
{ unfold sim, change_frame2.
  destruct (get_location (config (Good g)) =?= get_location (config (Good g0))) as [Hcase | Hcase].
  - destruct (select_tower_case_1 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id (Good g) Hcompat1 Hinvalid Hcase)
      as [pt [Hpt [Heq Hin]]].
    now rewrite Heq, build_similarity_inverse, build_similarity_eq2.
  - destruct (select_tower_case_2 (fun pt1 pt2 Hdiff => build_similarity Hdiff (symmetry non_trivial))
                                  (fun pt1 pt2 Hdiff => build_similarity Hdiff non_trivial)
                                  Similarity.id (Good g) Hcompat2 Hinvalid Hcase)
      as [Hpt Heq].
    rewrite Heq, build_similarity_inverse, build_similarity_eq1.
    apply pos_in_config. }
intro pt. rewrite Hobs, 2 add_spec, 2 singleton_spec.
repeat destruct_match;
solve [ omega
      | elim Hdiff; transitivity pt; eauto
      | elim Hdiff_sim; transitivity pt; eauto
      | elim Hdiff_sim;
        apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := pt)); auto; try (now symmetry); [];
        rewrite Hobs, add_In, In_singleton; auto
      | rewrite Hobs, add_In, In_singleton in Hin0, Hin1;
        unfold complement in *;
        destruct Hin0 as [[Hin0 _] | [Hin0 _]], Hin1 as [[Hin1 _] | [Hin1 _]];
        rewrite <- Hin0, <- Hin1 in *; contradiction ].
Qed.

(** Definition of the alternating frame changes. *)
Definition da2_left config : demonic_action := {|
  activate := activate2 true false config;
  relocate_byz := fun _ _ => mk_info origin;
  change_frame := change_frame2;
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt;
  
  precondition_satisfied := fun _ _ => I;
  precondition_satisfied_inv := fun _ _ => I;
  
  activate_compat := activate2_compat _ _ (reflexivity _);
  relocate_byz_compat := ltac:(now repeat intro);
  change_frame_compat := change_frame2_compat;
  choose_update_compat := ltac:(now repeat intro);
  choose_inactive_compat := ltac:(now repeat intro) |}.

Definition da2_right config : demonic_action := {|
  activate := activate2 false true config;
  relocate_byz := fun _ _ => mk_info origin;
  change_frame := change_frame2;
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt;
  
  precondition_satisfied := fun _ _ => I;
  precondition_satisfied_inv := fun _ _ => I;
  
  activate_compat := ltac:(now repeat intro; subst);
  relocate_byz_compat := ltac:(now repeat intro);
  change_frame_compat := change_frame2_compat;
  choose_update_compat := ltac:(now repeat intro);
  choose_inactive_compat := ltac:(now repeat intro) |}.

Lemma round_simplify2_left : forall config,
  !! config == map ((change_frame2 config g0)⁻¹) observation0 ->
  round r (da2_left config) config
  == fun id => match id with
                 | Good g => mk_info (if get_location (config (Good g)) =?= (change_frame2 config g0)⁻¹ origin
                                      then (change_frame2 config g)⁻¹ move else get_location (config (Good g)))
                 | Byz b => mk_info origin
               end.
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hobs.
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
unfold round. cbn -[equiv equiv_dec get_location map_config lift inverse].
assert (Hinvalid := invalid_reverse _ _ Hobs).
assert (Hsim0 := center_change_frame2 g0 Hinvalid). unfold Similarity.center in Hsim0.
pose (sim := change_frame2 config g0). fold sim in Hsim0, Hobs.
destruct_match_eq Hcase.
* (* The robot is on the first tower so it moves like g0. *)
  rewrite activate2_spec1 in Hcase; trivial; [].
  assert (Hsim := proj1 (change_frame2_eq _ _ Hinvalid) Hcase).
  rewrite get_location_lift. cbn [projT1].
  assert (Hsimg : get_location (config (Good g)) == sim⁻¹ origin) by (etransitivity; eauto).
  destruct_match; try contradiction; [].
  f_equiv.
  change get_location with (@id location). unfold id.
  rewrite <- (obs_from_config_map (St := Info) (f := change_frame2 config g) _ I config).
  rewrite obs_from_config_ignore_snd, Hobs, map_merge; autoclass; [].
  rewrite (map_extensionality_compat (f := id)), map_id; autoclass; [].
  intro x. rewrite Hsim. fold sim. apply Similarity.compose_inverse_r.
* (* The robot is on the second tower so it does not move. *)
  rewrite activate2_spec2 in Hcase; trivial; [].
  fold sim.
  destruct_match; reflexivity || now elim Hcase; etransitivity; eauto.
Qed.

Lemma invalid_da2_left_next : forall config,
  WithMultiplicity.invalid config -> WithMultiplicity.invalid (round r (da2_left config) config).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hinvalid.
pose (sim := change_frame2 config g0).
assert (Hdiff_move : sim⁻¹ move =/= sim⁻¹ one).
{ intro Heq. now apply Similarity.injective in Heq. }
assert (Hobs := change_frame2_obs g0 Hinvalid). fold sim in Hobs.
(* sim' maps the canonical config to the next round one *)
pose (sim' := build_similarity (symmetry non_trivial) Hdiff_move).
apply (invalid_reverse sim').
assert (Hconfig : round r (da2_left config) config
                  == map_config (lift (existT precondition (sim' ∘ sim) I)) config).
{ rewrite round_simplify2_left; auto; [].
  apply no_byz_eq. intro g. fold sim.
  cbn [map_config]. rewrite mk_info_get_location, get_location_lift.
  destruct (get_location (config (Good g)) =?= sim⁻¹ origin) as [Heq | Heq].
  + rewrite Heq. cbn -[equiv sim']. rewrite Bijection.section_retraction.
    change ((sim ⁻¹) 0%VS) with (Similarity.center sim) in Heq. unfold sim in Heq.
    rewrite center_change_frame2, change_frame2_eq in Heq; trivial; [].
    rewrite Heq. unfold sim'. now rewrite build_similarity_eq1.
  + assert (Heq' : get_location (config (Good g)) == (sim ⁻¹) one).
    { apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := (sim ⁻¹) origin)).
      - apply pos_in_config.
      - rewrite Hobs. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
      - rewrite Hobs. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
      - assumption.
      - intro Habs. apply Similarity.injective in Habs. now apply non_trivial. }
    rewrite Heq'. cbn -[equiv sim']. rewrite Bijection.section_retraction.
    unfold sim'. now rewrite build_similarity_eq2. }
rewrite Hconfig.
rewrite obs_from_config_ignore_snd, <- obs_from_config_map, Hobs; [| now autoclass].
rewrite map_merge; autoclass; [].
apply map_extensionality_compat; autoclass; [].
intro. cbn -[equiv sim']. now rewrite Bijection.section_retraction.
Qed.

Lemma da2_left_injective : forall config, WithMultiplicity.invalid config -> forall id1 id2,
  get_location (round r (da2_left config) config id1) == get_location (round r (da2_left config) config id2)
  <-> get_location (config id1) == get_location (config id2).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hinvalid id1 id2.
pattern id2. apply no_byz. pattern id1. apply no_byz. clear id1 id2. intros g1 g2.
assert (Hobs := change_frame2_obs g0 Hinvalid).
pose (sim := change_frame2 config g0). fold sim in Hobs.
rewrite (round_simplify2_left config Hobs (Good g1)),
        (round_simplify2_left config Hobs (Good g2)).
rewrite 2 mk_info_get_location. fold sim.
do 2 destruct_match.
+ split; intro Heq.
  - etransitivity; eauto.
  - rewrite change_frame2_eq in Heq; trivial; []. now rewrite Heq.
+ revert_one equiv. intro Heq1. rewrite Heq1.
  change ((sim ⁻¹) 0%VS) with (Similarity.center sim) in Heq1.
  unfold sim in Heq1. rewrite center_change_frame2, change_frame2_eq in Heq1; trivial; [].
  assert (Heq2 : get_location (config (Good g2)) == (sim ⁻¹) one).
  { assert (Hin := pos_in_config config origin (Good g2)).
    rewrite Hobs in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    now destruct Hin as [[] | []]. }
  rewrite Heq2, Heq1. fold sim.
  split; intro Heq; apply Similarity.injective in Heq; contradiction || now elim non_trivial.
+ revert_one equiv. intro Heq2. rewrite Heq2.
  change ((sim ⁻¹) 0%VS) with (Similarity.center sim) in Heq2.
  unfold sim in Heq2. rewrite center_change_frame2, change_frame2_eq in Heq2; trivial; [].
  assert (Heq1 : get_location (config (Good g1)) == (sim ⁻¹) one).
  { assert (Hin := pos_in_config config origin (Good g1)).
    rewrite Hobs in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    now destruct Hin as [[] | []]. }
  rewrite Heq2, Heq1. fold sim.
  split; intro Heq; apply Similarity.injective in Heq; (now symmetry in Heq) || now elim non_trivial.
+ split; intro; solve [ etransitivity; eauto ].
Qed.

Lemma round_simplify2_right : forall config,
  !! config == map (change_frame2 config g0 ⁻¹) observation0 ->
  round r (da2_right config) config
  == fun id => match id with
                 | Good g => mk_info (if get_location (config (Good g)) =?= (change_frame2 config g0)⁻¹ origin
                                      then get_location (config (Good g)) else (change_frame2 config g)⁻¹ move)
                 | Byz b => mk_info 0%VS
               end.
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hobs.
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
pose (sim := change_frame2 config g0). fold sim in Hobs |- *.
unfold round. cbn -[equiv_dec get_location map_config lift inverse].
assert (Hinvalid := invalid_reverse _ _ Hobs).
destruct_match_eq Hcase.
* (* The robot is on the second tower. *)
  assert (Hsim0 : get_location (config (Good g)) == sim⁻¹ one).
  { assert (Hin := pos_in_config config origin (Good g)).
    rewrite Hobs in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    destruct Hin as [[] | []]; trivial; [].
    rewrite activate2_spec2 in Hcase; trivial; [].
    elim Hcase. etransitivity; eauto; []. now apply center_change_frame2. }
  rewrite (obs_from_config_ignore_snd origin).
  assert (Hobs' : observation0 == map (change_frame2 config g) (!! config)).
  { rewrite <- map_id. Time change id with (Bijection.section Similarity.id).
    rewrite <- (map_extensionality_compat _ _ (Similarity.compose_inverse_r (change_frame2 config g))).
    rewrite (change_frame2_obs g Hinvalid), map_merge; autoclass. }
  rewrite obs_from_config_ignore_snd, <- obs_from_config_map, <- Hobs'; autoclass; [].
  destruct_match; try reflexivity; [].
  fold move. rewrite Hsim0 in *. elim non_trivial. eapply Similarity.injective; eauto.
* (* The robot is on the first tower so it does not move. *)
  destruct_match; try reflexivity; [].
  exfalso. revert_one equiv. intro Heq.
  rewrite activate2_spec1 in Hcase; trivial; []. contradict Hcase.
  now rewrite <- (center_change_frame2 g0).
Qed.

Lemma invalid_da2_right_next : forall config,
  WithMultiplicity.invalid config -> WithMultiplicity.invalid (round r (da2_right config) config).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hinvalid.
pose (sim0 := change_frame2 config g0).
assert (Hobs0 := change_frame2_obs g0 Hinvalid). fold sim0 in Hobs0.
(* Let us name a robot g1 on the second tower (the one that g0 is not on) and use its frame change
   to build the similarity that maps the canonical configuration to the next one. *)
assert (Hin : In ((sim0 ⁻¹) one) (!! config)).
{ rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass. }
rewrite obs_from_config_In in Hin. destruct Hin as [[g1 | []] Hg1]; try omega; [].
pose (sim1 := change_frame2 config g1).
assert (Hdiff : get_location (config (Good g0)) =/= get_location (config (Good g1))).
{ rewrite Hg1, <- center_change_frame2; trivial; [].
  unfold Similarity.center. fold sim0. intro Habs.
  apply Similarity.injective in Habs. now apply non_trivial. }
assert (Hobs1 := change_frame2_obs g1 Hinvalid). fold sim1 in Hobs1.
assert (Hg0 : get_location (config (Good g0)) == (sim1 ⁻¹) one).
{ apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := (sim1 ⁻¹) 0%VS)).
  - apply pos_in_config.
  - rewrite Hobs1. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
  - rewrite Hobs1. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
  - change ((sim1 ⁻¹) 0%VS) with (Similarity.center sim1). unfold sim1. now rewrite center_change_frame2.
  - intro Habs. apply Similarity.injective in Habs. now apply non_trivial. }
assert (Hdiff_move0 : sim0⁻¹ move =/= sim0⁻¹ one).
{ intro Heq. now apply Similarity.injective in Heq. }
assert (Hdiff_move1 : sim1⁻¹ move =/= sim1⁻¹ one).
{ intro Heq. now apply Similarity.injective in Heq. }
(* sim' maps the canonical config to the next round one *)
pose (sim' := build_similarity non_trivial Hdiff_move1).
apply (invalid_reverse sim').
assert (Hconfig : round r (da2_right config) config
                  == map_config (lift (existT precondition (sim' ∘ sim0) I)) config).
{ rewrite round_simplify2_right; auto; [].
  apply no_byz_eq. intro g. fold sim0.
  cbn [map_config]. rewrite mk_info_get_location, get_location_lift.
  destruct (get_location (config (Good g)) =?= sim0⁻¹ origin) as [Heq | Heq].
  + rewrite Heq. cbn -[equiv sim']. rewrite Bijection.section_retraction.
    unfold sim'. now rewrite build_similarity_eq2, <- Hg0, <- center_change_frame2.
  + assert (Heq' : get_location (config (Good g)) == (sim0 ⁻¹) one).
    { apply (WithMultiplicity.invalid_same_location (reflexivity _) Hinvalid (pt3 := (sim0 ⁻¹) origin)).
      - apply pos_in_config.
      - rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
      - rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass.
      - assumption.
      - intro Habs. apply Similarity.injective in Habs. now apply non_trivial. }
    rewrite Heq'. cbn -[equiv sim']. rewrite Bijection.section_retraction.
    unfold sim'. rewrite build_similarity_eq1.
    rewrite <- Hg1, change_frame2_eq in Heq'; trivial; []. now rewrite Heq'. }
rewrite Hconfig.
rewrite obs_from_config_ignore_snd, <- obs_from_config_map, Hobs0; [| now autoclass].
rewrite map_merge; [| autoclass | autoclass]; [].
apply map_extensionality_compat; autoclass; [].
intro. cbn -[equiv sim']. now rewrite Bijection.section_retraction.
Qed.

Lemma da2_right_injective : forall config, WithMultiplicity.invalid config -> forall g1 g2,
  get_location (round r (da2_right config) config g1) == get_location (round r (da2_right config) config g2)
  <-> get_location (config g1) == get_location (config g2).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
intros config Hinvalid id1 id2.
pattern id2. apply no_byz. pattern id1. apply no_byz. clear id1 id2. intros g1 g2.
assert (Hobs0 := change_frame2_obs g0 Hinvalid).
pose (sim0 := change_frame2 config g0). fold sim0 in Hobs0.
rewrite (round_simplify2_right config Hobs0 (Good g1)),
        (round_simplify2_right config Hobs0 (Good g2)).
rewrite 2 mk_info_get_location.
(* Let us name a robot g3 on the second tower (the one that g0 is not on) and use its frame change
   to build the similarity that maps the canonical configuration to the next one. *)
assert (Hin : In ((sim0 ⁻¹) one) (!! config)).
{ rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass. }
rewrite obs_from_config_In in Hin. destruct Hin as [[g3 | []] Hg3]; try omega; [].
pose (sim1 := change_frame2 config g3).
assert (Hdiff : get_location (config (Good g0)) =/= get_location (config (Good g3))).
{ rewrite Hg3, <- center_change_frame2; trivial; [].
  unfold Similarity.center. fold sim0. intro Habs.
  apply Similarity.injective in Habs. now apply non_trivial. }
do 2 destruct_match.
+ reflexivity.
+ revert_one equiv. intro Heq1. rewrite Heq1.
  split; intro Heq.
  - destruct (change_frame2_case g3 Hinvalid (symmetry Hdiff) g2) as [Hcase | Hcase].
    * rewrite <- Hcase. now apply center_change_frame2.
    * change ((change_frame2 config g0 ⁻¹) 0%VS) with (Similarity.center (change_frame2 config g0)).
      rewrite center_change_frame2; trivial; [].
      assert (Habs : (sim0 ⁻¹) 0%VS == (sim1 ⁻¹) one).
      { assert (Hin : In ((sim0 ⁻¹) 0%VS) (!! config)).
        { rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass. }
        rewrite (change_frame2_obs g3 Hinvalid) in Hin. fold sim1 in Hin.
        unfold observation0 in Hin. rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass.
        decompose [and or] Hin; trivial; elim Hdiff; []. now rewrite <- 2 center_change_frame2. }
      rewrite Hcase in Heq. fold sim0 sim1 in Heq. rewrite Heq in Habs.
      apply Similarity.injective in Habs. contradiction.
  - symmetry in Heq. contradiction.
+ revert_one equiv. intro Heq2. rewrite Heq2.
  change ((change_frame2 config g0 ⁻¹) 0%VS) with (Similarity.center (change_frame2 config g0)) in Heq2.
  rewrite center_change_frame2, change_frame2_eq in Heq2; trivial; [].
  assert (Heq1 : get_location (config (Good g1)) == (sim0 ⁻¹) one).
  { assert (Hin := pos_in_config config origin (Good g1)).
    rewrite Hobs0 in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    now destruct Hin as [[] | []]. }
  rewrite Heq1.
  split; intro Heq; try (apply Similarity.injective in Heq; now elim non_trivial); [].
  destruct (change_frame2_case g3 Hinvalid (symmetry Hdiff) g1) as [Hcase | Hcase].
  * rewrite <- Hcase, <- Heq1. symmetry. now apply center_change_frame2.
  * change ((change_frame2 config g0 ⁻¹) 0%VS) with (Similarity.center (change_frame2 config g0)).
    rewrite center_change_frame2; trivial; [].
    assert (Habs : (sim0 ⁻¹) 0%VS == (sim1 ⁻¹) one).
    { assert (Hin : In ((sim0 ⁻¹) 0%VS) (!! config)).
      { rewrite Hobs0. unfold observation0. rewrite map_add, map_singleton, add_In, In_singleton; autoclass. }
      rewrite (change_frame2_obs g3 Hinvalid) in Hin. unfold observation0 in Hin.
      rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
      decompose [and or] Hin; trivial; elim Hdiff; []. now rewrite <- 2 center_change_frame2. }
      rewrite Hcase in Heq. fold sim0 sim1 in Heq. rewrite <- Heq in Habs.
      apply Similarity.injective in Habs. contradiction.
+ assert (Heq1 : get_location (config (Good g1)) == (sim0 ⁻¹) one).
  { assert (Hin := pos_in_config config origin (Good g1)).
    rewrite Hobs0 in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    now destruct Hin as [[] | []]. }
  assert (Heq2 : get_location (config (Good g2)) == (sim0 ⁻¹) one).
  { assert (Hin := pos_in_config config origin (Good g2)).
    rewrite Hobs0 in Hin. unfold observation0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    now destruct Hin as [[] | []]. }
  rewrite Heq1, Heq2.
  rewrite <- Heq2 in Heq1. rewrite change_frame2_eq in Heq1; trivial; [].
  rewrite Heq1. split; reflexivity.
Qed.

(** A demon alternatively activating the "left" and "right" towers. *)
CoFixpoint bad_demon2 config : demon :=
   Stream.cons (da2_left config)
  (Stream.cons (da2_right (round r (da2_left config) config))
               (bad_demon2 (round r (da2_right (round r (da2_left config) config))
                           (round r (da2_left config) config)))).

Theorem Always_invalid2 : forall config, WithMultiplicity.invalid config ->
  Always_invalid (execute r (bad_demon2 config) config).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
cofix differs. intros config Hconfig.
constructor; [| constructor]; cbn.
- (* Inital state *)
  assumption.
- (* State after one step *)
  now apply invalid_da2_left_next.
- (* State after two steps *)
  apply differs. now apply invalid_da2_right_next, invalid_da2_left_next.
Qed.

Theorem kFair_bad_demon2 : forall config, WithMultiplicity.invalid config -> kFair 1 (bad_demon2 config).
Proof using Hmove build_similarity_eq1 build_similarity_eq2 build_similarity_inverse.
cofix fair_demon. intros config Hconfig.
constructor; [| constructor].
* clear fair_demon.
  intros id1 id2. apply (no_byz id2), (no_byz id1). clear id1 id2. intros g1 g2.
  rewrite (Stream.stream_eq (bad_demon2 config)).
  simpl Stream.hd.
  destruct (invalid_dec config) as [Hvalid | Hvalid].
  + assert (Hvalid' := invalid_da2_left_next Hvalid).
    destruct (get_location (config (Good g1)) =?= get_location (config (Good g0))) as [Htower | Htower];
    [| destruct (get_location (config (Good g2)) =?= get_location (config (Good g0))) as [Htower' | Htower']].
    - constructor 1. simpl. unfold activate2, select_tower.
      repeat destruct_match; trivial; contradiction.
    - constructor 2; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_2 (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g1) ltac:(reflexivity) Hvalid')
           as [Hdiff Hactivate]; trivial; [].
         hnf. now rewrite da2_left_injective.
    - constructor 3; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_2 (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g1) ltac:(reflexivity) Hvalid')
           as [Hdiff Hactivate]; trivial; [].
         hnf. now rewrite da2_left_injective.
  + constructor 1. simpl.
    unfold activate2. now apply select_tower_default.
* clear fair_demon.
  intros id1 id2. apply (no_byz id2), (no_byz id1). clear id1 id2. intros g1 g2.
  rewrite (Stream.stream_eq (bad_demon2 config)).
  simpl Stream.tl.
  pose (config':= round r (da2_left config) config).
  change (Between (Good g1) (Good g2)
                  (Stream.cons (da2_right config') (bad_demon2 (round r (da2_right config') config'))) 1).
  destruct (invalid_dec config') as [Hvalid | Hvalid].
  + assert (Hvalid' := invalid_da2_right_next Hvalid).
    destruct (get_location (config' (Good g1)) =?= get_location (config' (Good g0))) as [Htower | Htower];
    [destruct (get_location (config' (Good g2)) =?= get_location (config' (Good g0))) as [Htower' | Htower'] |].
    - constructor 3; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_1 (fun pt1 pt2 (_ : pt1 =/= pt2) => true)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => false) true (Good g1) ltac:(reflexivity) Hvalid')
           as [pt [Hdiff [Hactivate Hpt]]]; trivial; [].
         now rewrite da2_right_injective.
    - constructor 2; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_1 (fun pt1 pt2 (_ : pt1 =/= pt2) => true)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => false) true (Good g1) ltac:(reflexivity) Hvalid')
           as [pt [Hdiff [Hactivate Hpt]]]; trivial; [].
         now rewrite da2_right_injective.
    - constructor 1. simpl. unfold activate2, select_tower.
      repeat destruct_match; trivial; contradiction.
  + constructor 1. simpl.
    unfold activate2. now apply select_tower_default.
* apply fair_demon.
  now apply invalid_da2_right_next, invalid_da2_left_next.
Qed.

End MoveNot1.

(** **  Merging both cases  **)

Definition bad_demon : configuration -> demon.
Proof.
destruct (move =?= one) as [Hmove | Hmove].
- (** Robots exchange positions **)
  exact (fun _ => bad_demon1).
- (** Robots do not exchange positions **)
  exact bad_demon2.
Defined.

Theorem kFair_bad_demon : forall config, WithMultiplicity.invalid config -> kFair 1 (bad_demon config).
Proof using build_similarity_inverse.
intros. unfold bad_demon.
destruct (move =?= one).
- apply kFair_mono with 0%nat. exact kFair_bad_demon1. omega.
- now apply kFair_bad_demon2.
Qed.

Theorem kFair_bad_demon' : forall k config, (k>=1)%nat -> WithMultiplicity.invalid config -> kFair k (bad_demon config).
Proof using build_similarity_inverse.
intros.
eapply kFair_mono with 1%nat.
- apply kFair_bad_demon; auto.
- auto.
Qed.

(** * Final theorem

Given a non empty finite even set [G] and a robogram [r] on ([G]) × ∅,
for any invalid (bivalent) configuration, we can build a 1-fair demon
against which [r] does not solve the gathering problem. *)
Theorem noGathering :
  forall k, (1<=k)%nat ->
  forall config, WithMultiplicity.invalid config ->
  exists d, kFair k d
         /\ ~WillGather (execute r d config).
Proof using build_similarity_compat build_similarity_eq1 build_similarity_eq2 build_similarity_inverse even_nG nG_non_0.
intros k Hk config Hvalid. exists (bad_demon config).
split.
+ now apply kFair_bad_demon'.
+ apply different_no_gathering.
  unfold bad_demon.
  destruct (move =?= one) as [Hmove | Hmove].
  - now apply Always_invalid1.
  - now apply Always_invalid2.
Qed.

(** We can weaken the previous result to only proving that the demon is fair.
    This way, the statement is exactly complementary to the algorithm in InR2/Algorithm.v *)
Theorem noGathering_Fair :
  forall config, WithMultiplicity.invalid config ->
  exists d, Fair d /\ ~WillGather (execute r d config).
Proof using build_similarity_compat build_similarity_eq1 build_similarity_eq2 build_similarity_inverse even_nG nG_non_0.
intros config Hvalid.
destruct (noGathering ltac:(reflexivity) Hvalid) as [d [Hfair HnotGather]].
exists d. split; trivial; [].
eauto using kFair_Fair.
Qed.

End ImpossibilityProof.

Print Assumptions noGathering.
