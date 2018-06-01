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
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Gathering.WithMultiplicity.
Set Implicit Arguments.
Close Scope R_scope.
Import Datatypes. (* To recover Datatypes.id *)


Section ImpossibilityProof.

(** There are n good robots and no byzantine ones. *)
Parameter n : nat.
(** We assume that the number of robots is even and non-null. *)
Axiom even_nG : Nat.Even n.
Axiom nG_non_0 : n <> 0.

Instance MyRobots : Names := Robots n 0.
Local Transparent G B.

(** The setting is an arbitrary metric space over R. *)
Context {Loc : Location}.
Context {loc_RMS : RealMetricSpace location}.
(** It should be a normed space on top of that. *)
Hypothesis translation_hypothesis :
  forall v x y : location, dist (RealMetricSpace.add x v) (RealMetricSpace.add y v) = dist x y.
Hypothesis homothecy_hypothesis :
  forall (ρ : R) (x y : location), dist (mul ρ x) (mul ρ y) = (Rabs ρ * dist x y)%R.
Notation build_similarity := (Similarity.build_similarity translation_hypothesis homothecy_hypothesis).

(* We are in a rigid formalism with no other info than the location, so the demon makes no choice. *)
Instance Choice : update_choice Datatypes.unit := NoChoice.
Instance UpdFun : update_function Datatypes.unit := {
  update := fun _ _ trajectory _ => trajectory ratio_1;
  update_compat := ltac:(now repeat intro) }.

(* Trying to avoid notation problem with implicit arguments *)
Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation spect_from_config := (@spect_from_config _ _ _ _ multiset_spectrum).
Notation "!! config" := (spect_from_config config origin) (at level 10).

Implicit Type config : configuration.
Implicit Type da : demonic_action.

(* The robot trajectories are straight paths. *)
Definition path_loc := path location.
Definition paths_in_loc : location -> path_loc := local_straight_path.
Coercion paths_in_loc : location >-> path_loc.


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
Definition spect_from_config_spec : forall config (pt : location),
  (!! config)[pt] = countA_occ _ equiv_dec pt (List.map get_location (config_list config))
  := spect_from_config_spec.

Lemma no_byz : forall (id : ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. omega.
Qed.

Lemma no_byz_eq : forall config1 config2,
  (forall g, get_location (config1 (Good g)) == get_location (config2 (Good g))) -> config1 == config2.
Proof. intros config1 config2 Heq id. apply (no_byz id), Heq. Qed.

Definition mk_info : location -> location := id.
Lemma mk_info_get_location : forall pt, get_location (mk_info pt) == pt.
Proof. reflexivity. Qed.
(* 
(** We only assume that we know how to build a state from a position and this is compatible with [get_location]. *)
Variable mk_info : R -> info.
Hypothesis mk_info_get_location : forall pt, get_location (mk_info pt) == pt.
Instance mk_info_compat : Proper (equiv ==> equiv) mk_info.
Proof. simpl. repeat intro. now subst. Qed.
*)

(* To avoid passing the [nB = 0] argument each time. *)
Definition invalid_dec := invalid_dec (reflexivity nB).

(** From [elements], we can rebuild the [config_list]. *)
Lemma spect_makes_config_list : forall config : configuration,
  PermutationA equiv (List.map get_location (config_list config))
                     (List.fold_right (fun '(x, n) acc => alls x n ++ acc) nil (elements (!! config))).
Proof.
intro config.
unfold spect_from_config. cbn -[get_location config_list elements equiv location].
unfold make_multiset.
induction (List.map get_location (config_list config)) as [| e l]; try reflexivity; [].
(* maybe only the second arg is useful *)
assert (Hcompat : Proper (PermutationA equiv ==> PermutationA equiv ==> PermutationA equiv)
                         (fold_right (fun '(x, n) (acc : list location) => alls x n ++ acc))).
{ clear IHl l. intros l1 l1' Hl1 l2 l2' Hl2.
  revert l1 l1' Hl1. pattern l2, l2'.
  apply PermutationA_ind_bis with equiv; autoclass.
  + intros [] [] ? ? [Hl Hn] Hperm Hrec ? ? ?. simpl in *. subst.
    rewrite Hl at 1. now rewrite Hrec.
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
* (* [e] is not present in the spectrum *)
  rewrite Heq. cbn [alls app].
  rewrite Preliminary.removeA_out; try reflexivity; []. (* TODO: put it also in Util/Preliminary *)
  rewrite elements_spec. simpl. intuition.
* (* [e] does appear in the spectrum *)
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
Definition Always_invalid (e : execution) := Stream.forever (Stream.instant invalid) e.

Instance Always_invalid_compat : Proper (equiv ==> iff) Always_invalid.
Proof. apply Stream.forever_compat, Stream.instant_compat. apply invalid_compat. Qed.

(** **  Linking the different properties  **)
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
    rewrite spect_from_config_In in Hin.
    destruct Hin as [id Hin]. rewrite <- Hin.
    apply (no_byz id). intro g. now unfold gathered_at in Hnow; specialize (Hnow g).
  - assert (Hin : In pt2 (!! (Stream.hd e))).
    { unfold In. rewrite Hin2. now apply half_size_config. }
    rewrite spect_from_config_In in Hin.
    destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. apply (no_byz id). intro g. apply Hnow.
+ inversion He. now apply IHHabs.
Qed.

Hint Resolve half_size_config.

(** As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_config {A} (config : G -> A) : ident -> A := fun id =>
  match id with
    | Good g => config g
    | Byz b => ltac:(exfalso; now apply (Nat.nlt_0_r (proj1_sig b)), proj2_sig)
  end.

Local Opaque G B.

(** We define a particular robot [g0] that will help us distinguish two towers:
    the first one will be the one that [g)] belongs to.
    The actual value of g0 is irrelevant so we make its body opaque.  *)
Definition g0 : G.
Proof. exists 0. generalize nG_non_0. omega. Qed.

(** *  Proof of the impossiblity of gathering for two robots  **)

(** From now on and until the final theorem we assume given a robogram [r]. *)

Variable r : robogram.
Open Scope R_scope.

(* A demon that makes the robogram fail on any invalid configuration:
   - if robots go on the position of the other one (symmetrical by definition of robogram),
     activate both and they swap positions;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

Definition spectrum0 : spectrum := add origin (Nat.div2 nG) (singleton one (Nat.div2 nG)).

Theorem invalid_spect : forall config, invalid config -> forall g,
  { sim : similarity location | !! config == map sim spectrum0 & sim origin == get_location (config (Good g)) }.
Proof.
intros config Hconfig g.
destruct (invalid_strengthen (reflexivity _) Hconfig) as [pt1 [pt2 Hdiff Hspect]].
destruct (get_location (config (Good g)) =?= pt1) as [Heq1 | Heq1].
+ (* we map origin to pt1 and unit to pt2 *)
  exists (build_similarity (symmetry non_trivial) Hdiff).
  - unfold spectrum0.
    rewrite Hspect, map_add, map_singleton,
            Similarity.build_similarity_eq1, Similarity.build_similarity_eq2; autoclass.
  - now rewrite Similarity.build_similarity_eq1.
+ (* we map origin to pt2 and unit to pt1 *)
  symmetry in Hdiff.
  exists (build_similarity (symmetry non_trivial) Hdiff).
  - unfold spectrum0.
    rewrite Hspect, map_add, map_singleton, 
            Similarity.build_similarity_eq1, Similarity.build_similarity_eq2; autoclass; [].
    intro. rewrite 2 add_spec, 2 singleton_spec. do 2 destruct_match; simpl in *; omega.
  - rewrite Similarity.build_similarity_eq1. symmetry.
    assert (Hin := pos_in_config config origin (Good g)).
    rewrite Hspect, add_In, In_singleton in Hin. hnf in Heq1. tauto.
Defined.

Definition proj1_sig2 {A : Type} {P Q : A -> Prop} (e : {x : A | P x & Q x}) := let (a, _, _) := e in a.

(* This proof is different that the one for R and requires invalid_spect to be transparent. *)
Lemma invalid_spect_compat : forall config1 config2 (H1 : invalid config1) (H2 : invalid config2),
  config1 == config2 ->
  forall g h, get_location (config1 (Good g)) == get_location (config2 (Good h)) ->
  proj1_sig2 (invalid_spect H1 g) == proj1_sig2 (invalid_spect H2 h).
Proof.
intros config1 config2 H1 H2 Heq g h Hgh.
unfold invalid_spect.
destruct (invalid_strengthen (reflexivity 0%nat) H1) as [pt1 [pt2 Hdiff Hspect]],
         (invalid_strengthen (reflexivity 0%nat) H2) as [pt3 [pt4 Hdiff' Hspect']].
assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (pt3 :: pt4 :: nil)).
{ rewrite Heq, Hspect' in Hspect. apply support_compat in Hspect.
  revert Hspect. rewrite 2 support_add; auto; [].
  destruct (In_dec pt3 (singleton pt4 (Nat.div2 nG))) as [Habs |];
  [| destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Habs |]].
  - rewrite In_singleton in Habs. now elim Hdiff'.
  - rewrite In_singleton in Habs. now elim Hdiff.
  - rewrite 2 support_singleton; auto; []. now symmetry. }
repeat destruct_match; simpl; rewrite Hgh in *; intro.
+ assert (Heq1 : pt1 == pt3) by now transitivity (get_location (config2 (Good h))).
  rewrite Heq1 in Hperm. apply PermutationA_cons_inv in Hperm; autoclass; [].
  rewrite PermutationA_1 in Hperm; autoclass; [].
  rewrite Heq1, Hperm. reflexivity.
+ assert (Heqpt : pt1 == pt4 /\ pt2 == pt3).
  { rewrite PermutationA_2 in Hperm; autoclass; [].
    destruct Hperm as [[Heq1 Heq2] |?]; trivial; [].
    rewrite Heq1 in *. simpl complement in *. contradiction. }
  destruct Heqpt as [Heq1 Heq2].
  rewrite Heq1, Heq2. reflexivity.
+ assert (Heqpt : pt1 == pt4 /\ pt2 == pt3).
  { rewrite PermutationA_2 in Hperm; autoclass; [].
    destruct Hperm as [[Heq1 Heq2] |?]; trivial; [].
    rewrite Heq1 in *. simpl complement in *. contradiction. }
  destruct Heqpt as [Heq1 Heq2].
  rewrite Heq1, Heq2. reflexivity.
+ assert (Heq2 : pt2 == pt4).
  { transitivity (get_location (config2 (Good h))).
    + assert (Hin := pos_in_config config1 origin (Good h)).
      rewrite Hspect, Heq, add_In, In_singleton in Hin.
      simpl complement in *. symmetry. tauto.
    + assert (Hin := pos_in_config config2 origin (Good h)).
      rewrite Hspect', add_In, In_singleton in Hin.
      simpl complement in *. tauto. }
  rewrite Heq2 in Hperm. setoid_rewrite permA_swap in Hperm.
  apply PermutationA_cons_inv in Hperm; autoclass; [].
  rewrite PermutationA_1 in Hperm; autoclass; [].
  rewrite Heq2, Hperm. reflexivity.
Qed.

Global Opaque invalid_spect.

Theorem invalid_reverse : forall (sim : similarity location) config,
  !! config == map sim spectrum0 -> invalid config.
Proof.
intros sim config Hsim.
assert (Hcardinal := cardinal_spect_from_config config origin).
assert (Heven : Nat.Even nG).
{ rewrite <- Nat.even_spec.
  cut (Nat.odd nG = false).
  + unfold Nat.odd. now rewrite Bool.negb_false_iff.
  + apply Bool.not_true_is_false. intro Hodd.
    rewrite Hsim, map_cardinal in Hcardinal; autoclass; [].
    unfold spectrum0 in Hcardinal. rewrite cardinal_add, cardinal_singleton in Hcardinal.
    rewrite (Nat.div2_odd nG) in Hcardinal at 3. rewrite Hodd in *. simpl in *. omega. }
repeat split; trivial; [|].
+ rewrite <- Nat.even_spec in Heven.
  assert (HnG := nG_non_0). simpl nG in *.
  destruct n as [| [| ?]]; simpl; discriminate || omega || now elim HnG.
+ exists (sim origin), (sim one).
  repeat split.
  - intro Heq. apply Similarity.injective in Heq. symmetry in Heq. revert Heq. apply non_trivial.
  - rewrite Hsim, map_injective_spec; autoclass; try apply Similarity.injective; [].
    unfold spectrum0. rewrite add_same, singleton_other; try omega; [].
    symmetry. apply non_trivial.
  - rewrite Hsim, map_injective_spec; autoclass; try apply Similarity.injective; [].
    unfold spectrum0. rewrite add_other, singleton_same; try omega; [].
    apply non_trivial.
Qed.

(** The movement of robots in the reference configuration. *)
Definition move := r spectrum0 ratio_1.

(** The key idea is to prove that we can always make robots see the same spectrum in any invalid configuration.
    If they do not gather in one step, then they will never do so.

    So, in [config1], if the robot move to [unit], we activate all robots and they swap locations.
    If it does not, we activate only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move == one.

Definition change_frame1 config (g : G) :=
  match invalid_dec config with
    | Specif.left  H => Similarity.inverse (proj1_sig2 (invalid_spect H g))
    | Specif.right H => Similarity.id (* this second case will never be used *)
  end.

Instance change_frame1_compat : Proper (equiv ==> Logic.eq ==> equiv) change_frame1.
Proof.
unfold change_frame1. intros config1 config2 Heq gg g ?. subst gg.
destruct (invalid_dec config1) as [H1 | ?],
         (invalid_dec config2) as [H2 | ?];
try reflexivity || (apply invalid_compat in Heq; tauto); [].
f_equiv. apply invalid_spect_compat; trivial; now rewrite Heq.
Qed.

Definition da1 : demonic_action := {|
  activate := fun _ => true;
  relocate_byz := fun _ b => mk_info origin;
  change_frame := change_frame1;
  choose_update := fun _ _ _ => tt;
  
  activate_compat := ltac:(now repeat intro);
  relocate_byz_compat := ltac:(now repeat intro; f_equiv);
  change_frame_compat := change_frame1_compat;
  choose_update_compat := ltac:(now repeat intro) |}.

Definition bad_demon1 : demon := Stream.constant da1.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof. coinduction bad_fair1. intros id1 id2. now constructor. Qed.

(* It is a more restrained version where we assume that the starting configuration is invalid. *)
Lemma round_simplify1 : forall config pt1 pt2,
  pt1 =/= pt2 ->
  !! config == add pt1 (Nat.div2 nG) (singleton pt2 (Nat.div2 nG)) ->
  round r da1 config == fun id => match id with
                          | Good g => mk_info (if get_location (config (Good g)) =?= pt1 then pt2 else pt1)
                          | Byz b => mk_info origin
                        end.
Proof.
intros config pt1 pt2 Hdiff Hspect.
assert (Hcase : forall id, get_location (config id) == pt1 \/ get_location (config id) == pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hspect, add_In, In_singleton in Hin. subst. tauto. }
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
unfold round. cbn -[equiv equiv_dec get_location map_config lift].
rewrite spect_from_config_ignore_snd.
unfold change_frame1.
destruct (invalid_dec config) as [Hvalid | Hvalid].
* destruct (invalid_spect Hvalid g) as [sim Hspect1 Horigin1].
  simpl proj1_sig2.
  change (Bijection.retraction (sim ⁻¹)) with (Bijection.section sim).
  assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (sim origin :: sim one :: nil)).
  { apply support_compat in Hspect1. revert Hspect1.
    rewrite Hspect. unfold spectrum0.
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
  rewrite <- spect_from_config_ignore_snd, <- spect_from_config_map, Hspect1; autoclass; [].
  rewrite map_merge; autoclass; [].
  rewrite map_extensionality_compat, map_id; autoclass; try apply Similarity.compose_inverse_l; [].
  destruct_match.
  + assert (Hpt1 : sim origin == pt1) by (etransitivity; eauto).
    assert (Hpt2 : sim one == pt2).
    { decompose [and or] Hperm; auto; []. rewrite Hpt1 in *. now elim Hdiff. }
    simpl get_location. unfold id.
    rewrite <- Hpt2. f_equiv. now rewrite <- Hmove.
  + assert (Hpt2 : sim origin == pt2).
    { destruct (Hcase (Good g)); try contradiction; []. etransitivity; eauto. }
    assert (Hpt1 : sim one == pt1).
    { decompose [and or] Hperm; auto; []. rewrite Hpt2 in *. now elim Hdiff. }
    simpl get_location. unfold id.
    rewrite <- Hpt1. f_equiv. now rewrite <- Hmove.
* elim Hvalid.
  apply (invalid_reverse (build_similarity non_trivial Hdiff)).
  rewrite Hspect. unfold spectrum0.
  rewrite map_add, map_singleton, Similarity.build_similarity_eq1, Similarity.build_similarity_eq2; autoclass.
  intro. rewrite 2 add_spec, 2 singleton_spec. do 2 destruct_match; omega.
Qed.

Lemma invalid_da1_next : forall config, invalid config -> invalid (round r da1 config).
Proof.
intros config Hvalid.
destruct (invalid_strengthen (reflexivity _) Hvalid) as [pt1 [pt2 Hdiff Hspect]].
(* As [config] is invalid, all robots are only on two locations. *)
assert (Hcase : forall id, get_location (config id) == pt1 \/ get_location (config id) == pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hspect, add_In, In_singleton in Hin. subst. tauto. }
(* We build the similarity that performs the swap. *)
assert (Hdiff' : pt2 =/= pt1) by now symmetry.
pose (sim := build_similarity Hdiff Hdiff' : similarity location).
assert (Hconfig : round r da1 config == map_config (lift sim) config).
{ rewrite (round_simplify1 config Hdiff Hspect).
  apply no_byz_eq. intro g.
  cbn [map_config]. rewrite get_location_lift, mk_info_get_location.
  destruct (get_location (config (Good g)) =?= pt1) as [Hg | Hg];
  destruct (Hcase (Good g)) as [Hg' | Hg']; rewrite Hg' in *;
  solve [ symmetry; apply Similarity.build_similarity_eq1
        | symmetry; apply Similarity.build_similarity_eq2
        |  auto; now elim Hg ]. }
(* Let us pick an arbitrary robot (here [g0]) and consider the (unique) similarity [sim1]
   that maps [!! config] to [spectrum0] and such that [sim1 g0 = origin]. *)
destruct (invalid_spect Hvalid g0) as [sim1 Hsim1 ?].
apply (invalid_reverse (sim ∘ sim1)).
rewrite Hconfig.
rewrite <- spect_from_config_ignore_snd, <- spect_from_config_map, Hsim1, map_merge; autoclass.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_invalid1 : forall config, invalid config ->
  Always_invalid (execute r bad_demon1 config).
Proof.
coinduction differs.
+ now simpl.
+ cbn. now apply invalid_da1_next.
Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time  **)

Section MoveNot1.

Hypothesis Hmove : move =/= one.

(** A function that return different results depending on which tower the robot is.
    Both results are parametrized by the ordered locations of the towers. *)
Definition select_tower {A} (b_g0 b : forall pt1 pt2 : location, pt1 =/= pt2 -> A)
                            (default : A) (config : configuration) (id : ident) :=
  match invalid_dec config with
    | Specif.left  H =>
        match invalid_strengthen (reflexivity _) H with
        | existT _ pt1 (exist2 _ _ pt2 Hdiff Hspect) =>
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
Proof.
intros A eqA b_g0 b Hb_g0 Hb default1 default2 Hdefault config1 config2 Hconfig gg g ?. subst gg.
unfold select_tower.
destruct (invalid_dec config1) as [Hvalid1 | Hvalid1],
         (invalid_dec config2) as [Hvalid2 | Hvalid2];
try (exfalso; revert Hvalid1 Hvalid2; rewrite Hconfig; tauto); trivial; [].
change 0%nat with nB.
destruct (invalid_strengthen (reflexivity nB) Hvalid1) as [pt1  [pt2  Hdiff  Hspect ]],
         (invalid_strengthen (reflexivity nB) Hvalid2) as [pt1' [pt2' Hdiff' Hspect']].
assert (Hperm : PermutationA equiv (pt1 :: pt2 :: nil) (pt1' :: pt2' :: nil)).
{ apply support_compat in Hspect'. revert Hspect'.
  rewrite <- Hconfig, Hspect.
  rewrite 2 support_add; auto; [].
  destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Hin |];
  try (rewrite In_singleton in Hin; destruct Hin as [Hin _]; contradiction); [].
  destruct (In_dec pt1' (singleton pt2' (Nat.div2 nG))) as [Hin |];
  try (rewrite In_singleton in Hin; destruct Hin as [Hin _]; contradiction); [].
  rewrite 2 support_singleton; auto. }
apply PermutationA_2 in Hperm; autoclass; [].
assert (Hcase1 : forall id, get_location (config1 id) == pt1 \/ get_location (config1 id) == pt2).
{ intro id. assert (Hin := pos_in_config config1 origin id).
  rewrite Hspect, add_In, In_singleton in Hin. tauto. }
assert (Hcase2 : forall id, get_location (config2 id) == pt1' \/ get_location (config2 id) == pt2').
{ intro id. assert (Hin := pos_in_config config2 origin id).
  rewrite Hspect', add_In, In_singleton in Hin. tauto. }
(* repeat destruct_match; rewrite Hconfig in *;
try assert (Heq : pt1 == pt1' /\ pt2 == pt2')
    by (destruct Hperm as [? | [Heq1 Heq2]]; trivial; [];
        rewrite Heq1, Heq2 in *;
        split; transitivity (get_location (config2 (Good g0))); auto)
 || assert (Heq : pt1 == pt2' /\ pt2 == pt1')
    by (destruct Hperm as [? | [Heq1 Heq2]]; trivial; [];
        rewrite Heq1, Heq2 in *;
        split; transitivity (get_location (config2 (Good g0))); auto);
try (destruct Heq as [Heq1 Heq2]; rewrite Heq1, Heq2 in *; (now apply Hb_g0) || (now apply Hb)).

assert (Heq : pt1 == pt1' /\ pt2 == pt2')
      by (destruct Hperm as [? | [Heq1 Heq2]]; trivial; [];
          rewrite Heq1, Heq2 in *;
          split; transitivity (get_location (config2 (Good g0))); auto).

  try (assert (Heq : pt1 == pt1' /\ pt2 == pt2')
       by (destruct Hperm as [? | [Heq1 Heq2]]; trivial; [];
           rewrite Heq1, Heq2, Hconfig in *;
           split; transitivity (get_location (config2 (Good g0))); auto);
       destruct Heq as [Heq1 Heq2]; rewrite Heq1, Heq2 in *; now apply Hb_g0).


  try (assert (Heq : pt1 = pt1' /\ pt2 = pt2') by (intuition congruence); destruct Heq; subst pt1' pt2');
  try (assert (Heq : pt1 = pt2' /\ pt2 = pt1') by (intuition congruence); destruct Heq; subst pt1' pt2');
  (now apply Hb_g0) || (now apply Hb) || idtac.
  - assert (Heq : pt1 == pt1' /\ pt2 == pt2').
    { destruct Hperm as [? | [Heq1 Heq2]]; trivial; [].
      rewrite Heq1, Heq2, Hconfig in *.
      split; transitivity (get_location (config2 (Good g0))); auto. }
    now apply Hb_g0.
  - assert (Heq : pt1 == pt1' /\ pt2 == pt2').
    { destruct Hperm as [? | [Heq1 Heq2]]; trivial; [].
      rewrite Heq1, Heq2, Hconfig in *.
      split; transitivity (get_location (config2 (Good g0))); auto. }
    apply Hb.
+ assumption. *)
Admitted.

Lemma select_tower_case_1' : forall {A} `{Setoid A} b1 b2 (d : A) pt config id
  (Hdiff : get_location (config (Good g0)) =/= pt),
  !! config == add (get_location (config (Good g0))) (Nat.div2 nG) (singleton pt (Nat.div2 nG)) ->
  (forall pt1 pt2 pt3 pt4 (Hdiff : pt1 =/= pt2) (Hdiff' : pt3 =/= pt4),
     pt1 == pt3 -> pt2 == pt4 ->  b1 pt1 pt2 Hdiff == b1 pt3 pt4 Hdiff') ->
  get_location (config id) == get_location (config (Good g0)) ->
  select_tower b1 b2 d config id == b1 (get_location (config (Good g0))) pt Hdiff.
Proof.
intros A ? b1 b2 d pt config id Hdiff Hspect Hb1 Hcase.
unfold select_tower.
destruct (invalid_dec config) as [Hvalid | Hvalid].
+ destruct (invalid_strengthen (reflexivity 0%nat) Hvalid) as [pt1 [pt2 Hdiff' Hspect']].
  assert (Hperm : PermutationA equiv (get_location (config (Good g0)) :: pt :: nil) (pt1 :: pt2 :: nil)).
  { apply support_compat in Hspect'. revert Hspect'.
    rewrite Hspect, 2 support_add; auto; [].
    destruct (In_dec pt1 (singleton pt2 (Nat.div2 nG))) as [Hin | Hin],
             (In_dec (get_location (config (Good g0))) (singleton pt (Nat.div2 nG))) as [Hin' | Hin'];
    rewrite In_singleton in Hin, Hin';
    try solve [ simpl in *; tauto
              | destruct Hin' as [Hin' _]; apply Similarity.injective in Hin'; simpl in *; lra ]; [].
    rewrite 2 support_singleton; auto. }
  rewrite PermutationA_2 in Hperm; autoclass; [].
  repeat destruct_match; try contradiction; [|].
  - simpl in *. unfold Datatypes.id in *.
    destruct Hperm as [[Heq1 Heq2] | [Heq1 Heq2]]; apply Hb1; auto; [].
    transitivity pt1; auto; []. transitivity (config (Good g0)); auto.
  - simpl in *. destruct Hperm as [[] | []]; subst; auto; congruence.
+ elim Hvalid.
  apply (invalid_reverse (build_similarity non_trivial Hdiff)).
  rewrite Hspect. unfold spectrum0.
  rewrite map_add, map_singleton; autoclass; [].
  rewrite Similarity.build_similarity_eq1, Similarity.build_similarity_eq2.
  intro. rewrite 2 add_spec, 2 singleton_spec. do 2 destruct_match; omega.
Qed.

Lemma select_tower_case_1 : forall {A} `{Setoid A} b1 b2 (d : A) config id,
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> b1 pt1 pt2 Hdiff == b1 pt1' pt2' Hdiff') ->
  invalid config ->
  get_location (config id) == get_location (config (Good g0)) ->
  exists pt Hdiff, select_tower b1 b2 d config id == b1 (get_location (config (Good g0))) pt Hdiff
                /\ In pt (!! config).
Proof.
intros A ? b1 b2 d config id Hb1 ? Hcase.
unfold select_tower.
destruct (invalid_dec config) as [Hvalid | Hvalid].
* destruct (invalid_strengthen (reflexivity 0%nat) Hvalid) as [pt1 [pt2 Hdiff Hspect]].
  repeat destruct_match; try contradiction; [|].
  + assert (Hdiff' : get_location (config (Good g0)) =/= pt2).
    { intro. apply Hdiff. now transitivity (get_location (config (Good g0))). }
    exists pt2, Hdiff'. split.
    - now apply Hb1.
    - rewrite Hspect, add_In, In_singleton. auto.
  + assert (Heq : get_location (config (Good g0)) == pt2).
    { assert (Hin := pos_in_config config origin (Good g0)).
      rewrite Hspect in Hin. rewrite add_In, In_singleton in Hin.
      destruct Hin as [[] | []]; trivial. contradiction. }
    revert_one @complement. intro Hdiff'.
    exists pt1, Hdiff'. split.
    - now apply Hb1.
    - rewrite Hspect, add_In, In_singleton. auto.
* contradiction.
Qed.

(* NB: If we have unicity of inquality proof, we can replace Hdiff with the assumption. *)
Lemma select_tower_case_2 : forall {A} `{Setoid A} b1 b2 (d : A) config id,
  (forall pt1 pt2 pt1' pt2' (Hdiff : pt1 =/= pt2) (Hdiff' : pt1' =/= pt2'),
     pt1 == pt1' -> pt2 == pt2' -> b2 pt1 pt2 Hdiff == b2 pt1' pt2' Hdiff') ->
  invalid config ->
  get_location (config id) =/= get_location (config (Good g0)) ->
  exists Hdiff,
    select_tower b1 b2 d config id == b2 (get_location (config (Good g0))) (get_location (config id)) Hdiff.
Proof.
intros A ? b1 b2 d config id Hb2 ? Hdiff.
unfold select_tower.
destruct (invalid_dec config) as [Hvalid | Hvalid].
+ destruct (invalid_strengthen (reflexivity 0%nat) Hvalid) as [pt1 [pt2 Hdiff' Hspect']].
  assert (Hcase : get_location (config (Good g0)) == pt1 /\ get_location (config id) == pt2
               \/ get_location (config (Good g0)) == pt2 /\ get_location (config id) == pt1).
  { assert (Hin0 := pos_in_config config origin (Good g0)).
    assert (Hin := pos_in_config config origin id).
    rewrite Hspect', add_In,In_singleton in Hin0, Hin.
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
  ~invalid config -> select_tower b1 b2 d config id = d.
Proof. intros A b1 b2 d config id Hvalid. unfold select_tower. destruct_match; tauto. Qed.

Definition activate2 (b1 b2 : bool) := select_tower (fun _ _ _ => b1) (fun _ _ _ => b2) true.

Instance activate2_compat : forall b1 b2, Proper (equiv ==> eq ==> eq) (activate2 b1 b2).
Proof. intros. unfold activate2. now apply select_tower_compat. Qed.

Definition change_frame2 (config : configuration) (g : G) : similarity location :=
  @select_tower (similarity location)
    (fun pt1 pt2 (Hdiff : pt1 =/= pt2) => build_similarity Hdiff non_trivial)
    (fun pt1 pt2 (Hdiff : pt1 =/= pt2) => build_similarity Hdiff (symmetry non_trivial))
    Similarity.id
    config
    (Good g).

Instance change_frame2_compat : Proper (equiv ==> eq ==> equiv) change_frame2.
Proof.
intros config1 config2 Hconfig g1 g2 Hg. unfold change_frame2.
cut (Good g1 = Good g2); try congruence; [].
generalize (Good g1), (Good g2). revert config1 config2 Hconfig.
apply select_tower_compat; reflexivity || intros; now apply Similarity.build_similarity_compat.
Qed.

Definition da2_left config : demonic_action := {|
  activate := activate2 true false config;
  relocate_byz := fun _ _ => mk_info origin;
  change_frame := change_frame2;
  choose_update := fun _ _ _ => tt;
  
  activate_compat := activate2_compat _ _ (reflexivity _);
  relocate_byz_compat := ltac:(now repeat intro);
  change_frame_compat := change_frame2_compat;
  choose_update_compat := ltac:(now repeat intro) |}.

Definition da2_right config : demonic_action := {|
  activate := activate2 false true config;
  relocate_byz := fun _ _ => mk_info origin;
  change_frame := change_frame2;
  choose_update := fun _ _ _ => tt;
  
  activate_compat := ltac:(now repeat intro; subst);
  relocate_byz_compat := ltac:(now repeat intro);
  change_frame_compat := change_frame2_compat;
  choose_update_compat := ltac:(now repeat intro) |}.

Lemma round_simplify2_left : forall config (sim : similarity location),
  !! config == map sim spectrum0 ->
  get_location (config (Good g0)) == sim origin ->
  round r (da2_left config) config
  == fun id => match id with
                 | Good g => mk_info (if get_location (config (Good g)) =?= sim origin then sim move else sim one)
                 | Byz b => mk_info origin
               end.
Proof.
intros config sim Hspect Hsim0.
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
unfold round. cbn -[equiv equiv_dec get_location map_config lift].
unfold activate2, change_frame2.
assert (Hvalid := invalid_reverse sim config Hspect).
destruct (get_location (config (Good g)) =?= get_location (config (Good g0))) as [Hcase | Hcase].
* (* The robot is on the first tower so it moves like g0. *)
  destruct (select_tower_case_1 (fun pt1 pt2 (_ : pt1 =/= pt2) => true)
                                (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
                                true (Good g) ltac:(reflexivity) Hvalid Hcase)
    as [pt [Hdiff [Hactivate Hpt]]].
  destruct (select_tower_case_1 (fun pt1 pt2 (Hdiff0 : pt1 =/= pt2) => build_similarity Hdiff0 non_trivial)
                                (fun pt1 pt2 (Hdiff0 : pt1 =/= pt2) => build_similarity Hdiff0 (symmetry non_trivial))
                                Similarity.id (Good g) ltac:(now intros; apply Similarity.build_similarity_compat)
                                Hvalid Hcase)
    as [pt' [Hdiff' [Hframe Hpt']]].
  rewrite Hactivate. rewrite Hframe at 1 2. clear dependent pt.
  assert (Hsimg : get_location (config (Good g)) == sim origin) by (etransitivity; eauto).
  destruct_match; try contradiction; [].
  rewrite spect_from_config_ignore_snd, <- spect_from_config_ignore_snd,
          <- spect_from_config_map; autoclass; [].
  rewrite Hspect, map_merge; autoclass; [].
  assert (Hpt : pt' == sim one).
  { rewrite Hspect in Hpt'. unfold spectrum0 in Hpt'.
    rewrite map_add, map_singleton in Hpt'; autoclass; [].
    rewrite add_In, In_singleton in Hpt'. destruct Hpt' as [[Hpt'?] |]; try tauto; [].
    elim Hdiff'. now rewrite Hpt'. }
  assert (Hspectrum0 : map (fun x : location => build_similarity Hdiff' non_trivial (sim x)) spectrum0 == spectrum0).
  { unfold spectrum0. rewrite map_add, map_singleton; autoclass; [].
    rewrite <- Hsim0, Similarity.build_similarity_eq1.
    rewrite <- Hpt, Similarity.build_similarity_eq2.
    intro. rewrite 2 add_spec, 2 singleton_spec. do 2 destruct_match; omega. }
  rewrite Hspectrum0. change ((r spectrum0) ratio_1) with move.
  change ((build_similarity Hdiff' non_trivial)⁻¹ move == sim move).
  rewrite Similarity.build_similarity_inverse.
  admit.
* (* The robot is on the second tower so it does not move. *)
  assert (Hsim1 : get_location (config (Good g)) == sim one).
  { assert (Hin := pos_in_config config origin (Good g)).
    rewrite Hspect in Hin. unfold spectrum0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    destruct Hin as [[] | []]; trivial. elim Hcase. etransitivity; eauto. }
  destruct (select_tower_case_2 (fun pt1 pt2 (_ : pt1 =/= pt2) => true)
    (fun pt1 pt2 (_ : pt1 =/= pt2) => false) true (Good g) ltac:(reflexivity) Hvalid Hcase) as [Hdiff Hactivate].
  rewrite Hactivate.
  destruct_match; trivial; []. elim Hcase. etransitivity; eauto.
Admitted.

Lemma invalid_da2_left_next : forall config,
  invalid config -> invalid (round r (da2_left config) config).
Proof.
intros config Hvalid.
destruct (invalid_spect Hvalid g0) as [sim Hspect Hsim0].
assert (Hdiff_move : sim move =/= sim one).
{ intro Heq. now apply Similarity.injective in Heq. }
pose (sim' := build_similarity non_trivial Hdiff_move).
apply (invalid_reverse sim').
assert (Hconfig : round r (da2_left config) config == map_config (lift (sim' ∘ sim ⁻¹)) config).
{ rewrite round_simplify2_left; auto; [].
  apply no_byz_eq. intro g.
  cbn [map_config]. rewrite mk_info_get_location, get_location_lift.
  destruct (get_location (config (Good g)) =?= sim origin) as [Heq | Heq].
  + rewrite Heq. cbn -[equiv sim']. rewrite Bijection.retraction_section.
    unfold sim'. rewrite Similarity.build_similarity_eq1.
  + assert (Hsim1 : get_location (config (Good g)) == sim 1).
    { assert (Hin := pos_in_config config origin (Good g)).
      rewrite Hspect in Hin. unfold spectrum0 in Hin.
      rewrite  map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
      destruct Hin as [[] | []]; trivial; contradiction. }
    rewrite Hsim1. cbn -[equiv sim']. rewrite Bijection.retraction_section.
    unfold sim'. now rewrite build_similarity_eq2. }
rewrite Hconfig.
rewrite <- spect_from_config_ignore_snd, <- spect_from_config_map, Hspect; [| now autoclass].
rewrite map_merge; autoclass; [].
apply map_extensionality_compat; autoclass; [].
intro. cbn -[equiv sim']. now rewrite Bijection.retraction_section.
Qed.

Lemma da2_left_injective : forall config, invalid config -> forall g1 g2,
  get_location (round r (da2_left config) config g1) == get_location (round r (da2_left config) config g2)
  <-> get_location (config g1) == get_location (config g2).
Proof.
intros config Hvalid id1 id2.
pattern id2. apply no_byz. pattern id1. apply no_byz. clear id1 id2. intros g1 g2.
destruct (invalid_spect Hvalid g0) as [sim Hspect Hsim0].
erewrite 2 round_simplify2_left; auto; [].
rewrite 2 mk_info_get_location.
assert (sim move =/= sim 1). { intro Habs. apply Similarity.injective in Habs. contradiction. }
do 2 destruct_match; try (simpl in *; split; intro; congruence); [].
assert (Hcase : forall id, get_location (config id) == sim 0 \/ get_location (config id) == sim 1).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hspect in Hin. unfold spectrum0 in Hin.
  rewrite  map_add, map_singleton, add_In, In_singleton in Hin; autoclass; []. tauto. }
destruct (Hcase (Good g1)), (Hcase (Good g2)); split; intro; simpl in *; tauto || congruence.
Qed.

Lemma round_simplify2_right : forall config (sim : similarity location),
  !! config == map sim spectrum0 ->
  get_location (config (Good g0)) == sim 1 ->
  round r (da2_right config) config
  == fun id => match id with
                 | Good g => mk_info (if get_location (config (Good g)) =?= sim 1 then sim 1 else sim move)
                 | Byz b => mk_info 0
               end.
Proof.
intros config sim Hspect Hsim1.
apply no_byz_eq. intro g.
rewrite mk_info_get_location.
unfold round. cbn -[equiv equiv_dec get_location map_config lift].
rewrite spect_from_config_ignore_snd.
unfold activate2, change_frame2.
assert (Hvalid := invalid_reverse sim config Hspect).
destruct (get_location (config (Good g)) =?= get_location (config (Good g0))) as [Hcase | Hcase].
* destruct (select_tower_case_1 (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
    (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g) Hvalid Hcase) as [pt [Hdiff [Hactivate Hpt]]].
  rewrite Hactivate.
  destruct_match; simpl in *; congruence.
* assert (Hsim0 : get_location (config (Good g)) == sim 0).
  { assert (Hin := pos_in_config config origin (Good g)).
    rewrite Hspect in Hin. unfold spectrum0 in Hin.
    rewrite map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
    destruct Hin as [[] | []]; trivial; []. elim Hcase. etransitivity; eauto. }
  destruct (select_tower_case_2 (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
    (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g) Hvalid Hcase) as [Hdiff Hactivate].
  destruct (select_tower_case_2 (fun pt1 pt2 (Hdiff0 : pt1 =/= pt2) => build_similarity Hdiff0 neq_0_1)
    (fun pt1 pt2 (Hdiff0 : pt1 =/= pt2) => build_similarity Hdiff0 neq_1_0) Similarity.id (Good g) Hvalid Hcase)
  as [Hdiff' Hframe].
  rewrite Hactivate, Hframe.
  assert (Hsim : sim == build_similarity neq_1_0 Hdiff').
  { apply (similarity_eq _ _ neq_0_1).
    - now rewrite build_similarity_eq2, Hsim0.
    - now rewrite build_similarity_eq1. }
  rewrite <- spect_from_config_ignore_snd, <- spect_from_config_map; autoclass; [].
  rewrite Hspect, map_merge; autoclass; [].
  rewrite <- (map_extensionality_compat Similarity.id), map_id; autoclass; [|].
  + destruct_match.
    - elim neq_0_1. apply (Similarity.injective sim).
      now transitivity (get_location (config (Good g))).
    - transitivity ((build_similarity (symmetry Hcase) neq_1_0)⁻¹ move); try reflexivity; [].
      rewrite Hsim, build_similarity_inverse.
      now apply build_similarity_compat.
  + change (Similarity.id == build_similarity (symmetry Hcase) neq_1_0 ∘ sim).
    assert (Hsim' : sim⁻¹ == build_similarity (symmetry Hcase) neq_1_0).
    { rewrite <- build_similarity_inverse, Hsim. f_equiv. now apply build_similarity_compat. }
    rewrite <- Hsim'. symmetry. apply compose_inverse_l.
Qed.

Lemma invalid_da2_right_next : forall config,
  invalid config -> invalid (round r (da2_right config) config).
Proof.
intros config Hvalid.
destruct (invalid_strengthen (reflexivity _) Hvalid) as [pt1 [pt2 Hdiff Hspect]].
(* As [config] is invalid, all robots are only on two locations. *)
assert (Hcase : forall id, get_location (config id) = pt1 \/ get_location (config id) = pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hspect, add_In, In_singleton in Hin. tauto. }
(* Let [g1] and [g2] be robots mapped to these two locations. *)
assert (Hin1 : In pt1 (!! config)).
{ rewrite Hspect, add_In. left. split; trivial; reflexivity. }
rewrite spect_from_config_In in Hin1. destruct Hin1 as [[g1 | []] Hg1]; try omega; [].
assert (Hin2 : In pt2 (!! config)).
{ rewrite Hspect, add_In, In_singleton. right. split; trivial; reflexivity. }
rewrite spect_from_config_In in Hin2. destruct Hin2 as [[g2 | []] Hg2]; try omega; [].
(* To ease the rest of the proof, we assume that pt1 is the location of [g0],
   swapping them if necessary. *)
assert (Hg : exists g, get_location (config (Good g0)) =/= get_location (config (Good g))).
{ destruct (get_location (config (Good g0)) =?= pt1).
  - exists g2. simpl in *; congruence.
  - exists g1. simpl in *; congruence. }
destruct Hg as [g3 Hg3].
destruct (invalid_spect Hvalid g3) as [sim Hspect' Hsim0].
assert (Hcase' : forall id, get_location (config id) = sim 0 \/ get_location (config id) = sim 1).
{ intro id. assert (Hin := pos_in_config config origin id). unfold spectrum0 in *.
  rewrite Hspect', map_add, map_singleton, add_In, In_singleton in Hin; autoclass; simpl in *; tauto. }
assert (Hsim1 : get_location (config (Good g0)) == sim 1).
{ destruct (Hcase' (Good g0)); trivial; []. elim Hg3. now rewrite <- Hsim0. }
clear pt1 pt2 g1 g2 Hg1 Hg2 Hdiff Hspect Hcase.
assert (Hdiff_move : sim move =/= sim 1).
{ intro Heq. now apply Similarity.injective in Heq. }
pose (sim' := build_similarity neq_0_1 Hdiff_move).
apply (invalid_reverse sim').
assert (Hconfig : round r (da2_right config) config == map_config (lift (sim' ∘ sim ⁻¹)) config).
{ rewrite round_simplify2_right; auto; [].
  apply no_byz_eq. intro g.
  cbn [map_config]. rewrite mk_info_get_location, get_location_lift.
  destruct (get_location (config (Good g)) =?= sim 1) as [Heq | Heq].
  + rewrite Heq. cbn -[equiv sim']. rewrite Bijection.retraction_section.
    unfold sim'. now rewrite build_similarity_eq2.
  + assert (Hsim1' : get_location (config (Good g)) == sim origin).
    { assert (Hin := pos_in_config config origin (Good g)).
      rewrite Hspect' in Hin. unfold spectrum0 in Hin.
      rewrite  map_add, map_singleton, add_In, In_singleton in Hin; autoclass; [].
      destruct Hin as [[] | []]; trivial; contradiction. }
    rewrite Hsim1'. cbn -[equiv sim']. rewrite Bijection.retraction_section.
    unfold sim'. now rewrite build_similarity_eq1. }
rewrite Hconfig.
rewrite <- spect_from_config_ignore_snd, <- spect_from_config_map, Hspect'; [| now autoclass].
rewrite map_merge; autoclass; [].
apply map_extensionality_compat; autoclass; [].
intro. cbn -[equiv sim']. now rewrite Bijection.retraction_section.
Qed.

Lemma da2_right_injective : forall config, invalid config -> forall g1 g2,
  get_location (round r (da2_right config) config g1) == get_location (round r (da2_right config) config g2)
  <-> get_location (config g1) == get_location (config g2).
Proof.
intros config Hvalid id1 id2.
pattern id2. apply no_byz. pattern id1. apply no_byz. clear id1 id2. intros g1 g2.
destruct (invalid_strengthen (reflexivity _) Hvalid) as [pt1 [pt2 Hdiff Hspect]].
(* As [config] is invalid, all robots are only on two locations. *)
assert (Hcase : forall id, get_location (config id) = pt1 \/ get_location (config id) = pt2).
{ intro id. assert (Hin := pos_in_config config origin id).
  rewrite Hspect, add_In, In_singleton in Hin. tauto. }
(* Let [g1] and [g2] be robots mapped to these two locations. *)
assert (Hin1 : In pt1 (!! config)).
{ rewrite Hspect, add_In. left. split; trivial; reflexivity. }
rewrite spect_from_config_In in Hin1. destruct Hin1 as [[g1' | []] Hg1]; try omega; [].
assert (Hin2 : In pt2 (!! config)).
{ rewrite Hspect, add_In, In_singleton. right. split; trivial; reflexivity. }
rewrite spect_from_config_In in Hin2. destruct Hin2 as [[g2' | []] Hg2]; try omega; [].
(* To ease the rest of the proof, we assume that pt1 is the location of [g0],
   swapping them if necessary. *)
assert (Hg : exists g, get_location (config (Good g0)) =/= get_location (config (Good g))).
{ destruct (get_location (config (Good g0)) =?= pt1).
  - exists g2'. simpl in *; congruence.
  - exists g1'. simpl in *; congruence. }
destruct Hg as [g3 Hg3].
destruct (invalid_spect Hvalid g3) as [sim Hspect' Hsim0].
assert (Hcase' : forall id, get_location (config id) = sim 0 \/ get_location (config id) = sim 1).
{ intro id. assert (Hin := pos_in_config config origin id). unfold spectrum0 in *.
  rewrite Hspect', map_add, map_singleton, add_In, In_singleton in Hin; autoclass; simpl in *; tauto. }
assert (Hsim1 : get_location (config (Good g0)) == sim 1).
{ destruct (Hcase' (Good g0)); trivial; []. elim Hg3. now rewrite <- Hsim0. }
clear pt1 pt2 g1' g2' Hg1 Hg2 Hdiff Hspect Hcase.
erewrite 2 round_simplify2_right; auto; [].
rewrite 2 mk_info_get_location.
assert (sim move =/= sim 1). { intro Habs. apply Similarity.injective in Habs. contradiction. }
do 2 destruct_match; try (simpl in *; split; intro; congruence); [].
destruct (Hcase' (Good g1)), (Hcase' (Good g2)); split; intro; simpl in *; tauto || congruence.
Qed.

CoFixpoint bad_demon2 config : demon :=
   Stream.cons (da2_left config)
  (Stream.cons (da2_right (round r (da2_left config) config))
               (bad_demon2 (round r (da2_right (round r (da2_left config) config))
                           (round r (da2_left config) config)))).

Theorem Always_invalid2 : forall config, invalid config ->
  Always_invalid (execute r (bad_demon2 config) config).
Proof.
cofix differs. intros config Hconfig.
constructor; [| constructor]; cbn.
- (* Inital state *)
  assumption.
- (* State after one step *)
  now apply invalid_da2_left_next.
- (* State after two steps *)
  apply differs. now apply invalid_da2_right_next, invalid_da2_left_next.
Qed.

Theorem kFair_bad_demon2 : forall config, invalid config -> kFair 1 (bad_demon2 config).
Proof.
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
           (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g1) Hvalid') as [Hdiff Hactivate]; trivial; [].
         hnf. now rewrite da2_left_injective.
    - constructor 3; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_2 (fun pt1 pt2 (_ : pt1 =/= pt2) => false)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => true) true (Good g1) Hvalid') as [Hdiff Hactivate]; trivial; [].
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
           (fun pt1 pt2 (_ : pt1 =/= pt2) => false) true (Good g1) Hvalid')
           as [pt [Hdiff [Hactivate Hpt]]]; trivial; [].
         now rewrite da2_right_injective.
    - constructor 2; simpl.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ unfold activate2, select_tower. repeat destruct_match; trivial; contradiction.
      ++ constructor 1. simpl. unfold activate2.
         destruct (select_tower_case_1 (fun pt1 pt2 (_ : pt1 =/= pt2) => true)
           (fun pt1 pt2 (_ : pt1 =/= pt2) => false) true (Good g1) Hvalid')
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
destruct (Rdec move 1) as [Hmove | Hmove].
- (** Robots exchange positions **)
  exact (fun _ => bad_demon1).
- (** Robots do not exchange positions **)
  exact bad_demon2.
Defined.

Theorem kFair_bad_demon : forall config, invalid config -> kFair 1 (bad_demon config).
Proof.
intros. unfold bad_demon.
destruct (Rdec move 1).
- apply kFair_mono with 0%nat. exact kFair_bad_demon1. omega.
- now apply kFair_bad_demon2.
Qed.

Theorem kFair_bad_demon' : forall k config, (k>=1)%nat -> invalid config -> kFair k (bad_demon config).
Proof.
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
  forall config, invalid config ->
  exists d, kFair k d
         /\ forall pt, ~WillGather pt (execute r d config).
Proof.
intros k Hk config Hvalid. exists (bad_demon config).
split.
+ now apply kFair_bad_demon'.
+ apply different_no_gathering.
  unfold bad_demon.
  destruct (Rdec move 1) as [Hmove | Hmove].
  - now apply Always_invalid1.
  - now apply Always_invalid2.
Qed.

End ImpossibilityProof.

Print Assumptions noGathering.
