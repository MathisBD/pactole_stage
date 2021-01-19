(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


Require Import Utf8.
Require Import Reals.
Require Import Psatz.
Require Import SetoidDec.
Require Import Arith.Div2.
Require Import Lia.
Require Import SetoidList.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.R.
Require Import Pactole.Observations.MultisetObservation.
Require Import Pactole.Models.Similarity.
Require Import Pactole.Models.Rigid.
Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.
Import Datatypes.
Import List.
Import SetoidClass.


Typeclasses eauto := (bfs).


Section ConvergenceImpossibility.
(** There are [2 * n] good robots and [n] byzantine ones. *)
Variable n : nat.
Hypothesis n_non_0 : n <> 0.
Instance MyRobots : Names := Robots (2 * n) n.

(** The space is R, and it is a Euclidean space. *)
Instance Loc : Location := make_Location R.
Instance location_VS : RealVectorSpace location := R_VS.
Instance location_ES : EuclideanSpace location := R_ES.
(** Robots compute a target location. *)
Instance Robots : robot_choice location := { robot_choice_Setoid := location_Setoid }.
(** The only information in the state of a robot is its location.
    Changes of frame must come from a similarity. *)
Instance Info : State location := OnlyLocation (fun _ => True).
(** Robots observe the location of others robots with strong multiplicity. *)
Instance Obs : Observation := multiset_observation.
(** Demons use similarities to perform the change of frame of reference. *)
Instance FC : frame_choice (Similarity.similarity location) := FrameChoiceSimilarity.
(** Demons do not make any choice in how a robot state is updated, both when active or not. *)
Instance NoActiveChoice : update_choice unit := {update_choice_EqDec := unit_eqdec}.
Instance NoInactiveChoice : inactive_choice unit := {inactive_choice_EqDec := unit_eqdec}.
(** Updates are rigid. *)
Instance UpdateFun : update_function location (Similarity.similarity location) unit := {
  update := fun _ _ _ target _ => target;
  update_compat := ltac:(repeat intro; subst; auto) }.

Instance InactiveFun : inactive_function unit := {
  inactive := fun config id _ => config id;
  inactive_compat := ltac:(repeat intro; subst; auto) }.

Instance Update : RigidSetting.
Proof using . split. now intros. Qed.

Notation "!!" := (fun config => obs_from_config config origin).

(* Helping [auto] handle basic real arithmetic contradictions *)
Hint Extern 0 (1 =/= 0)%R => apply R1_neq_R0 : core.
Hint Extern 0 (0 =/= 1)%R => symmetry; trivial : core.
Hint Extern 0 (1 <> 0)%R => apply R1_neq_R0 : core.
Hint Extern 0 (0 <> 1)%R => intro; apply R1_neq_R0; now symmetry : core.
Hint Extern 0 (~@equiv R _ 1 0)%R => apply R1_neq_R0 : core.
Hint Extern 0 (~@equiv R _ 0 1)%R => intro; apply R1_neq_R0; now symmetry : core.
Hint Extern 0 (_ <> _) =>
  match goal with | H : ?x <> ?y |- ?y <> ?x => intro; apply H; now symmetry end : core.
Hint Extern 0 (~equiv R _ _ _) =>
  match goal with | H : ~@equiv R _ ?x ?y |- ~@equiv R _ ?y ?x =>
         intro; apply H; now symmetry end : core.


Implicit Type config : configuration.
Implicit Type da : demonic_action.

(* The robot trajectories are straight paths. *)
Definition path_R := path R.
Definition paths_in_R : R -> path_R := local_straight_path.
Coercion paths_in_R : R >-> path_R.


(* We need to unfold [o_is_ok] for rewriting *)
Definition obs_from_config_spec : forall config (pt : R),
  (!! config)[pt] = countA_occ _ equiv_dec pt (List.map get_location (config_list config))
 := fun config => @obs_from_config_spec R _ _ _ _ config 0%R.

Lemma nB_value : nB = n.
Proof using . reflexivity. Qed.

(** Not true in general as the info may change even if the robot does not move. *)
Lemma no_moving_same_config : forall r da config,
  moving r da config = List.nil -> round r da config == config.
Proof using .
intros r da config Hmove id.
destruct (round r da config id =?= config id) as [Heq | Heq]; trivial; [].
apply <- moving_spec in Heq. rewrite Hmove in Heq. inversion Heq.
Qed.

Lemma nG_nB : nG = 2 * nB.
Proof using . reflexivity. Qed.

Corollary even_nG : Nat.Even nG.
Proof using . exists nB. apply nG_nB. Qed.

Corollary nG_non_0 : nG <> 0.
Proof using n_non_0. rewrite nG_nB. assert (Hn0 := n_non_0). simpl. lia. Qed.

Corollary half_size_pos : Nat.div2 nG > 0.
Proof using n_non_0.
assert (Hn0 := n_non_0). rewrite nG_nB, nB_value.
destruct n as [| ?].
- lia.
- simpl. rewrite plus_comm. simpl. lia.
Qed.


(** ** Properties of executions  *)

Open Scope R_scope.

(** Expressing that all good robots are confined in a small disk. *)
Definition imprisoned (center : R) (radius : R) (e : execution) : Prop :=
  Stream.forever (Stream.instant 
    (fun config => forall g, dist center (get_location (config (Good g))) <=radius)) e.

(** The execution will end in a small disk. *)
Definition attracted (c : R) (r : R) (e : execution) : Prop := Stream.eventually (imprisoned c r) e.

Instance imprisoned_compat : Proper (equiv ==> Logic.eq ==> equiv ==> iff) imprisoned.
Proof using .
intros c1 c2 Hc ? r Hr e1 e2 He. subst. split.
+ revert c1 c2 e1 e2 Hc He. coinduction Hrec.
  - intro g.
    assert (Heq : get_location (Stream.hd e1 (Good g)) == get_location (Stream.hd e2 (Good g))).
    { apply Stream.hd_compat in He. apply get_location_compat, He. }
    rewrite <- Heq, <- Hc. match goal with H : imprisoned _ _ _ |- _ => apply H end.
  - match goal with H : imprisoned _ _ _ |- _ => inversion_clear H end.
    eapply Hrec; try eassumption; []. now f_equiv.
+ revert c1 c2 e1 e2 Hc He. coinduction Hrec.
  - intro g. apply Stream.hd_compat in He. specialize (He (Good g)). rewrite He, Hc.
    match goal with H : imprisoned _ _ _ |- _ => apply H end.
  - match goal with H : imprisoned _ _ _ |- _ => inversion_clear H end.
    eapply Hrec; try eassumption; []. now f_equiv.
Qed.

Instance attracted_compat : Proper (equiv ==> eq ==> equiv ==> iff) attracted.
Proof using . intros ? ? Heq ? ? ?. now apply Stream.eventually_compat, imprisoned_compat. Qed.

(** A solution is just convergence property for any demon. *)
Definition solution (r : robogram) : Prop :=
  forall (config : configuration) (d : demon), Fair d →
  forall (ε : R), 0 < ε → exists (pt : R), attracted pt ε (execute r d config).

Definition solution_FSYNC (r : robogram) : Prop :=
  forall (config : configuration) (d : demon), FSYNC d →
  forall (ε : R), 0 < ε → exists (pt : R), attracted pt ε (execute r d config).

(** A SSYNC solution is also a FSYNC solution. *)
Lemma synchro : ∀ r, solution r → solution_FSYNC r.
Proof using . unfold solution. intros r Hfair config d Hd. apply Hfair, FSYNC_implies_fair; autoclass. Qed.

Close Scope R_scope.
Close Scope vector_scope.


(** We split good robots into two halves. *)

Definition left  := half1 Gnames.
Definition right := half2 Gnames.

Lemma merge_left_right : left ++ right = Gnames.
Proof using . apply merge_halves. Qed.

Definition left_dec (g : G) := List.in_dec Geq_dec g left.

Lemma not_left_is_right : forall g : G, ~In g left -> In g right.
Proof using .
intros g Hleft.
assert (Hin : List.In g Gnames) by apply In_Gnames.
rewrite <- merge_left_right, in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof using .
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption.
apply Gnames_NoDup.
Qed.

Lemma left_spec : forall g, In g left <-> proj1_sig g < Nat.div2 nG.
Proof using .
Local Transparent G.
intro g. unfold left, half1. rewrite Gnames_length. unfold Gnames.
apply firstn_enum_spec.
Local Opaque G.
Qed.

Lemma right_spec : forall g, In g right <-> Nat.div2 nG <= proj1_sig g.
Proof using .
intro g. unfold right, half2. rewrite Gnames_length. unfold Gnames.
rewrite (skipn_enum_spec (Nat.div2 nG) g). intuition. apply proj2_sig.
Qed.

(** First and last robots are resp. in the first and in the second half. *)
Definition gfirst : G.
Proof. exists 0. abstract (generalize n_non_0; intro; lia). Defined.

Definition glast : G.
Proof. exists (pred nG). abstract (simpl; generalize n_non_0; intro; lia). Defined.

Lemma gfirst_left : In gfirst left.
Proof using . rewrite left_spec. simpl. apply half_size_pos. Qed.

Lemma glast_right : In glast right.
Proof using .
rewrite right_spec. simpl. assert (Heven := even_nG).
destruct n as [| [| ]]; simpl; auto; [].
apply le_n_S, Nat.div2_decr, le_n_Sn.
Qed.

Hint Resolve gfirst_left glast_right left_right_exclusive : core.


(** * Proof of the impossiblity of convergence with one third of robots byzantine. *)

(** A demon that makes the robogram fail:
    - good robots are split into two distinct towers
    - byzantine robots move alternatively between both towers
    - the stack with byzantine is activated, good robots cannot move. *)

Open Scope R_scope.
Open Scope vector_scope.

(** The reference starting configuration **)
Definition config1 : configuration := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b  => 0
  end.

(** The second configuration **)
Definition config2 : configuration := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b  => 1
  end.

Arguments config1 id : simpl never.
Arguments config2 id : simpl never.

Lemma minus_1 : -1 <> 0.
Proof using . apply Ropp_neq_0_compat, R1_neq_R0. Qed.

Definition observation1 := add 0 nG (singleton 1 nB).
Definition observation2 := add 0 nB (singleton 1 nG).

(* An auxiliary lemma to avoid trouble with dependent types. *)
Lemma obs_config_aux : forall pt1 pt2 : R, pt1 =/= pt2 ->
  forall pt n l, NoDup l -> length l = (2 * n)%nat ->
  countA_occ equiv equiv_dec pt
    (map (fun x  => if in_dec Geq_dec x (half1 l) then pt1 else pt2) l)
  = (add pt1 n (singleton pt2 n))[pt].
Proof using n_non_0.
intros pt1 pt2 Hdiff pt k. induction k as [| k]; intros l Hnodup Hlen.
* apply length_0 in Hlen. subst. simpl map. now rewrite add_0, singleton_0 (* , empty_spec *) .
* replace (2 * S k)%nat with (S (S (2 * k)))%nat in Hlen by ring.
  destruct l as [| a [| b l']]; try discriminate.
  destruct (@not_nil_last _ (b :: l') ltac:(discriminate)) as [z [l Hl]].
  rewrite Hl in *. clear Hl b l'. rewrite half1_cons2.
  assert (Hdup : ~List.In a l /\ ~List.In z l /\ NoDup l /\ a <> z).
  { inversion_clear Hnodup as [| ? ? Hin Hnodup'].
    rewrite <- NoDupA_Leibniz, NoDupA_app_iff in Hnodup'; refine _.
    destruct Hnodup' as [? [? Hnodup']]. repeat split.
    - intuition.
    - intro Hz. setoid_rewrite InA_Leibniz in Hnodup'. apply (Hnodup' z); intuition.
    - now rewrite <- NoDupA_Leibniz.
    - rewrite in_app_iff in Hin. intro Heq. subst. intuition. }
  destruct Hdup as [Hal [Hzl [Hl Haz]]].
  assert (Hlen' : (length l = 2 * k)%nat).
  { simpl in Hlen. rewrite app_length in Hlen. simpl in *. lia. }
  cbn [map]. rewrite map_app. cbn [map].
   destruct (in_dec Geq_dec a (a :: half1 l)) as [_ | Habs].
   destruct (in_dec Geq_dec z (a :: half1 l)) as [Habs | _].
  + inversion_clear Habs; try (now elim Haz); [].
    exfalso. now apply Hzl, half1_incl.
  + rewrite (map_ext_in _ (fun x => if in_dec Geq_dec x (half1 l) then pt1 else pt2)).
    - cbn [countA_occ]. rewrite countA_occ_app. rewrite IHk; trivial.
      assert (Hneq : pt2 =/= pt1) by intuition.
      cbn [countA_occ].
      destruct (pt1 =?= pt) as [Heq1 | ?], (pt2 =?= pt) as [Heq2 | ?];
      rewrite ?Heq1, ?Heq2, ?add_same, ?add_other, ?singleton_same, ?singleton_other;
      trivial; ring || (try (intro; auto)).
    - intros x Hin.
      destruct (in_dec Geq_dec x (half1 l)) as [Hx | Hx],
               (in_dec Geq_dec x (a :: half1 l)) as [Hx' | Hx']; trivial.
      -- elim Hx'. intuition.
      -- inversion_clear Hx'; subst; contradiction.
  + elim Habs. intuition.
Qed.

Theorem obs_config1 : !! config1 == observation1.
Proof using n_non_0.
intro pt. unfold config1, observation1.
rewrite obs_from_config_spec, config_list_spec. cbn [fst].
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_app, map_map, map_map, map_cst, map_app, map_map, map_alls, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
rewrite (map_ext_in _ (fun x => if left_dec x then 0%R else 1%R)); auto; [].
unfold left_dec, left. rewrite (obs_config_aux H01 _ nB).
+ destruct (pt =?= 0) as [Heq | Hneq]; [| destruct (pt =?= 1) as [Heq | ?]].
  - hnf in Heq. subst. rewrite countA_occ_alls_in; autoclass; [].
    repeat rewrite add_same, singleton_other; trivial; simpl; [].
    Local Transparent B. simpl.
    rewrite enum_length. lia.
    Local Opaque B.
  - hnf in Heq. subst. rewrite countA_occ_alls_out; autoclass; [].
    repeat rewrite add_other, singleton_same; trivial; []. lia.
  - rewrite countA_occ_alls_out; auto; [].
    now repeat rewrite add_other, singleton_other.
+ apply Gnames_NoDup.
+ rewrite Gnames_length. reflexivity.
Qed.

Theorem obs_config2 : !! config2 == observation2.
Proof using n_non_0.
intro pt. unfold config2, observation2.
rewrite obs_from_config_spec, config_list_spec. cbn [fst].
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_map, map_app, map_map, map_map, map_cst, countA_occ_app.
assert (H01 : 0 <> 1) by auto.
rewrite (map_ext_in _ (fun x => if left_dec x then 0%R else 1%R)); auto; [].
unfold left_dec, left. rewrite (obs_config_aux H01 _ nB).
+ destruct (pt =?= 0) as [Heq | Hneq]; [| destruct (pt =?= 1) as [Heq | Hneq']].
  - hnf in Heq. subst. rewrite countA_occ_alls_out; auto.
    repeat rewrite add_same, singleton_other; trivial; []. lia.
  - hnf in Heq. subst. rewrite countA_occ_alls_in; autoclass; [].
    repeat rewrite add_other, singleton_same; trivial; [].
    rewrite Bnames_length. simpl. lia.
  - rewrite countA_occ_alls_out; auto; [].
    now repeat rewrite add_other, singleton_other.
+ apply Gnames_NoDup.
+ rewrite Gnames_length. reflexivity.
Qed.

Definition swap (pt : location) := translation (opp pt) ∘ (homothecy pt minus_1).

Instance swap_compat : Proper (equiv ==> equiv) swap.
Proof using . intros pt pt' Hpt x. simpl. rewrite Hpt. ring. Qed.

Lemma swap_obs2_obs1 : MMultisetExtraOps.map (swap 1) observation2 == observation1.
Proof using .
intro pt. unfold observation1, observation2, swap. rewrite map_add, map_singleton; autoclass; [].
cbn -[add singleton].
ring_simplify (1 + -1 * (0 + -(1)) + -(1)).
ring_simplify (1 + -1 * (1 + -(1)) + -(1)).
destruct (Rdec pt 0); [| destruct (Rdec pt 1)]; subst;
repeat rewrite ?add_same, ?singleton_same, ?singleton_other, ?add_other; auto.
Qed.

(** An execution alternating config1 and config2 *)
Definition exec : execution := Stream.alternate config1 config2.

(** The demon defeating any robogram *)

Definition activate1 (id : ident) :=
  match id with
    | Good g => if left_dec g then true else false
    | Byz b => true
  end.

Definition change_frame1 config g : similarity location :=
  translation (opp (get_location (config (Good g)))).

Definition bad_da1 : demonic_action.
refine {|
  activate := activate1;
  relocate_byz := fun _ _ => 1;
  change_frame := change_frame1;
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt |}.
Proof.
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (unfold change_frame1; intros ? ? Heq ? ? ?; subst; now rewrite Heq).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
Defined.

Definition activate2 (id : ident) :=
  match id with
    | Good g => if left_dec g then false else true
    | Byz b => true
  end.

Definition bad_da2 : demonic_action.
simple refine {|
  activate := activate2;
  relocate_byz := fun _ _ => 0;
  change_frame := fun config g => swap (get_location (config (Good g)));
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt |}; autoclass.
Proof.
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (intros ? ? Heq ? ? ?; subst; now rewrite Heq).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
Defined.

Definition bad_demon : demon := Stream.alternate bad_da1 bad_da2.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof using .
cofix cofx.
constructor; [| constructor].
* intros [g1 | b1] id2; [destruct (left_dec g1) |].
  + apply kReset. simpl. now destruct (left_dec g1).
  + destruct id2 as [g2 | b2]; [destruct (left_dec g2) |].
    - apply kReduce; simpl.
      -- now destruct (left_dec g1).
      -- now destruct (left_dec g2).
      -- apply kReset. simpl. now destruct (left_dec g1).
    - apply kStall; simpl.
      -- now destruct (left_dec g1).
      -- now destruct (left_dec g2).
      -- apply kReset. simpl. now destruct (left_dec g1).
    - apply kReduce; simpl.
      -- now destruct (left_dec g1).
      -- reflexivity.
      -- apply kReset. simpl. now destruct (left_dec g1).
  + apply kReset. reflexivity.
* intros [g1 | b1] id2; [destruct (left_dec g1) |].
  + destruct id2 as [g2 | b2]; [destruct (left_dec g2) |].
    - apply kStall; simpl.
      -- now destruct (left_dec g1).
      -- now destruct (left_dec g2).
      -- apply kReset. simpl. now destruct (left_dec g1).
    - apply kReduce; simpl.
      -- now destruct (left_dec g1).
      -- now destruct (left_dec g2).
      -- apply kReset. simpl. now destruct (left_dec g1).
    - apply kReduce; simpl.
      -- now destruct (left_dec g1).
      -- reflexivity.
      -- apply kReset. simpl. now destruct (left_dec g1).
  + apply kReset. simpl. now destruct (left_dec g1).
  + apply kReset. reflexivity.
* simpl. assumption.
Qed.

Corollary Fair_bad_demon : Fair bad_demon.
Proof using . apply kFair_Fair with 1%nat; autoclass. apply kFair_bad_demon. Qed.

Corollary kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof using .
intros.
eapply kFair_mono with 1%nat.
- apply kFair_bad_demon; auto.
- auto.
Qed.

(** From now on and until the final theorem we consider a given robogram [r].
    We now prove that [r] does not move in some observation. *)
Section PropRobogram.

Variable r : robogram.
Hypothesis sol : solution r.

(** In any observation containing a tower of size at least [nG], the robogram does not make robots
    move.  Indeed, otherwise they all go to the same location and we can build a demon that shift
    byzantine robots by the same amount in order to get the same translated configuration. *)

Definition shifting_da (pt : R) : demonic_action.
simple refine {| activate := fun _ => true;
                 relocate_byz := fun _ _ => pt;
                 change_frame := fun config g => translation (opp (get_location (config (Good g))));
                 choose_update := fun _ _ _ => tt;
                 choose_inactive := fun _ _ => tt |}; autoclass.
Proof.
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
+ abstract (intros ? ? Heq ? ? ?; subst; now rewrite Heq).
+ abstract (now repeat intro).
+ abstract (now repeat intro).
Defined.

(** A demon that shifts byzantine robots by d each round. *)
CoFixpoint shifting_demon d pt :=
  Stream.cons (shifting_da (pt + d + 1)) (shifting_demon d (pt + d)).

Lemma Fair_shifting_demon : forall d pt, Fair (shifting_demon d pt).
Proof using .
intros d pt. apply FSYNC_implies_fair; autoclass; []. revert pt.
cofix shift_fair. intro pt. constructor.
+ repeat intro. simpl. reflexivity.
+ cbn. apply shift_fair.
Qed.

(** The configuration that will be shifted **)
Definition config0 pt : configuration := fun id =>
  match id with
    | Good _ => pt
    | Byz b => pt + 1
  end.

(** An execution that shifts by [d] at each round, starting from [pt]. *)
CoFixpoint shifting_execution d pt := Stream.cons (config0 pt) (shifting_execution d (pt + d)).

Lemma observation_config0 : forall pt : location,
  @equiv observation _
    (!! (map_config (lift (existT precondition (translation (opp pt)) I)) (config0 pt)))
    observation1.
Proof using .
intros pt x. unfold config0, observation1.
rewrite obs_from_config_spec, config_list_spec.
change names with (map Good Gnames ++ map Byz Bnames).
rewrite map_map, map_app, map_map, map_map, countA_occ_app.
rewrite (map_ext_in _ (fun _ : G => 0)), (map_ext_in _ (fun _ : B => 1)).
+ do 2 rewrite map_cst.
  destruct (equiv_dec x 0) as [Hx | Hnx]; [| destruct (equiv_dec x 1) as [Hx | Hnx']].
  - rewrite Hx, countA_occ_alls_in, Gnames_length; autoclass.
    rewrite countA_occ_alls_out; auto.
    rewrite add_same, singleton_other; auto.
  - rewrite Hx, countA_occ_alls_in, Bnames_length; autoclass.
    rewrite countA_occ_alls_out; auto.
    rewrite add_other, singleton_same; auto.
  - repeat rewrite countA_occ_alls_out; auto.
    rewrite add_other, singleton_other; auto.
+ intros b Hin. unfold map_config. rewrite get_location_lift. compute. ring.
+ intros g Hin. unfold map_config. rewrite get_location_lift. compute. ring.
Qed.

Corollary obs_config0_0 : !! (config0 0) == observation1.
Proof using .
rewrite <- (observation_config0 0). f_equiv. simpl lift.
rewrite <- map_config_id at 1. f_equiv.
intros ? ? Heq. rewrite Heq. unfold id. simpl in *. field.
Qed.


Section AbsurdMove.
Definition move := r observation1.
Hypothesis absurdmove : move <> 0.

Lemma round_move : forall pt,
  round r (shifting_da (pt + move + 1)) (config0 pt) == config0 (pt + move).
Proof using .
intros pt id. unfold round. cbn -[fst obs_from_config].
destruct id as [g | b].
- assert (Htranslate := observation_config0 pt).
  ring_simplify (pt + - pt). rewrite Ropp_involutive.
  simpl map_config in *. unfold id in *.
  apply (pgm_compat r) in Htranslate. rewrite Htranslate. unfold move. simpl. ring.
- reflexivity.
Qed.

Lemma keep_moving_by_eq : forall pt config,
  config == config0 pt -> execute r (shifting_demon move pt) config == shifting_execution move pt.
Proof using .
cofix shift_exec. intros pt config Heq.
constructor.
+ simpl. assumption.
+ simpl. apply shift_exec. now rewrite <- round_move, Heq.
Qed.

Theorem keep_moving : forall pt,
  execute r (shifting_demon move pt) (config0 pt) == shifting_execution move pt.
Proof using . intro. apply keep_moving_by_eq. reflexivity. Qed.

Theorem absurd : False.
Proof using absurdmove n_non_0 sol.
assert (Hthird_move : 0 < Rabs (move / 3)). { apply Rabs_pos_lt. lra. }
specialize (sol (config0 0) (Fair_shifting_demon move 0) Hthird_move).
destruct sol as [pt Hpt]. rewrite keep_moving in Hpt.
remember (shifting_execution move 0) as e. remember (Rabs (move / 3)) as ε.
revert Heqe. generalize 0.
induction Hpt as [e IHpt | e IHpt]; intros start Hstart.
+ subst e ε. destruct IHpt as [Hnow1 [Hnow2 Hlater]]. cbn in *.
  clear -absurdmove Hnow1 Hnow2 n_non_0. specialize (Hnow1 gfirst). specialize (Hnow2 gfirst).
  cut (Rabs move <= Rabs (move / 3) + Rabs (move / 3)).
  - assert (Hpos : 0 < Rabs move) by now apply Rabs_pos_lt.
    unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv; try lra.
    assert (Habs3 : Rabs 3 = 3). { apply Rabs_pos_eq. lra. } rewrite Habs3 in *.
    lra.
  - rewrite sqrt_square in Hnow1, Hnow2.
    replace move with ((pt - start) - (pt - (start + move))) at 1 by ring.
    unfold Rminus at 1. eapply Rle_trans; try (now apply Rabs_triang); [].
    apply Rplus_le_compat; trivial; []. now rewrite Rabs_Ropp.
+ apply (IHIHpt (start + move)). subst e. simpl. reflexivity.
Qed.

End AbsurdMove.

Theorem no_move1 : r observation1 = 0.
Proof using n_non_0 sol.
destruct (Rdec (r observation1) 0) as [? | Hmove]; trivial.
exfalso. apply absurd. assumption.
Qed.

Corollary no_move2 : r (!! (map_config (swap 1) config2)) == 0.
Proof using n_non_0 sol.
setoid_rewrite <- no_move1 at 2.
apply (pgm_compat r). f_equiv.
change (Bijection.section (swap 1)) with (lift (existT precondition (swap 1) I)).
replace origin with ((lift (existT precondition (swap 1) I)) 1) by (compute; ring).
rewrite <- (obs_from_config_map (f := swap 1)); autoclass; [].
rewrite obs_from_config_ignore_snd, obs_config2.
apply swap_obs2_obs1.
Qed.

Lemma round_config1 : round r bad_da1 config1 == config2.
Proof using n_non_0 sol.
intros id. unfold round.
simpl (activate bad_da1). unfold activate1.
destruct id as [g | b]; try reflexivity; [].
destruct (left_dec g) as [Hleft | Hright]; try reflexivity; [].
cbn -[obs_from_config config1 config2 translation]. unfold change_frame1, id.
assert (Hg1 : config1 (Good g) = 0) by (unfold config1; destruct_match; auto; contradiction).
assert (Hg2 : config2 (Good g) = 0) by (unfold config2; destruct_match; auto; contradiction).
rewrite Hg1, Hg2. change (opp (get_location 0)) with (- 0).
rewrite Ropp_0. rewrite Similarity.translation_origin. cbn.
rewrite obs_config1. apply no_move1.
Qed.

Lemma round_config2 : round r bad_da2 config2 == config1.
Proof using n_non_0 sol.
intros id. unfold round.
simpl (activate bad_da2). unfold activate2.
destruct id as [g | b]; try reflexivity; [].
destruct (left_dec g) as [Hleft | Hright]; try reflexivity; [].
cbn -[swap map_config]. unfold id.
assert (Hg1 : config1 (Good g) = 1) by (unfold config1; destruct_match; auto; contradiction).
assert (Hg2 : config2 (Good g) = 1) by (unfold config2; destruct_match; auto; contradiction).
rewrite Hg1, Hg2, obs_from_config_ignore_snd, no_move2.
simpl. ring.
Qed.

Theorem execute_bad_demon : execute r bad_demon config1 == exec.
Proof using n_non_0 sol.
cut (forall e, execute r bad_demon config1 == e -> e == exec); auto.
cofix exec. intros e He; constructor; [| constructor].
+ rewrite <- He. unfold Stream.instant2. simpl. now split.
+ rewrite <- He. simpl. apply round_config1.
+ apply exec. rewrite <- He.
  change (Stream.tl (Stream.tl (execute r bad_demon config1)))
    with (execute r bad_demon (round r bad_da2 (round r bad_da1 config1))).
  apply execute_compat; auto; []. rewrite <- round_config2 at 1.
  apply round_compat; try reflexivity; []. now rewrite round_config1.
Qed.

End PropRobogram.


(***********************)
(** *  Final theorem  **)
(***********************)

(** A 2-step induction scheme for attracted. *)
Definition attracted_ind2 (c : R) (r : R) (P : execution → Prop)
  (P0 : ∀ e : execution, imprisoned c r e → P e)
  (P1 : ∀ e : execution, imprisoned c r (Stream.tl e) → P e)
  (Ps : ∀ e : execution, attracted c r (Stream.tl (Stream.tl e)) →
                         P (Stream.tl (Stream.tl e)) → P e)
  := fix F (e : execution) (a : attracted c r e) {struct a} : P e :=
    match a with
      | Stream.Now i => P0 e i
      | Stream.Later (Stream.Now i) => P1 e i
      | Stream.Later (Stream.Later a') => Ps e a' (F (Stream.tl (Stream.tl e)) a')
    end.

Theorem noConvergence : forall r, ~solution r.
Proof using n_non_0.
intros r Hr.
assert (Hpos : 0 < 1/4) by lra.
destruct (Hr config1 bad_demon Fair_bad_demon _ Hpos) as [pt Hpt].
rewrite execute_bad_demon in Hpt; trivial.
revert Hpt. cut (exec == exec); try reflexivity. generalize exec at -2. intros e He Hpt.
induction Hpt using attracted_ind2.
+ (* First step *)
  rewrite He in H. inversion H as [Habs _].
  assert (Hfirst := Habs gfirst). assert (Hlast := Habs glast).
  simpl get_location in *. unfold id, config1 in *.
  pose (gfirst_left). pose (glast_right).
  destruct (left_dec gfirst); try contradiction.
  destruct (left_dec glast).
  - now apply (left_right_exclusive glast).
  - clear -Hfirst Hlast. cut (1 <= 1/4 + 1/4). lra.
    replace 1 with ((pt - 0) + (1 - pt)) at 1 by ring.
    setoid_rewrite <- Rabs_pos_eq at 1; try lra; [].
    eapply Rle_trans; try (now apply Rabs_triang); [].
    simpl dist in *. rewrite sqrt_square in *.
    apply Rplus_le_compat; assumption || now rewrite Rabs_minus_sym.
+ (* Second step, same proof *)
  rewrite He in H. inversion H as [Habs _].
  assert (Hfirst := Habs gfirst). assert (Hlast := Habs glast).
  simpl get_location in *. unfold id, config2 in *.
  pose (gfirst_left). pose (glast_right).
  destruct (left_dec gfirst); try contradiction.
  destruct (left_dec glast).
  - now apply (left_right_exclusive glast).
  - clear -Hfirst Hlast. cut (1 <= 1/4 + 1/4); try lra; [].
    replace 1 with ((pt - 0) + (1 - pt)) at 1 by ring.
    setoid_rewrite <- Rabs_pos_eq at 1; try lra; [].
    eapply Rle_trans; try (now apply Rabs_triang); [].
    simpl dist in *. rewrite sqrt_square in *.
    apply Rplus_le_compat; assumption || now rewrite Rabs_minus_sym.
+ (* Inductive step *)
  apply IHHpt. rewrite He. reflexivity.
Qed.

End ConvergenceImpossibility.

(* Do not leave this here, because it makes "make vos" fail.
 It is done in Impossiblity_2G_1B_Assumptions.v instead *)
(* Print Assumptions noConvergence. *)
