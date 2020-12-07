(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain               
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Require Import Utf8.
Require Import List SetoidList.
Require Import Decidable.
Require Import Setoid Equalities Morphisms.
Require Import Compare_dec FinFun.
Require Import ZArith Arith_base Arith.Div2 Lia Psatz.
Require Import Pactole.CaseStudies.Exploration.Definitions.


Open Scope list_scope.
Set Implicit Arguments.
Typeclasses eauto := (bfs).

Section Tower.

(** Given an abitrary ring *)
Context {RR : RingSpec}.
(** There are kG good robots and no byzantine ones. *)
Variable kG : nat.
Instance Robots : Names := Robots kG 0.

(** Assumptions on the number of robots: it is non zero and strictly divides the ring size. *)
Hypothesis kdn : (ring_size mod kG = 0)%nat.
Hypothesis k_inf_n : (kG < ring_size)%nat.
(*Hypothesis k_sup_1 : (1 < kG)%nat.*)

(** There is no byzantine robot so we can simplify properties about identifiers and configurations. *)
(* TODO: put properties with no byz into a file Models/NoByzantine.v *)
Lemma no_byz : forall (id : ident) P, (forall g, P (Good g)) -> P id.
Proof using k_inf_n (*k_sup_1*) kdn.
intros [g | b] P HP.
+ apply HP.
+ destruct b. lia.
Qed.

(** A dummy state used for (inexistant) byzantine robots. *)
Definition origin : location := of_Z 0.
Definition dummy_val : location := origin. (* could be anything *)

Notation "!! config" := (@obs_from_config _ _ _ _ multiset_observation config origin) (at level 0).
Notation execute := (execute (UpdFun := UpdFun)).

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, config1 (Good g) == config2 (Good g)) -> config1 == config2.
Proof using k_inf_n (*k_sup_1*) kdn. intros config1 config2 Heq id. apply (no_byz id). intro g. apply Heq. Qed.

(** In order to prove that at least one position is occupied, we define the list of positions. *)
Definition Vlist := Identifiers.enum ring_size.

Lemma Vlist_NoDup : NoDupA equiv Vlist.
Proof using . rewrite NoDupA_Leibniz. apply enum_NoDup. Qed.

Lemma Vlist_length : length Vlist = ring_size.
Proof using . apply enum_length. Qed.

(** As there is strictly less robots than location, there is an empty location. *)
Lemma ConfigExistsEmpty : forall config, ¬ (∀ pt, In pt (!! config)).
Proof using k_inf_n (*k_sup_1*) kdn.
generalize k_inf_n; intros Hkin config Hall.
assert (Hsize : size (!! config) < ring_size).
{ apply le_lt_trans with (cardinal (!! config)).
  - apply size_cardinal.
  - cut (cardinal (!! config) = kG); try lia; [].
    change (cardinal (make_multiset (List.map get_location (config_list config))) = kG).
    rewrite cardinal_make_multiset, config_list_spec, map_map, map_length.
    rewrite names_length. simpl. lia. }
assert (Hle : ring_size <= size (!! config)).
{ rewrite size_spec.
  assert (Hobs : forall pt, InA equiv pt (support (!! config))).
  { intro pt. specialize (Hall pt). now rewrite support_spec. }
  rewrite <- Vlist_length.
  apply (Preliminary.inclA_length setoid_equiv).
  - apply Vlist_NoDup.
  - repeat intro. apply Hobs. }
lia.
Qed.

Lemma Stopped_same : forall e, Stopped e -> e == Stream.tl e.
Proof using .
cofix Hcoind. intros e Hstop. constructor.
+ clear Hcoind. apply Hstop.
+ apply Hcoind. apply Hstop.
Qed.

Lemma Will_stop_tl : forall e, Will_stop e -> Will_stop (Stream.tl e).
Proof using .
intros e He. induction He.
+ left. match goal with H : Stopped _ |- _ => apply H end.
+ right. apply IHHe.
Qed.

(** No algorithm can stop on a starting configuration. *)
Theorem no_stop_on_starting_config : forall r d config,
  Fair d ->
  Explore_and_Stop r ->
  Valid_starting_config config ->
  ~Stopped (execute r d config).
Proof using k_inf_n (*k_sup_1*) kdn.
intros r d config.
generalize (@reflexivity execution equiv _ (execute r d config)).
generalize (execute r d config) at -2.
intros e Heqe Hfair Hsol Hvalid Hsto.
destruct (Hsol d config Hfair Hvalid) as [Hvisit Hstop].
assert (Hfalse :=  ConfigExistsEmpty config).
(* TODO: remove the use of classical logic: everything is decidable here *)
apply Logic.Classical_Pred_Type.not_all_ex_not in Hfalse.
destruct Hfalse as [loc Hfalse].
specialize (Hvisit loc).
rewrite <- Heqe in *.
induction Hvisit.
+ rewrite Heqe in *.
  match goal with H : Stream.instant _ _ |- _ => destruct H as [g Hg] end.
  rewrite (obs_from_config_In config origin) in Hfalse;
    destruct Hfalse.
  exists (Good g).
  apply Hg.
+ apply IHHvisit.
  - rewrite <- Heqe. symmetry. now apply Stopped_same.
  - apply Hsto.
  - now apply Will_stop_tl.
Qed.

(** In particular, there is a tower on any final configuration. *)
Lemma tower_on_final_config : forall r d config,
  Fair d ->
  Explore_and_Stop r ->
  Stopped (execute r d config) ->
  exists loc, ((!! config)[loc] > 1)%nat.
Proof using k_inf_n (*k_sup_1*) kdn.
intros r d config Hfair Hsol Hstop.
assert (Hequiv := @no_stop_on_starting_config r d config Hfair Hsol).
assert (Hvalid : ~Valid_starting_config config) by tauto.
apply config_not_injective in Hvalid.
destruct Hvalid as [id [id' [Hid Heq]]].
exists (config id).
assert (Hobs := obs_from_config_spec config origin (config id)).
assert (Hperm : exists l, PermutationA equiv (config_list config) (config id :: config id' :: l)).
{ assert (Hin : List.In id names) by apply In_names.
  assert (Hin' : List.In id' names) by apply In_names.
  assert (Hperm : exists l, PermutationA eq names (id :: id' :: l)).
  { rewrite <- InA_Leibniz in Hin, Hin'.
    apply PermutationA_split in Hin; autoclass; [].
    destruct Hin as [l' Hperm']. rewrite Hperm', InA_cons in Hin'.
    destruct Hin' as [| Hin']; try congruence; [].
    apply PermutationA_split in Hin'; autoclass; [].
    destruct Hin' as [l Hperm]. exists l. now rewrite Hperm', Hperm. }
  destruct Hperm as [l Hperm].
  exists (List.map config l).
  now rewrite config_list_spec, Hperm. }
destruct Hperm as [l Hperm].
rewrite Hobs.
(* FIXME: why does [rewrite Hperm] fail here? *)
rewrite (countA_occ_compat _ equiv_dec _ _ (reflexivity (config id))
          (PermutationA_map _ _ Hperm)).
simpl List.map. rewrite List.map_id. unfold Datatypes.id. simpl.
repeat destruct_match; solve [lia | exfalso; auto].
Qed.

Lemma exec_stopped r : forall d c, Fair d -> Will_stop (execute r d c) ->
  exists d' c', Fair d'/\ Stopped (execute r d' c').
(*exists e, exec_r_comp e r /\ Stopped e.*)
Proof using .
intros d' config' Hfair Hstop.
remember (execute r d' config') as e'.
revert Heqe'.
revert d' config' Hfair.
induction Hstop as [e' Hstop | e' Hstop IHstop].
+ intros d' config' Hfair Heq.
  exists d', config'; now rewrite Heq in *.
+ intros d' config' Hfair Heq.
  apply (IHstop (Stream.tl d') (Stream.hd (Stream.tl e'))).
  - destruct Hfair as [_ Hfair]. constructor; apply Hfair.
  - now rewrite Heq, execute_tail.
Qed.

Lemma no_exploration_k_inf_2 : forall r d config,
  Fair d ->
  Explore_and_Stop r ->
  Valid_starting_config config ->
  (kG > 1)%nat.
Proof using k_inf_n (*k_sup_1*) kdn.
intros r d config Hfair Hsol Hvalid.
assert (Hexr := exec_stopped r).
assert (Htower := tower_on_final_config).
destruct (Hsol d config Hfair Hvalid) as [Hvisit Hstop].
destruct (Hexr d config Hfair Hstop) as [d' [config' [Hfair' Hstop']]].
specialize (Htower r d' config' Hfair' Hsol Hstop').
destruct Htower.
assert (Hcard := cardinal_lower x (!! config')).
rewrite cardinal_obs_from_config in Hcard.
unfold nG, nB in *.
unfold Robots in *. simpl in *. lia.
Qed.

End Tower.

(* Prefer not to leave this here, so that make -vos does not fail here.
See Tower_Assumptions.v *)
(* Print Assumptions no_exploration_k_inf_2. *)

(*
(** Stronger result: in any successful sequential execution,
    the last starting configuration was seen at least [ring_size - kG + 1] rounds ago. *)

Fixpoint last_init_conf (l : list configuration) (a : configuration) :=
  match l with
  | nil => (False, nil)
  | config :: l' => if a =?= config
                    then (((List.Forall (fun x => ~ Valid_starting_config x ) l')
                          /\ Valid_starting_config a),l')
                    else last_init_conf l' a
  end.

(* Definition SequencialExecution (e : execution) : Prop :=
  Stream.forever
    (fun e' => forall r d conf,
         e' == execute r d conf /\
         (exists id, forall id', id' <> id /\ step (Stream.hd d) id' (conf id')
                                              = Moving false)) e. *)
Definition SequencialExecution : execution -> Prop :=
  Stream.forever (Stream.instant
    (fun config => forall da, exists id, forall id', id' <> id -> activate da id' = false)).

Fixpoint Biggest_list_of_exe (l : list configuration) (e : execution) : Prop :=
  match l with
  | nil => Stopped e
  | x :: nil => x == Stream.hd e /\ Stopped e
  | x :: y => x == Stream.hd e /\ ~ Stream.hd e == Stream.hd (Stream.tl e)
                               /\  Biggest_list_of_exe y (Stream.tl (Stream.tl e))
  end.

(* Lemma stop_tl : forall e, Stopped e -> Stopped (Stream.tl e).
Proof. intros e He. apply He. Qed. *)

Theorem TowerOnFinalConf : forall l r d config (e : execution) x,
    Valid_starting_config config ->
    e == execute r d config ->
    Biggest_list_of_exe l e ->
    let (P, l') := last_init_conf l config in
    P ->
    Explore_and_Stop r ->
    SequencialExecution e ->
    (forall config, List.In config l' ->
       exists pt, (!! config)[pt] = x -> (1 < x)%nat  -> (x < kG)%nat) ->
    (ring_size - kG + 1 <= length l')%nat.
Proof.
intros l r d config e x Hconfig Heq_e Hlist.
destruct (last_init_conf l config) as (P, l') eqn : Hlic.
intros HP Hvalid Hsequ Hl_conf.
assert ((length l' < ring_size - kG + 1)%nat
       -> False).
{ intros Hf.
  unfold last_init_conf in Hlic.
  induction l.
  * simpl in *.
    rewrite surjective_pairing in Hlic.
    simpl in *.
    assert (P = fst (P, l')) by intuition.
    rewrite <- Hlic in *.
    simpl in *.
    now rewrite <- H.
  * destruct (config =?=  a).
    + assert (HeqP : P = fst (P, l')) by intuition.
      assert (l' = snd (P, l')) by intuition.
      rewrite <- Hlic in *; cbn -[equiv] in *.
      rewrite HeqP in HP.
      intuition.
      assert (Valid_starting_config a).
      { revert_one @equiv. intro Heq. now rewrite <- Heq. }
      destruct (last_init_conf l) eqn : Hl.
      
    split.
    - intros.
      destruct Hsequ.
      specialize (H0 r d conf). 
      destruct H0 as (He_conf, (id,Hid)).
      destruct l eqn : Hl.
    - simpl in *.
      destruct (Hvalid c Hconf) as (Hvisit, Hstop).
      assert (Hfalse :=  ConfExistsEmpty c).
      unfold is_visited in *.
      rewrite Heq_e in Hlist.
      now generalize (test Hvalid Heq_e Hconf Hlist).
    - destruct l0 eqn : Hl'.
       + simpl in *.
         destruct Hlist as (Hceq, Hstp).
         generalize (test Hvalid Heq_e Hconf).
         intros Htest.
         assert (Hval_t: ValidStartingConf t).
         rewrite Hceq.
         rewrite Heq_e.
         now simpl in *.
         assert (He_eq : eeq e (execute r d t)).
         rewrite Hceq.
         now rewrite Heq_e.
         generalize (test Hvalid He_eq Hval_t).
         intros Htest'.
         destruct Htest.
         now rewrite <- Heq_e.
       + destruct (Classical_Prop.classic (ValidStartingConf (last (t :: t0 :: l1) c)))
           as [Hv|Hnv].
         simpl in *.
         destruct ( Config.eq_dec (Stream.hd e) (Stream.hd (Stream.tl (Stream.tl e))));
           try easy.
         destruct Hlist as (Hceq, Hlist).
         assert (Hse : ~Stopped e).
         intros Hs.
         destruct Hs as (Hse, Hs).
         now unfold stop_now in Hse.
         destruct l1.
         * destruct (Classical_Prop.classic
                       (ValidStartingConfSolExplorationStop
                       r (Stream.tl (Stream.tl d)))) as [Hvrd|Hnvrd].
           assert (Heeq_to : eeq (Stream.tl (Stream.tl e)) (execute r (Stream.tl (Stream.tl d)) t0)).
           { rewrite Heq_e.
             destruct Hlist as (Hlist, Hstp).
             rewrite Heq_e in Hlist.
             repeat rewrite execute_tail in *.
             apply execute_compat; try easy.
           }
           destruct (test Hvrd Heeq_to Hv).
           now rewrite <- Heeq_to.
           unfold ValidStartingConfSolExplorationStop in *.
           apply Classical_Prop.NNPP.
           intro.
           apply Hnvrd.
           intros.
           destruct (Hvrd t0 Hv).  Heeq_to).
           admit.
         apply Classical_Pred_Type.not_all_not_ex.
         intros Hf.
         destruct Hnv.
         unfold ValidStartingConf.
         intros (ex, Hex).
         now specialize (Hf ex).
Qed.
 *)
