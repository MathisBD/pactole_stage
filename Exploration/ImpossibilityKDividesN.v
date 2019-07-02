(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, R. Pelle, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Psatz Rbase.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid SetoidList Compare_dec Morphisms.
Require Import Pactole.Exploration.Definitions.


Open Scope Z_scope.
Set Implicit Arguments.
Typeclasses eauto := (bfs).


Section Exploration.

(** Given an abitrary ring *)
Context {RR : RingSpec}.
(** There are kG good robots and no byzantine ones. *)
Variable kG : nat.
Instance Robots : Names := Robots kG 0.

(** Assumptions on the number of robots: it is non zero, less than and divides the ring size. *)
Hypothesis kdn : (ring_size mod kG = 0)%nat.
Hypothesis k_inf_n : (kG < ring_size)%nat.
Hypothesis k_sup_1 : (1 < kG)%nat.

(** There is no byzantine robot so we can simplify properties
    about identifiers and configurations. *)
Lemma no_byz : forall (id : ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. omega.
Qed.

(** A dummy state used for (inexistant) byzantine robots. *)
Definition origin : location := of_Z 0.
Definition dummy_val : location := origin. (* could be anything *)

Existing Instance setting.
Notation "!! config" := (spect_from_config config origin) (at level 0).

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, config1 (Good g) == config2 (Good g)) -> config1 == config2.
Proof. intros config1 config2 Heq id. apply (no_byz id). intro g. apply Heq. Qed.


(** Let us consider an arbirary robogram. *)
Variable r : robogram.

(** The key idea is to prove that we can always make robots think that there are
    in the same configuration.  Thus, is they move at all, then they will never stop.
    If they do not move, they do not explore the ring.
    The configuration to which we will always come back is [ref_config],
    in which robots are evenly spaced on the ring.  *)

(** ***  Definition of the reference configuration and demon used in the proof  **)

Definition create_ref_config (g : G) : location :=
  Ring.of_Z (Z_of_nat (proj1_sig g * (ring_size / kG))).

(** The starting configuration where robots are evenly spaced:
    each robot is at a distance of [ring_size / kG] from the previous one,
    starting from the origin. *)
Definition ref_config : configuration :=
  fun id => match id with
              | Good g => create_ref_config g
              | Byz b => dummy_val
            end.

Lemma ref_config_injective :
  Util.Preliminary.injective eq equiv (fun id => get_location (ref_config id)).
Proof.
intros id1 id2.
assert (ring_size / kG <> 0)%nat by (rewrite Nat.div_small_iff; omega).
apply (no_byz id2), (no_byz id1). clear id1 id2.
intros g1 g2 Heq. f_equal. hnf in Heq.
unfold ref_config, create_ref_config, Ring.of_Z in *. simpl in *.
apply (f_equal to_Z) in Heq. unfold to_Z in Heq. simpl in Heq.
rewrite 2 Z2Nat.id in Heq; try (apply Z.mod_pos_bound; lia); [].
assert (Hlt : forall n, (n < kG)%nat -> Z.of_nat (n * (ring_size / kG)) < Z.of_nat ring_size).
{ intros n Hn. apply Nat2Z.inj_lt.
  apply Nat.lt_le_trans with (kG * (ring_size / kG))%nat.
  - apply mult_lt_compat_r; omega.
  - apply Nat.mul_div_le. omega. }
rewrite 2 Z.mod_small in Heq; try (split; apply Zle_0_nat || apply Hlt, proj2_sig); [].
apply Nat2Z.inj, Nat.mul_cancel_r in Heq; auto.
Local Transparent G. unfold G. now apply eq_proj1.
Qed.

(**  Translating [ref_config] by multiples of [ring_size / kG] does not change its spectrum. *)
Lemma spect_trans_ref_config : forall g,
  !! (map_config (Ring.trans (to_Z (create_ref_config g))) ref_config) == !! ref_config.
Proof.
unfold spect_from_config, glob_spect, setting,
       MultisetSpectrum.multiset_spectrum, MultisetSpectrum.make_multiset.
intro g. apply MMultisetFacts.from_elements_compat. (* FIXME: [f_equiv] works but is too long *)
rewrite 2 config_list_spec, 4 map_map.
change (finite_node ring_size) with location.
apply NoDupA_equivlistA_PermutationA; autoclass; [| |].
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros id1 id2 [Heq _]. apply ref_config_injective.
    simpl in Heq. unfold Datatypes.id in *.
    apply (f_equal to_Z) in Heq. rewrite 2 Z2Z in Heq.
    assert (Heq_mod : (to_Z (ref_config id1)) mod Z.of_nat ring_size
                      = (to_Z (ref_config id2)) mod Z.of_nat ring_size).
    { replace (to_Z (ref_config id1))
        with (to_Z (ref_config id1) - to_Z (create_ref_config g)
              + to_Z (create_ref_config g)) by ring.
      rewrite Z.add_mod, Heq, <- Z.add_mod; try omega; []. f_equal. ring. }
    rewrite 2 Z.mod_small in Heq_mod; auto using to_Z_small; [].
    apply to_Z_injective in Heq_mod. now rewrite Heq_mod.
  + rewrite NoDupA_Leibniz. apply names_NoDup.
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros ? ? []. now apply ref_config_injective.
  + rewrite NoDupA_Leibniz. apply names_NoDup.
* intro pt. repeat rewrite InA_map_iff; autoclass; [].
  assert (HkG : kG <> 0%nat) by omega.
  assert (Z.of_nat ring_size <> 0) by omega.
  assert (ring_size / kG <> 0)%nat by (rewrite Nat.div_small_iff; omega).
  assert (Hg : (proj1_sig g < kG)%nat) by apply proj2_sig.
  assert (Hsize : (kG * (ring_size / kG) = ring_size)%nat).
  { symmetry. now rewrite Nat.div_exact. }
  split; intros [id [Hpt _]]; revert Hpt; apply (no_byz id); clear id; intros g' Hpt.
  + assert (Hlt : ((proj1_sig g' + (kG - proj1_sig g)) mod kG < kG)%nat)
      by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    change (fin kG) with G in id'.
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. split; try reflexivity; []. hnf. simpl.
      unfold Datatypes.id, create_ref_config. apply to_Z_injective. rewrite 2 Z2Z.
      (* This part is a proof about modular arithmetic; we stay in Z to use the ring structure *)
      rewrite 2 Ring.Z2Z, <- Zdiv.Zminus_mod.
      unfold id'. simpl.
      rewrite <- Nat.mul_mod_distr_r, Hsize, Zdiv.mod_Zmod, Z.mod_mod; try omega; [].
      rewrite Nat.mul_add_distr_r, Nat2Z.inj_add, 3 Nat2Z.inj_mul, Nat2Z.inj_sub; try omega; [].
      rewrite Z.mul_sub_distr_r, <- (Nat2Z.inj_mul kG), Hsize.
      rewrite Z.add_mod, Zdiv.Zminus_mod, Z.mod_same, Z.add_mod_idemp_r; try omega; [].
      rewrite Zdiv.Zminus_mod. reflexivity.
    - rewrite InA_Leibniz. apply In_names.
  + assert (Hlt : ((proj1_sig g' + proj1_sig g) mod kG < kG)%nat) by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    change (fin kG) with G in id'.
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. split; try reflexivity; []. hnf. simpl.
      unfold Datatypes.id, create_ref_config. apply to_Z_injective. rewrite 2 Z2Z.
      (* This part is a proof about modular arithmetic; we stay in Z to use the ring structure *)
      rewrite 2 Ring.Z2Z, <- Zdiv.Zminus_mod.
      unfold id'. simpl.
      rewrite <- Nat.mul_mod_distr_r, Hsize, Zdiv.mod_Zmod; try omega; [].
      rewrite Zdiv.Zminus_mod_idemp_l. f_equal. lia.
    - rewrite InA_Leibniz. apply In_names.
Qed.

(** The demon activate all robots and shifts their view to be on 0. *)
Program Definition da : demonic_action := {|
  activate := fun id => true;
  relocate_byz := fun _ _ => dummy_val;
  change_frame := fun config g => (to_Z (config (Good g)), false);
  choose_update := fun _ _ _ => tt;
  choose_inactive := fun _ _ => tt |}.
Next Obligation. (* activate_compat *)
now repeat intro.
Qed.
Next Obligation. (* relocate_byz_compat *)
repeat intro. do 2 f_equal. subst. auto.
Qed.
Next Obligation. (* change_frame_compat *)
now repeat intro.
Qed.
Next Obligation. (* choose_update_compat *)
now repeat intro.
Qed.

Definition bad_demon : demon := Stream.constant da.

(** This setting is FFSYNC. *)
Lemma FSYNC_one : FSYNC_da da.
Proof. split. Qed.
Lemma FYSNC_setting : FSYNC bad_demon.
Proof. coinduction Hcoind. apply FSYNC_one. Qed.

(** As all robots see the same spectrum, we take for instance the one at location [origin]. *)
Definition move := pgm r (!! ref_config).
Definition target := move_along origin move.


(** **  First case: robots do not move  **)

(** In this case, the configuration stays exactly the same
    hence there is a location which is not explored. *)

Section NoMove.
Hypothesis Hmove : move == SelfLoop.

Lemma round_id : round r da ref_config == ref_config.
Proof.
rewrite FSYNC_round_simplify; try (now split); [].
apply no_byz_eq. intro g.
cbn -[Ring.trans equiv setting ring_edge map_config].
unfold lift. cbn -[map_config Ring.trans equiv].
rewrite (MultisetSpectrum.spect_from_config_ignore_snd origin).
rewrite spect_trans_ref_config, Hmove. cbn [move_along map_config].
apply Bijection.retraction_section.
Qed.

Lemma NeverVisited_ref_config : forall e,
  e == execute r bad_demon ref_config ->
  exists pt, ~ Will_be_visited pt e.
Proof.
intros e Heq_e. exists (of_Z 1).
intro Hl. induction Hl as [e [g Hvisited] | e Hlater IHvisited].
* (* FIXME: why does [rewrite Heq_e in Hvisited] fail? *)
  rewrite (Stream.hd_compat Heq_e) in Hvisited. simpl in Hvisited.
  apply (f_equal (@proj1_sig _ (fun x => lt x ring_size))) in Hvisited. revert Hvisited.
  assert (1 < ring_size / kG)%nat by (apply <- Nat.div_exact in kdn; nia).
  unfold Ring.of_Z. simpl. rewrite Z.mod_1_l, Z.mod_small; try omega; [|].
  + change 1 with (Z.of_nat 1). rewrite 2 Nat2Z.id. nia.
  + split; try apply Zle_0_nat; [].
    apply inj_lt, Nat.lt_le_trans with (kG * (ring_size / kG))%nat.
    - apply mult_lt_compat_r; try omega; []. apply proj2_sig.
    - rewrite <- Nat.div_exact in kdn; omega.
* apply IHvisited. rewrite Heq_e, execute_tail.
  (* FIXME: why does [f_equiv] fail to find [execute_compat]? *)
  apply execute_compat; auto using round_id.
Qed.

Lemma never_visited : ~(forall pt, Will_be_visited pt (execute r bad_demon ref_config)).
Proof.
intros Hw.
destruct (NeverVisited_ref_config (reflexivity _)) as [pt Hpt].
apply Hpt, Hw.
Qed.

Theorem no_exploration_idle : ~ FullSolExplorationStop r.
Proof.
intros Habs.
specialize (Habs bad_demon).
destruct (Habs ref_config) as [Hexpl _].
now apply never_visited.
Qed.

End NoMove.


(** **  Second case: the robots move  **)

(** ***  Equality of configurations up to translation  **)

(** Translating a configuration. *)
Definition f_config config k : configuration := map_config (trans (- k)) config.

Instance f_config_compat : Proper (equiv ==> equiv ==> equiv) f_config.
Proof.
unfold f_config. repeat intro.
apply map_config_compat; trivial; [].
intros ? ? Heq. now repeat f_equiv.
Qed.

Lemma f_config_merge : forall config k1 k2,
  f_config (f_config config k1) k2 == f_config config (k1 + k2).
Proof.
intros config k1 k2. unfold f_config. rewrite map_config_merge; autoclass; [].
apply no_byz_eq. intro g.
repeat split; simpl. apply to_Z_injective.
repeat rewrite Z2Z, Z.sub_opp_r, ?Zdiv.Zplus_mod_idemp_l.
f_equal. ring.
Qed.

Lemma f_config_swap : forall config k1 k2,
  f_config (f_config config k1) k2 == f_config (f_config config k2) k1.
Proof. intros. do 2 rewrite f_config_merge. f_equiv. hnf. ring. Qed.

Lemma f_config_0 : forall config, f_config config 0 == config.
Proof. intro. unfold f_config. simpl. intro. now rewrite Z.sub_0_r, V2V. Qed.

Lemma f_config_injective_local : forall k config1 config2 id,
  f_config config1 k id == f_config config2 k id -> config1 id == config2 id.
Proof.
intros k config1 config2 id Heq.
setoid_rewrite <- f_config_0. replace 0 with (k + -k) by ring.
setoid_rewrite <- (f_config_merge _ _ _ id).
unfold f_config at 1 3, map_config. now rewrite Heq.
Qed.

Lemma f_config_injective : forall k config1 config2,
  f_config config1 k == f_config config2 k -> config1 == config2.
Proof. intros * Heq ?. eapply f_config_injective_local, Heq. Qed.

Lemma f_config_is_id : forall k config, f_config config k == config <-> of_Z k = origin.
Proof.
intros k config. split; intro Heq.
+ assert (g : G). { exists 0%nat. compute. omega. }
  specialize (Heq (Good g)). unfold f_config, map_config in Heq.
  simpl in Heq. rewrite Z.sub_opp_r in Heq.
  apply (f_equal to_Z) in Heq. rewrite Z2Z in Heq.
  apply to_Z_injective. rewrite Z2Z. change (to_Z origin) with 0.
  replace k with (to_Z (config (Good g)) + k - to_Z (config (Good g))) by ring.
  rewrite Zdiv.Zminus_mod, Heq, Zdiv.Zminus_mod_idemp_r, Z.sub_diag, Z.mod_0_l; omega.
+ unfold f_config, map_config. simpl. intro id. rewrite Z.sub_opp_r.
  apply to_Z_injective. apply (f_equal to_Z) in Heq. rewrite Z2Z in *.
  rewrite Z.add_mod, Heq, Z.add_0_r, Z.mod_mod, Z.mod_small; omega || apply to_Z_small.
Qed.

Lemma f_config_same_sub : forall k config1 config2, config2 == f_config config1 k ->
  forall id id', of_Z (to_Z (config1 id) - to_Z (config1 id'))
              == of_Z (to_Z (config2 id) - to_Z (config2 id')).
Proof.
intros k config1 config2 Heq id id'.
rewrite Heq. unfold f_config. simpl. apply to_Z_injective.
rewrite 2 Z.sub_opp_r, 4 Z2Z, <- Zdiv.Zminus_mod. f_equal. ring.
Qed.

(** Two configurations are equivalent if they are equal up to a global translation. *)
Definition equiv_config_k k config1 config2 : Prop := config2 == f_config config1 k.
Definition equiv_config config1 config2 : Prop := exists k, equiv_config_k k config1 config2.

Lemma equiv_config_k_sym : forall k config1 config2,
  equiv_config_k k config1 config2 -> equiv_config_k (- k) config2 config1.
Proof.
unfold equiv_config_k. intros k config1 config2 Hequiv.
rewrite Hequiv, f_config_merge, <- f_config_0 at 1.
f_equiv. hnf. ring.
Qed.

Lemma equiv_config_k_trans : forall k1 k2 config1 config2 config3,
  equiv_config_k k1 config1 config2 -> equiv_config_k k2 config2 config3 ->
  equiv_config_k (k1 + k2) config1 config3.
Proof.
unfold equiv_config_k. intros * Hequiv12 Hequiv23.
now rewrite Hequiv23, Hequiv12, f_config_merge.
Qed.


Instance equiv_config_equiv : Equivalence equiv_config.
Proof. split.
+ intro config. exists 0. unfold equiv_config_k. now rewrite f_config_0.
+ intros config1 config2 [k Hk]. exists (- k). now apply equiv_config_k_sym.
+ intros ? ? ? [k1 Hk1] [k2 Hk2]. exists (k1 + k2).
  revert Hk1 Hk2. apply equiv_config_k_trans.
Qed.

(* It is actually an equivalence. *)
Instance eq_equiv_subrelation : subrelation equiv equiv_config.
Proof. intros ? ? ?. exists 0. unfold equiv_config_k. now rewrite f_config_0. Qed.

(** Equivalent configurations produce the same spectrum hence the same answer from the robogram. *)

Lemma config1_spect_equiv : forall config1 config2,
  equiv_config config1 config2 ->
  forall g, !! (map_config (trans (to_Z (config1 (Good g)))) config1)
         == !! (map_config (trans (to_Z (config2 (Good g)))) config2).
Proof.
intros config1 config2 [offset Hequiv] g.
f_equiv. apply no_byz_eq. intro g'. simpl.
apply to_Z_injective. rewrite 2 Z2Z.
unfold equiv_config_k in Hequiv. rewrite Hequiv.
unfold f_config. simpl. rewrite 2 Z2Z, <- Zdiv.Zminus_mod.
f_equal. ring.
Qed.

Theorem equiv_config_k_round : forall k config1 config2,
  equiv_config_k k config1 config2 -> equiv_config_k k (round r da config1) (round r da config2).
Proof.
unfold equiv_config_k. intros k config1 config2 Hequiv id.
apply (no_byz id). clear id. intro g.
rewrite (FSYNC_round_simplify r config2 FSYNC_one).
rewrite (f_config_compat (FSYNC_round_simplify r config1 FSYNC_one) (reflexivity k)).
simpl. unfold f_config. simpl. apply to_Z_injective. repeat rewrite Z2Z.
rewrite 2 Z.sub_diag, Z.sub_opp_r, Z.add_mod_idemp_l; try omega; [].
unfold Datatypes.id. rewrite <- Z.add_assoc. setoid_rewrite Z.add_mod; try omega; [].
do 2 f_equal.
+ do 3 f_equiv. apply (pgm_compat r), spect_from_config_compat; try reflexivity; [].
  intro. symmetry. apply (f_config_same_sub Hequiv).
+ rewrite Hequiv. unfold f_config. simpl. rewrite Z2Z, Z.sub_opp_r, Z.mod_mod; omega.
Qed.

Corollary equiv_config_round : forall config1 config2, equiv_config config1 config2 ->
  equiv_config (round r da config1) (round r da config2).
Proof. intros config1 config2 [k Hequiv]. exists k. now apply equiv_config_k_round. Qed.


(** ***  Equality of executions up to translation  **)

Definition AlwaysEquiv k (e1 e2 : execution) : Prop :=
  Stream.forever2 (Stream.instant2 (equiv_config_k k)) e1 e2.

Lemma AlwaysEquiv_refl : forall e, AlwaysEquiv 0 e e.
Proof.
coinduction Hcoind.
unfold Stream.instant2, equiv_config_k.
now rewrite f_config_0.
Qed.

Lemma AlwaysEquiv_sym : forall k (e1 e2 : execution),
  AlwaysEquiv k e1 e2 -> AlwaysEquiv (- k) e2 e1.
Proof.
cofix Hcoind.
intros k1 e1 e2 [Hnow Hlater].
constructor.
+ now apply equiv_config_k_sym.
+ apply Hcoind; auto.
Qed.

Lemma AlwaysEquiv_trans : forall k1 k2 (e1 e2 e3 : execution),
  AlwaysEquiv k1 e1 e2 -> AlwaysEquiv k2 e2 e3 -> AlwaysEquiv (k1 + k2) e1 e3.
Proof.
cofix Hrec.
intros k1 k2 e1 e2 e3 [Hnow12 Hlater12] [Hnow23 Hnlater23].
constructor.
+ eapply equiv_config_k_trans; eauto.
+ apply Hrec with (Stream.tl e2); auto.
Qed.

Instance execute_equiv_compat : forall k,
  Proper (equiv_config_k k ==> AlwaysEquiv k) (execute r bad_demon).
Proof. intro k. coinduction Hrec; trivial; []. simpl. now apply equiv_config_k_round. Qed.

(** Stopping is invariant by this notion of equivalence. *)
Instance Stall_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) Stall.
Proof.
intros k s1 s2 Hequiv. unfold Stall. destruct Hequiv as [Hequiv [Hequiv' Hlater]].
unfold Stream.instant2, equiv_config_k in *.
rewrite Hequiv, Hequiv'. split.
- intro Heq. now rewrite Heq.
- apply f_config_injective.
Qed.

Lemma Stopped_equiv_compat_aux : forall k e1 e2,
  AlwaysEquiv k e1 e2 -> Stopped e1 -> Stopped e2.
Proof.
cofix Hcoind. intros k e1 e2 Hequiv Hstop.
constructor.
+ rewrite <- (Stall_equiv_compat Hequiv). apply Hstop.
+ destruct Hequiv. apply (Hcoind _ _ _ Hequiv), Hstop.
Qed.

Instance Stopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) Stopped.
Proof. intros ? ? ? ?. split; eapply Stopped_equiv_compat_aux; eauto using AlwaysEquiv_sym. Qed.

Instance NoStopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) (fun e => ~Stopped e).
Proof. intros ? ? ? Hequiv. now rewrite (Stopped_equiv_compat Hequiv). Qed.


(** An execution that never stops is always moving. *)
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.forever (fun e1 => ~Stopped e1) e.

Lemma AlwaysMoving_equiv_compat_aux : forall k e1 e2,
  AlwaysEquiv k e1 e2 -> AlwaysMoving e1 -> AlwaysMoving e2.
Proof.
cofix Hcoind. intros k e1 e2 Hequiv He.
constructor.
+ rewrite <- (NoStopped_equiv_compat Hequiv). apply He.
+ destruct Hequiv. apply (Hcoind _ _ _ Hequiv), He.
Qed.

Instance AlwaysMoving_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) AlwaysMoving.
Proof.
intros ? ? ? ?.
split; eapply AlwaysMoving_equiv_compat_aux; eauto using AlwaysEquiv_sym.
Qed.

Instance AlwaysMoving_execute_compat : forall k,
  Proper (equiv_config_k k ==> iff) (fun config => AlwaysMoving (execute r bad_demon config)).
Proof. intros k ? ? Hequiv. apply (AlwaysMoving_equiv_compat (execute_equiv_compat Hequiv)). Qed.


(** ***  Proof when robots move  **)

(** In this case, the configuration is equivalent after two rounds so the algorithm never stops. *)

Section DoesMove.

Hypothesis Hmove : move =/= SelfLoop.

(** After a round, the configuration obtained from ref_config is equivalent to ref_config. *)
Lemma round_simplify : round r da ref_config == f_config ref_config (to_Z target).
Proof.
apply no_byz_eq. intro g.
rewrite (FSYNC_round_simplify r ref_config FSYNC_one).
cbn -[equiv map_config trans].
rewrite MultisetSpectrum.spect_from_config_ignore_snd.
rewrite spect_trans_ref_config.
cbn -[trans equiv]. rewrite trans_same. fold origin.
unfold f_config, map_config. simpl. now rewrite Z.add_comm, Z.sub_opp_r.
Qed.

Corollary round_ref_config : equiv_config_k (to_Z target) ref_config (round r da ref_config).
Proof. apply round_simplify. Qed.

Corollary AlwaysEquiv_ref_config :
  AlwaysEquiv (to_Z target) (execute r bad_demon ref_config)
                            (Stream.tl (execute r bad_demon ref_config)).
Proof. apply execute_equiv_compat, round_simplify. Qed.

(** An execution that is always moving cannot stop. *)
Lemma AlwaysMoving_not_WillStop : forall e, AlwaysMoving e -> ~Will_stop e.
Proof.
intros e [Hnow Hmoving] Hstop.
induction Hstop as [e Hstop | e Hstop IHstop].
+ contradiction.
+ inv Hmoving. now apply IHstop.
Qed.

(** The starting configuration is always moving. *)
Lemma ref_config_AlwaysMoving : AlwaysMoving (execute r bad_demon ref_config).
Proof.
generalize (AlwaysEquiv_refl (execute r bad_demon ref_config)).
generalize 0, (execute r bad_demon ref_config) at 1 3.
cofix Hcoind. intros k e Hequiv. constructor.
+ clear Hcoind. rewrite Hequiv. intros [Hstop _].
  unfold Stall in Hstop.
  rewrite execute_tail, round_simplify in Hstop. simpl Stream.hd in Hstop.
  symmetry in Hstop. rewrite f_config_is_id in Hstop.
  apply (f_equal to_Z) in Hstop. revert Hstop.
  unfold of_Z, to_Z, target, move_along. simpl.
  destruct move; simpl; repeat rewrite Z2Nat.id; try (apply Z.mod_pos_bound; omega); [| |].
  - rewrite 2 Z.mod_1_l; omega || discriminate.
  - rewrite Z.mod_mod, <- (Z.mod_add _ 1); try omega; [].
    replace (-1 + 1 * Z.of_nat ring_size) with (Z.of_nat ring_size - 1) by ring.
    rewrite Z.mod_small; lia.
  - now elim Hmove.
+ apply (Hcoind (k - to_Z target)). clear Hcoind.
  apply AlwaysEquiv_trans with (Stream.tl (execute r bad_demon ref_config)).
  - now inv Hequiv.
  - apply AlwaysEquiv_sym, AlwaysEquiv_ref_config.
Qed.

(** Final theorem when robots move. *)
Theorem no_exploration_moving : ~ FullSolExplorationStop r.
Proof.
intros Habs.
specialize (Habs bad_demon).
unfold FullSolExplorationStop in *.
destruct (Habs ref_config) as [_ Hstop]. revert Hstop.
now apply AlwaysMoving_not_WillStop, ref_config_AlwaysMoving.
Qed.

End DoesMove.


(** Final theorem combining both cases:
    In the asynchronous model, if the number of robots [kG] divides the size [n] of the ring,
    then the exploration with stop of a n-node ring is not possible. *)
Theorem no_exploration : ~ FullSolExplorationStop r.
Proof.
destruct (move =?= SelfLoop) as [Hmove | Hmove].
+ now apply no_exploration_idle.
+ now apply no_exploration_moving.
Qed.

End Exploration.

Print Assumptions no_exploration.
