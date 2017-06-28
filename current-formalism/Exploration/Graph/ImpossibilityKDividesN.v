(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, R. Pelle, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid SetoidList Compare_dec Morphisms.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
Require Import Pactole.Exploration.ZnZ.Definitions.
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
Require Import Pactole.Exploration.Graph.Definitions.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.


Set Implicit Arguments.
Open Scope Z_scope.


(** Size of the ring. *)
Definition n := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.n.

(** Number of good robots. *)
Definition kG := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.kG.

Module K := Pactole.Exploration.ZnZ.ImpossibilityKDividesN.K.

Module def : RingDef with Definition n := n.
 Definition n:= n.
 Definition n_sup_1 : (n > 1)%nat := n_sup_1.
End def.

(** The setting is a ring. *)
Module Gra := MakeRing.


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(K).
Export DefsE.
Export Gra.
Export MakeRing.
Import Equiv.DGF.

(** There is no byzantine robot so we can simplify properties about identifiers and configurations. *)
Lemma no_byz : forall (id : Names.ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. unfold K.nB in *. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : Config.t,
  (forall g, Config.eq_RobotConf (config1 (Good g)) (config2 (Good g))) -> Config.eq config1 config2.
Proof. intros config1 config2 Heq id. apply (no_byz id). intro g. apply Heq. Qed.

(** A dummy value used for (inexistant) byzantine robots. *)
Definition dummy_val := {| Config.loc := Loc.origin;
                           Config.info := {| Info.source := Loc.origin; Info.target := Loc.origin |} |}.


Section Exploration.
Variable r : Equiv.DGF.robogram.

Hypothesis Hdiv : (n mod kG = 0)%nat.

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    Thus, is they move at all, then they will never stop.  If they do not move, they do not explore the graph.
    The configuration to which we will always come back is [config1].  *)

(** ***  Definition of the starting configuration and demon used in the proof  **)

Definition create_config1 (k : nat) (g : {n : nat | (n < k)%nat}) : Loc.t :=
  Loc.mul (((Z_of_nat ((proj1_sig g) * (n / kG))))) Loc.unit.

(** The starting configuration where robots are evenly spaced:
    each robot is at a distance of [n / kG] from the previous one, starting from the origin. *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_config1 g in
                          {| Config.loc :=  pos;
                             Config.info := {| Info.source := pos; Info.target := pos |} |}
              | Byz b => dummy_val
            end.

Lemma config1_injective : forall id1 id2,
  Loc.eq (Config.loc (config1 id1)) (Config.loc (config1 id2)) -> id1 = id2.
Proof.
intros id1 id2. apply (no_byz id2), (no_byz id1). clear id1 id2.
intros g1 g2 Heq. f_equal. revert Heq. apply unique_g.
Qed.

(**  Translating [config1] by multiple of [n / kG] does not change its spectrum. *)
Lemma spect_trans_config1 : forall g : Names.G,
  Spect.eq (!! (Config.map (Config.app (trans (create_config1 g))) config1)) (!! config1).
Proof.
intro g. unfold Spect.from_config. f_equiv. do 2 rewrite Config.list_spec, map_map.
apply NoDupA_equivlistA_PermutationA; autoclass; [| |].
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros id1 id2 Heq. apply Loc.add_reg_r in Heq.
    now apply config1_injective.
  + rewrite NoDupA_Leibniz. apply Names.names_NoDup.
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros ? ? ?. now apply config1_injective.
  + rewrite NoDupA_Leibniz. apply Names.names_NoDup.
* intro pt. repeat rewrite InA_map_iff; autoclass; [].
  assert (HkG : kG <> 0%nat). { generalize k_sup_1. unfold kG. omega. }
  assert (Z.of_nat n <> 0). { generalize n_sup_1. unfold n. omega. }
  split; intros [id [Hpt _]]; revert Hpt; apply (no_byz id); clear id; intros g' Hpt.
  + assert (Hlt : ((proj1_sig g' + (kG - proj1_sig g)) mod kG < kG)%nat) by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. unfold create_config1. simpl. clear Hpt.
      (* This part is a proof about modular arithmetic *)
      rewrite Nat.add_mod, <- Loc.minus_morph, Loc.add_morph; trivial; [].
      unfold Loc.mul, ImpossibilityKDividesN.Loc.mul, Loc.unit, ImpossibilityKDividesN.Loc.unit.
      destruct g as [g Hg], g' as [g' Hg']. simpl in *. change K.nG with kG in *.
      destruct (Nat.eq_dec g 0).
      ++ (* particular case when g = 0 *)
         subst g. rewrite Nat.sub_0_r, Nat.mul_0_l, Nat.mod_same, Nat.add_0_r, Nat.mod_mod; trivial; [].
         hnf. do 2 f_equal. rewrite Nat.mod_small; trivial; nia.
      ++ assert (kG - g < kG)%nat by omega.
         rewrite (Nat.mod_small (kG - g)), (Nat.mod_small g'); trivial. 
         hnf. repeat rewrite Z.mod_mod, Z.mul_1_r; trivial; [].
         assert (Hcase : ((g' + (kG - g)) mod kG = g' + (kG - g) /\ g' < g
                       \/ (g' + (kG - g)) mod kG = g' - g /\ g <= g')%nat).
         { assert (Hadd : (g' + (kG - g) < kG + kG)%nat) by now apply Nat.add_lt_mono.
           destruct (le_lt_dec g g').
           - right. split; trivial; []. rewrite Nat.mod_eq; trivial; [].
             cut ((g' + (kG - g)) / kG = 1)%nat; try nia; [].
             assert ((0 <= (g' + (kG - g)) mod kG < kG)%nat) by (apply Nat.mod_bound_pos; omega).
             assert (Hle : (kG <= (g' + (kG - g)))%nat) by omega.
             rewrite (Nat.div_mod (g' + (kG - g)) kG HkG) in Hadd, Hle.
             destruct ((g' + (kG - g)) / kG)%nat as [| [| n]]; nia.
           - left. split; trivial; []. rewrite Nat.mod_small; omega. }
         destruct Hcase as [[Hcase Hwhy] | [Hcase Hwhy]]; rewrite Hcase.
         -- rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r, Nat2Z.inj_add, Nat2Z.inj_sub; [| nia].
            rewrite Z.add_sub_assoc, Z.add_comm, <- Z.add_sub_assoc, Z.add_mod; trivial; [].
            rewrite <- (proj2 (Nat.div_exact n kG HkG) Hdiv), Z.mod_same; trivial; [].
            simpl. now rewrite Z.mod_mod.
         -- f_equal. nia.
    - rewrite InA_Leibniz. apply Names.In_names.
  + assert (Hlt : ((proj1_sig g' + proj1_sig g) mod kG < kG)%nat) by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. unfold create_config1. simpl.
      (* This part is a proof about modular arithmetic *)
      rewrite Nat.add_mod, <- Loc.minus_morph, Loc.add_morph; trivial; [].
      unfold Loc.mul, ImpossibilityKDividesN.Loc.mul, Loc.unit, ImpossibilityKDividesN.Loc.unit.
      destruct g as [g Hg], g' as [g' Hg']. simpl in *.
      rewrite (Nat.mod_small g), (Nat.mod_small g'); trivial; [].
      hnf. repeat rewrite Z.mod_mod, Z.mul_1_r; trivial; [].
      assert (Hcase : ((g' + g) mod kG = g' + g /\ g' + g < kG
                    \/ (g' + g) mod kG = g' + g - kG /\ kG <= g' + g)%nat).
      { assert (Hadd : (g' + g < kG + kG)%nat) by now apply Nat.add_lt_mono.
        destruct (le_lt_dec kG (g' + g)) as [Hle |].
        - right. rewrite Nat.mod_eq; trivial; [].
          cut ((g' + g) / kG = 1)%nat; try nia; [].
          assert (0 <= (g' + g) mod kG < kG)%nat by (apply Nat.mod_bound_pos; omega).
          rewrite (Nat.div_mod (g' + g) kG HkG) in Hadd, Hle.
          destruct ((g' + g) / kG)%nat as [| [| n]]; nia.
        - left. now rewrite Nat.mod_small. }
      destruct Hcase as [[Hcase Hwhy] | [Hcase Hwhy]]; rewrite Hcase.
      ++ f_equal. nia.
      ++ rewrite Nat.mul_sub_distr_r. rewrite Nat2Z.inj_sub; try nia; [].
         repeat rewrite Nat2Z.inj_mul, ?Nat2Z.inj_add. rewrite <- (Nat2Z.inj_mul kG).
         rewrite <- (proj2 (Nat.div_exact n kG HkG) Hdiv).
         unfold Z.sub. rewrite Z.add_mod, (Z.add_mod _ (-Z.of_nat n)); trivial; [].
         rewrite Zdiv.Z_mod_zero_opp_full; try apply Z.mod_same; trivial; [].
         rewrite Z.add_0_r, Z.mod_mod, Z.mul_add_distr_r, <- Z.add_mod; trivial; []. f_equal. lia.
    - rewrite InA_Leibniz. apply Names.In_names.
Qed.

Program Definition da : demonic_action := {|
  relocate_byz := fun _ => dummy_val;
      step := fun id Rconfig =>
                if Loc.eq_dec (Config.loc Rconfig) (Info.target (Config.info Rconfig))
                then Active (trans (Config.loc Rconfig)) else Moving true |}.
Next Obligation.
intuition. unfold Loc.eq_dec in *.
now destruct (LocationA.eq_dec (Config.loc Rconfig) (Info.target (Config.info Rconfig))).
Qed.
Next Obligation.
intros [g1 | b1] [g2 | b2] Hg rc1 rc2 Hrc; try discriminate; simpl in *.
destruct Hrc as (Hl_rc, (Hs_rc, Ht_rc)).
destruct (Loc.eq_dec (Config.loc rc1) (Info.target (Config.info rc1))),
         (Loc.eq_dec (Config.loc rc2) (Info.target (Config.info rc2)));
try (now auto); try now rewrite Hl_rc, Ht_rc in *.
- rewrite Hl_rc. now unfold Aom_eq.
- destruct b1. unfold K.nB in *. omega.
Qed.

CoFixpoint bad_demon : demon := Stream.cons da bad_demon.

(** As all robots see the same spectrum, we take for instance the one at location [Loc.origin]. *)
Definition move := pgm r (!! config1) Loc.origin.


(** **  First case: robots do not move  **)

(** In this case, the configuration stays exactly the same hence there is a location which is not explored. *)

Section NoMove.
Hypothesis Hmove : Loc.eq move Loc.origin.

Lemma round_id : Config.eq (round r da config1) config1.
Proof.
apply no_byz_eq. intro g. unfold round. simpl.
destruct_match; try congruence; [].
repeat split; []. cbn -[trans].
rewrite spect_trans_config1. simpl. rewrite Loc.add_opp.
change (Graph.Veq (Loc.add move (create_config1 g)) (create_config1 g)).
now rewrite Hmove, Loc.add_comm, Loc.add_origin.
Qed.

Lemma NeverVisited_config1 : forall e,
  eeq e (execute r bad_demon config1) ->
  exists pt, ~ Will_be_visited pt e.
Proof.
intros e Heq_e.
exists Loc.unit.
intro Hl. induction Hl as [e [g Hvisited] | e Hlater IHvisited].
+ rewrite Heq_e in Hvisited. simpl in Hvisited.
  assert (Heq : Z.of_nat (n mod kG) = 0) by (unfold n, kG; generalize kdn; omega).
  now apply (config1_ne_unit Heq g).
+ apply IHvisited. rewrite Heq_e. cbn. f_equiv. apply round_id.
Qed.

Lemma never_visited : ~(forall pt, Will_be_visited pt (execute r bad_demon config1)).
Proof.
intros Hw.
destruct (NeverVisited_config1 (reflexivity _)) as [pt Hpt].
apply Hpt, Hw.
Qed.

Theorem no_exploration_idle : ~(forall d, FullSolExplorationStop r d).
Proof.
intros Habs.
specialize (Habs bad_demon).
destruct (Habs config1) as [Hexpl _].
now apply never_visited.
Qed.

End NoMove.


(** **  Second case: the robots move  **)

(** ***  Equality of configurations up to translation  **)

(** Translating a configuration. *)
Definition f_config config k : Config.t := Config.map (Config.app (trans (Loc.opp k))) config.

Instance f_config_compat : Proper (Config.eq ==> Loc.eq ==> Config.eq) f_config.
Proof.
unfold f_config. repeat intro.
apply Config.map_compat; trivial; [].
intros ? ? Heq. now repeat f_equiv.
Qed.

Lemma f_config_merge : forall config k1 k2,
  Config.eq (f_config (f_config config k1) k2) (f_config config (Loc.add k1 k2)).
Proof.
intros config k1 k2. unfold f_config. rewrite Config.map_merge; autoclass; [].
apply no_byz_eq. intro g.
repeat split; simpl; repeat rewrite Loc.opp_opp; now rewrite Loc.add_assoc.
Qed.

Lemma f_config_swap : forall config k1 k2,
  Config.eq (f_config (f_config config k1) k2) (f_config (f_config config k2) k1).
Proof. intros. do 2 rewrite f_config_merge. now rewrite Loc.add_comm. Qed.

Lemma f_config_origin : forall config, Config.eq (f_config config Loc.origin) config.
Proof.
intro config. unfold f_config. simpl.
rewrite <- (Config.map_id config) at 2. rewrite <- Config.app_id. do 2 f_equiv.
intros ? ? Heq. now rewrite Loc.opp_opp, Loc.add_origin.
Qed.

Lemma f_config_is_id : forall k config, Config.eq (f_config config k) config <-> Loc.eq k Loc.origin.
Proof.
intros k config. split; intro Heq.
+ assert (g : Names.G). { exists 0%nat. compute. generalize k_sup_1; omega. }
  specialize (Heq (Good g)). unfold f_config, Config.map, Config.app in Heq.
  apply Config.loc_compat in Heq. simpl in Heq.
  rewrite Loc.opp_opp in Heq. rewrite <- (Loc.add_origin (Config.loc (config (Good g)))) in Heq at 2.
  now apply Loc.add_reg_l in Heq.
+ now rewrite Heq, f_config_origin.
Qed.

(** Two configurations are equivalent if they are equal up to a global translation. *)
Definition equiv_config_k k config1 config2 : Prop := Config.eq config2 (f_config config1 k).
Definition equiv_config config1 config2 : Prop := exists k, equiv_config_k k config1 config2.

Lemma equiv_config_k_sym : forall k config1 config2,
  equiv_config_k k config1 config2 -> equiv_config_k (Loc.opp k) config2 config1.
Proof.
unfold equiv_config_k. intros k config1 config2 Hequiv.
now rewrite Hequiv, f_config_merge, Loc.add_opp, f_config_origin.
Qed.

Lemma equiv_config_k_trans : forall k1 k2 config1 config2 config3,
  equiv_config_k k1 config1 config2 -> equiv_config_k k2 config2 config3 ->
  equiv_config_k (Loc.add k1 k2) config1 config3.
Proof.
unfold equiv_config_k. intros * Hequiv12 Hequiv23.
now rewrite Hequiv23, Hequiv12, f_config_merge.
Qed.


Instance equiv_config_equiv : Equivalence equiv_config.
Proof. split.
+ intro config. exists 0. unfold equiv_config_k. now rewrite f_config_origin.
+ intros config1 config2 [k Hk]. exists (Loc.opp k). now apply equiv_config_k_sym.
+ intros ? ? ? [k1 Hk1] [k2 Hk2]. exists (Loc.add k1 k2).
  revert Hk1 Hk2. apply equiv_config_k_trans.
Qed.

Instance eq_equiv_subrelation : subrelation Config.eq equiv_config.
Proof.
intros config1 config2 Heq. exists Loc.origin. unfold equiv_config_k, f_config. simpl.
assert ((Loc.eq ==> Loc.eq)%signature (fun x => Loc.add x (Loc.opp (Loc.opp Loc.origin))) id).
{ intros ? ? H. now rewrite Loc.opp_opp, Loc.add_origin, H. }
now rewrite H, Config.app_id, Config.map_id, Heq.
Qed.

(** Equivalent configurations produce the same spectrum hence the same answer from the robogram. *)

Lemma config1_Spectre_Equiv : forall config1 config2,
  equiv_config config1 config2 ->
  forall g, Spect.eq (!! (Config.map (Config.app (trans (Config.loc (config1 (Good g))))) config1))
                     (!! (Config.map (Config.app (trans (Config.loc (config2 (Good g))))) config2)).
Proof.
intros config1 config2 [offset Hequiv] g.
f_equiv. apply no_byz_eq. intro g'. simpl.
repeat split; simpl;
rewrite (Hequiv (Good g)), (Hequiv (Good g')); unfold f_config; simpl;
rewrite Loc.opp_opp, Loc.opp_distr_add, <- Loc.add_assoc; f_equiv;
setoid_rewrite Loc.add_comm at 2;
now rewrite <- Loc.add_assoc, (Loc.add_comm _ offset), Loc.add_opp, Loc.add_origin.
Qed.

Theorem equiv_config_k_round : forall k config1 config2,
  equiv_config_k k config1 config2 -> equiv_config_k k (round r da config1) (round r da config2).
Proof.
unfold equiv_config_k. intros k config1 config2 Hequiv id.
apply (no_byz id). clear id. intro g. unfold round. simpl.
destruct (Loc.eq_dec (Config.loc (config2 (Good g))) (Info.target (Config.info (config2 (Good g)))))
  as [Hcase | Hcase].
+ (* da1 sets g as Active *)
  assert (Loc.eq (Config.loc (config1 (Good g))) (Info.target (Config.info (config1 (Good g))))).
  { rewrite (Hequiv (Good g)) in Hcase. simpl in Hcase. now apply Loc.add_reg_r in Hcase. }
  unfold f_config. unfold Config.map at 2, Config.app at 2. simpl.
  destruct_match; simpl; try contradiction; [].
  repeat split; simpl; try apply Hequiv; [].
  (* Only target is changed and we replace config1 with config2 *)
  assert (Hspect := config1_Spectre_Equiv (ex_intro _ k Hequiv) g).
  rewrite <- Hspect, (Hequiv (Good g)). clear Hspect. simpl.
  rewrite Loc.opp_opp.
  rewrite <- (Loc.add_assoc (pgm _ _ _)). f_equiv.
  apply pgm_compat. f_equiv. now do 2 rewrite Loc.add_opp.
+ (* da1 sets g as Moving *)
  assert (~Loc.eq (Config.loc (config1 (Good g))) (Info.target (Config.info (config1 (Good g))))).
  { rewrite (Hequiv (Good g)) in Hcase. simpl in Hcase. intro Heq. apply Hcase. now rewrite Heq. }
  unfold f_config. unfold Config.map at 1, Config.app at 1. simpl.
  destruct_match; simpl; try contradiction; [].
  repeat split; simpl; apply Hequiv.
Qed.

Corollary equiv_config_round : forall config1 config2, equiv_config config1 config2 ->
  equiv_config (round r da config1) (round r da config2).
Proof. intros config1 config2 [k Hequiv]. exists k. now apply equiv_config_k_round. Qed.


(** ***  Equality of executions up to translation  **)

Definition AlwaysEquiv k (e1 e2 : execution) : Prop :=
  Stream.next_eq (equiv_config_k k) e1 e2.

Lemma AlwaysEquiv_refl : forall e, AlwaysEquiv Loc.origin e e.
Proof.
cofix Hrec. intro e. constructor.
+ unfold Stream.instant2, equiv_config_k. now rewrite f_config_origin.
+ apply Hrec; auto.
Qed.

Lemma AlwaysEquiv_sym : forall k (e1 e2 : execution),
  AlwaysEquiv k e1 e2 -> AlwaysEquiv (Loc.opp k) e2 e1.
Proof.
cofix Hrec.
intros k1 e1 e2 [Hnow Hlater].
constructor.
+ now apply equiv_config_k_sym.
+ apply Hrec; auto.
Qed.

Lemma AlwaysEquiv_trans : forall k1 k2 (e1 e2 e3 : execution),
  AlwaysEquiv k1 e1 e2 -> AlwaysEquiv k2 e2 e3 -> AlwaysEquiv (Loc.add k1 k2) e1 e3.
Proof.
cofix Hrec.
intros k1 k2 e1 e2 e3 [Hnow12 Hlater12] [Hnow23 Hnlater23].
constructor.
+ eapply equiv_config_k_trans; eauto.
+ apply Hrec with (Stream.tl (Stream.tl e2)); auto.
Qed.

Instance execute_equiv_compat : forall k, Proper (equiv_config_k k ==> AlwaysEquiv k) (execute r bad_demon).
Proof. intro k. coinduction Hrec; trivial; []. simpl. now do 2 apply equiv_config_k_round. Qed.

(** Stopping is invariant by this notion of equivalence. *)
Instance stop_now_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) stop_now.
Proof.
intros k s1 s2 Hequiv. unfold stop_now. destruct Hequiv as [Hequiv [Hequiv' Hlater]].
unfold Stream.instant2, equiv_config_k in *.
rewrite Hequiv, Hequiv'. split; intro Heq.
+ now rewrite Heq.
+ apply no_byz_eq. intro g. specialize (Heq (Good g)).
  destruct Heq as [Heql [Heqs Heqt]]. simpl in *.
  repeat split; eapply Loc.add_reg_r; eassumption.
Qed.

Instance Stopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) Stopped.
Proof.
intros k s1 s2 Hequiv. apply (Stream.next_forever_next_compat (equiv_config_k k)).
+ apply stop_now_equiv_compat.
+ apply Hequiv.
Qed.

Instance NoStopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) (fun e => ~Stopped e).
Proof. intros ? ? ? Hequiv. now rewrite (Stopped_equiv_compat Hequiv). Qed.


(** An execution that never stops is always moving. *)
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.next_forever (fun e1 => ~Stopped e1) e.

Instance AlwaysMoving_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) AlwaysMoving.
Proof.
intros k ? ? Hequiv.
apply (Stream.next_forever_next_compat _ _ _ (@NoStopped_equiv_compat k) _ _ Hequiv).
Qed.

Instance AlwaysMoving_execute_compat : forall k,
  Proper (equiv_config_k k ==> iff) (fun config => AlwaysMoving (execute r bad_demon config)).
Proof. intros k ? ? Hequiv. apply (AlwaysMoving_equiv_compat (execute_equiv_compat Hequiv)). Qed.


(** ***  Proof when robots move  **)

(** In this case, the configuration is equivalent after two rounds so the algorithm never stops. *)

Section DoesMove.

Hypothesis Hmove : ~Loc.eq move Loc.origin.

(** After two rounds, the configuration obtained from config1 is equivalent to config1. *)
Lemma round_round : Config.eq (round r da (round r da config1)) (f_config config1 move).
Proof.
assert (Hstep1 : forall id, step da id (config1 id) = Active (trans (Config.loc (config1 id)))).
{ intro id. apply (no_byz id). clear id. intro g. simpl. destruct_match; congruence. }
assert (Hstep2 : forall id, step da id (round r da config1 id) = Moving true).
{ intro id. apply (no_byz id). clear id. intro g. unfold round.
  specialize (Hstep1 (Good g)). destruct_match; try discriminate; []. inv Hstep1. cbn -[trans].
  destruct_match; trivial; []. exfalso. revert e.
  rewrite spect_trans_config1. unfold trans. simpl. rewrite Loc.add_opp.
  rewrite <- Loc.add_origin at 1. rewrite Loc.add_comm at 1.
  intro Heq. apply Loc.add_reg_r in Heq. symmetry in Heq. now revert Heq. }
apply no_byz_eq. intro g.
specialize (Hstep1 (Good g)). specialize (Hstep2 (Good g)).
(* unfold the second copy of round *)
unfold f_config, round at 1, Config.map at 1.
destruct_match; try discriminate; []. inv Hstep2.
(* unfold the first copy of round *)
unfold round. destruct_match; try discriminate; []. inv Hstep1. cbn -[trans].
repeat split; cbn -[trans].
- rewrite spect_trans_config1. simpl. now rewrite Loc.add_opp, Loc.opp_opp, Loc.add_comm.
- admit. (* Wrong for source *)
- rewrite spect_trans_config1. simpl. now rewrite Loc.add_opp, Loc.opp_opp, Loc.add_comm.
Admitted. (* round_round is wrong if the info contains the source *)

Corollary round_config1 : equiv_config_k move config1 (round r da (round r da config1)).
Proof. apply round_round. Qed.

Corollary AlwaysEquiv_config1 :
  AlwaysEquiv move (execute r bad_demon config1) (Stream.tl (Stream.tl (execute r bad_demon config1))).
Proof. apply execute_equiv_compat, round_round. Qed.

(** An execution that is always moving cannot stop. *)
Lemma AlwaysMoving_not_WillStop : forall e, AlwaysMoving e -> ~Will_stop e.
Proof.
intros e [Hnow Hmoving] Hstop.
induction Hstop as [e Hstop | e Hstop IHstop].
+ contradiction.
+ inv Hmoving. now apply IHstop.
Qed.

(** The starting configuration is always moving. *)
Lemma config1_AlwaysMoving : AlwaysMoving (execute r bad_demon config1).
Proof.
generalize (AlwaysEquiv_refl (execute r bad_demon config1)).
generalize Loc.origin, (execute r bad_demon config1) at 1 3.
cofix Hrec. intros k e Hequiv. constructor.
+ rewrite Hequiv. intros [Hstop _].
  unfold stop_now in Hstop. simpl in *. rewrite round_round in Hstop.
  symmetry in Hstop. rewrite f_config_is_id in Hstop. contradiction.
+ apply (Hrec (Loc.add k (Loc.opp move))). clear Hrec.
  apply AlwaysEquiv_trans with (Stream.tl (Stream.tl (execute r bad_demon config1))).
  - now inv Hequiv.
  - apply AlwaysEquiv_sym, AlwaysEquiv_config1.
Qed.

(** Final theorem when robots move. *)
Theorem no_exploration_moving : ~(forall d, FullSolExplorationStop r d).
Proof.
intros Habs.
specialize (Habs bad_demon).
unfold FullSolExplorationStop in *.
destruct (Habs config1) as [_ Hstop]. revert Hstop.
now apply AlwaysMoving_not_WillStop, config1_AlwaysMoving.
Qed.

End DoesMove.


(** Final theorem combining both cases:
    In the asynchronous model, if the number of robots [kG] divides the size [n] of the ring,
    then the exploration with stop of a n-node ring is not possible. *)
Theorem no_exploration : ~(forall d, FullSolExplorationStop r d).
Proof.
destruct (Loc.eq_dec move Loc.origin) as [Hmove | Hmove].
+ now apply no_exploration_idle.
+ now apply no_exploration_moving.
Qed.

End Exploration.

(* Print Assumptions no_exploration. *)
