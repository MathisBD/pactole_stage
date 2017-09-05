(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, R. Pelle, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     R. Pelle                                                               
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
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
Require Import Pactole.Exploration.Graph.DefinitionsSSync.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.
Open Scope Z_scope.


(** There are kG good robots and no byzantine ones. *)
Parameter kG : nat.

Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := DefinitionsSSync.ExplorationDefs(K).
Export DefsE.

(** Assumptions on the number of robots: it is non zero, less than n and divides n (the size of the ring). *)
Axiom kdn : (n mod kG = 0)%nat.
Axiom k_inf_n : (kG < n)%nat.
Axiom k_sup_1 : (1 < kG)%nat.

(** There is no meaningful information inside state. *)
Lemma no_info : forall rc1 rc2, Loc.eq (Config.loc rc1) (Config.loc rc2) -> Config.eq_RobotConf rc1 rc2.
Proof. intros [? []] [? []] Heq; split; simpl in *; auto. Qed.

(** There is no byzantine robot so we can simplify properties about identifiers and configurations. *)
Lemma no_byz : forall (id : Names.ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. unfold K.nB in *. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : Config.t,
  (forall g, Loc.eq (config1 (Good g)) (config2 (Good g))) -> Config.eq config1 config2.
Proof. intros config1 config2 Heq id. apply (no_byz id). intro g. apply no_info, Heq. Qed.

(** A dummy value used for (inexistant) byzantine robots. *)
Definition dummy_val := {| Config.loc := Loc.origin; Config.state := tt |}.


Section Exploration.
Variable r : DGF.robogram.

Hypothesis Hdiv : (n mod kG = 0)%nat.

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    Thus, is they move at all, then they will never stop.  If they do not move, they do not explore the graph.
    The configuration to which we will always come back is [config1].  *)

(** ***  Definition of the starting configuration and demon used in the proof  **)

Definition create_config1 (k : nat) (g : {n : nat | (n < k)%nat}) : Loc.t :=
  Ring.of_Z (((Z_of_nat ((proj1_sig g) * (n / kG))))).

(** The starting configuration where robots are evenly spaced:
    each robot is at a distance of [n / kG] from the previous one, starting from the origin. *)
Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_config1 g in
                          {| Config.loc :=  pos; Config.state := tt |}
              | Byz b => dummy_val
            end.

Lemma config1_injective : forall id1 id2,
  Loc.eq (Config.loc (config1 id1)) (Config.loc (config1 id2)) -> id1 = id2.
Proof.
generalize k_sup_1, k_inf_n. intros Hk1 Hkn id1 id2.
assert (n / kG <> 0)%nat by (rewrite Nat.div_small_iff; omega).
apply (no_byz id2), (no_byz id1). clear id1 id2.
intros g1 g2 Heq. f_equal. hnf in Heq.
unfold config1, create_config1, Ring.of_Z in *. simpl in *.
apply eq_proj1.
inv Heq. revert_all. rewrite 2 Z.mod_small, 2 Nat2Z.id, Nat.mul_cancel_r; auto; [|].
+ split; try apply Zle_0_nat; []. apply Nat2Z.inj_lt.
  apply Nat.lt_le_trans with (kG * (n / kG))%nat.
  - destruct g2 as [g2 Hg2]. simpl. unfold K.nG in *. apply mult_lt_compat_r; omega.
  - apply Nat.mul_div_le. omega.
+ split; try apply Zle_0_nat; []. apply Nat2Z.inj_lt.
  apply Nat.lt_le_trans with (kG * (n / kG))%nat.
  - destruct g1 as [g1 Hg1]. simpl. unfold K.nG in *. apply mult_lt_compat_r; omega.
  - apply Nat.mul_div_le. omega.
Qed.

(**  Translating [config1] by multiples of [n / kG] does not change its spectrum. *)
Lemma spect_trans_config1 : forall (g : Names.G) l,
  Spect.eq (!! (Config.map (apply_sim (trans (create_config1 g))) config1) l) (!! config1 l).
Proof.
intros g l. unfold Spect.from_config. split; f_equiv. do 2 rewrite Config.list_spec, map_map.
apply NoDupA_equivlistA_PermutationA; autoclass; [| |].
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros id1 id2 Heq. simpl in Heq. apply Loc.add_reg_r in Heq.
    now apply config1_injective.
  + rewrite NoDupA_Leibniz. apply Names.names_NoDup.
* apply map_injective_NoDupA with eq; autoclass; [|].
  + intros ? ? ?. now apply config1_injective.
  + rewrite NoDupA_Leibniz. apply Names.names_NoDup.
* intro pt. repeat rewrite InA_map_iff; autoclass; [| |].
  assert (HkG : kG <> 0%nat). { generalize k_sup_1. omega. }
  assert (Z.of_nat n <> 0). { generalize n_sup_1. omega. }
  assert (n / kG <> 0)%nat by (rewrite Nat.div_small_iff; generalize k_sup_1, k_inf_n; omega).
  split; intros [id [Hpt _]]; revert Hpt; apply (no_byz id); clear id; intros g' Hpt.
  + assert (Hlt : ((proj1_sig g' + (kG - proj1_sig g)) mod kG < kG)%nat) by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. unfold create_config1, Loc.add, Loc.opp. simpl.
      (* This part is a proof about modular arithmetic; we stay in Z to use the ring structure *)
      assert (Hn : (kG * (n / kG) = n)%nat). { symmetry. now rewrite Nat.div_exact. }
      hnf. rewrite 3 Ring.Z2Z. apply eq_proj1. unfold Ring.of_Z, Ring.n, Def.n. simpl. f_equal.
      (* Simplifying the left-hand side *)
      rewrite <- Nat.mul_mod_distr_r, Hn, Zdiv.mod_Zmod, Z.mod_mod; try omega; [].
      (* Simplifying the right-hand side *)
      rewrite Z.add_mod_idemp_l, Zopp_mod, Z.mod_mod, Z.add_mod_idemp_r;
      try (try apply Z.mod_pos_bound; omega); [].
      f_equal. rewrite 2 Nat2Z.inj_mul, Nat2Z.inj_add, Nat2Z.inj_sub, Z.mod_small.
      ++ ring_simplify. now rewrite <- (Nat2Z.inj_mul kG), Hn, Nat2Z.inj_mul.
      ++ split; try apply Zle_0_nat; [].
         apply Nat2Z.inj_lt. rewrite <- Hn at 2. rewrite <- Nat.mul_lt_mono_pos_r; lia || apply proj2_sig.
      ++ apply lt_le_weak, proj2_sig.
    - rewrite InA_Leibniz. apply Names.In_names.
  + assert (Hlt : ((proj1_sig g' + proj1_sig g) mod kG < kG)%nat) by now apply Nat.mod_upper_bound.
    pose (id' := exist (fun x => lt x kG) _ Hlt).
    exists (Good id'). split.
    - simpl. rewrite <- Hpt. simpl. unfold create_config1, Loc.add, Loc.opp. simpl.
      (* This part is a proof about modular arithmetic; we stay in Z to use the ring structure *)
      assert (Hn : (kG * (n / kG) = n)%nat). { symmetry. now rewrite Nat.div_exact. }
      hnf. rewrite 3 Ring.Z2Z. apply eq_proj1. unfold Ring.of_Z, Ring.n, Def.n. simpl. f_equal.
      (* Simplifying the left-hand side *)
      rewrite <- Nat.mul_mod_distr_r, Hn, Zdiv.mod_Zmod, Z.mod_mod; try omega; [].
      (* Simplifying the right-hand side *)
      rewrite Z.add_mod_idemp_l, Zopp_mod, Z.mod_mod, Z.add_mod_idemp_r;
      try (try apply Z.mod_pos_bound; omega); [].
      rewrite 2 Nat2Z.inj_mul, Nat2Z.inj_add, Z.add_mod, Zdiv.Zminus_mod_idemp_r, <- Z.add_mod; trivial; [].
      ring_simplify ((Z.of_nat (proj1_sig g') + Z.of_nat (proj1_sig g)) * Z.of_nat (n / kG)
                     + (Z.of_nat n - Z.of_nat (proj1_sig g) * Z.of_nat (n / kG))).
      rewrite <- (Z.mul_1_l (Z.of_nat n)) at 1.
      rewrite Z.mod_add; trivial; []. f_equal. lia.
    - rewrite InA_Leibniz. apply Names.In_names.
      + intros x y H; now rewrite H.
      + intros x y Hxy; rewrite Hxy; easy.
Qed.

Program Definition da : demonic_action := {|
  relocate_byz := fun _ => dummy_val;
  step := fun id => Some (fun Rconfig => trans (Config.loc Rconfig)) |}.
Next Obligation.
repeat intro. now do 2 f_equiv.
Qed.

Definition bad_demon : demon := Stream.constant da.

(** As all robots see the same spectrum, we take for instance the one at location [Loc.origin]. *)
Definition move := pgm r (!! config1 Loc.origin).


(** **  First case: robots do not move  **)

(** In this case, the configuration stays exactly the same hence there is a location which is not explored. *)

Section NoMove.
Hypothesis Hmove : Loc.eq move Loc.origin.

Lemma round_id : Config.eq (round r da config1) config1.
Proof.
apply no_byz_eq. intro g. unfold round. simpl.
repeat split; []. cbn -[trans].
rewrite spect_trans_config1. simpl. rewrite Loc.add_opp.
change (Ring.Veq (Loc.add move (create_config1 g)) (create_config1 g)).
now rewrite Hmove, Loc.add_comm, Loc.add_origin.
Qed.

Lemma NeverVisited_config1 : forall e,
  eeq e (execute r bad_demon config1) ->
  exists pt, ~ Will_be_visited pt e.
Proof.
intros e Heq_e. exists Loc.unit.
intro Hl. induction Hl as [e [g Hvisited] | e Hlater IHvisited].
* rewrite Heq_e in Hvisited. simpl in Hvisited.
  apply (f_equal (@proj1_sig _ (fun x => lt x n))) in Hvisited. revert Hvisited.
  assert (Hn := n_sup_1). assert (Hk := k_sup_1). assert (Hk' := k_inf_n).
  assert (Heq : Z.of_nat (n mod kG) = 0) by (generalize kdn; omega).
  unfold create_config1, Loc.eq, Ring.Veq, Loc.unit.
  assert (1 < n / kG)%nat.
  { apply <- Nat.div_exact in Hdiv; try omega; [].
    rewrite Hdiv in Hk'. destruct (n / kG)%nat as [| [| ?]]; omega. }
  unfold Ring.of_Z. simpl. rewrite Z.mod_1_l, Z.mod_small; try (unfold Ring.n, Def.n; lia); [|].
  + change 1 with (Z.of_nat 1). rewrite 2 Nat2Z.id. nia.
  + split; try apply Zle_0_nat; [].
    apply inj_lt, Nat.lt_le_trans with (kG * (n / kG))%nat.
    - apply mult_lt_compat_r; try omega; []. apply proj2_sig.
    - rewrite <- Nat.div_exact in Hdiv; try omega; []. now rewrite <- Hdiv.
* apply IHvisited. rewrite Heq_e. cbn. f_equiv. apply round_id.
Qed.

Lemma never_visited : ~(forall pt, Will_be_visited pt (execute r bad_demon config1)).
Proof.
intros Hw.
destruct (NeverVisited_config1 (reflexivity _)) as [pt Hpt].
apply Hpt, Hw.
Qed.

Theorem no_exploration_idle : ~(FullSolExplorationStop r).
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

Lemma f_config_injective : forall k, injective Config.eq Config.eq (fun config => f_config config k).
Proof.
intros k config1 config2 Heq x.
destruct (Heq x) as [Hloc _]. simpl in *.
repeat split.
+ now apply Loc.add_reg_r in Hloc.
+ now destruct (Config.state (config1 x)), (Config.state (config2 x)).
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
+ intro config. exists Loc.origin. unfold equiv_config_k. now rewrite f_config_origin.
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

Lemma config1_spect_equiv : forall config1 config2,
  equiv_config config1 config2 ->
  forall g l, Spect.eq (!! (Config.map (apply_sim (trans (Config.loc (config1 (Good g))))) config1) l)
                       (!! (Config.map (apply_sim (trans (Config.loc (config2 (Good g))))) config2) l).
Proof.
intros config1 config2 [offset Hequiv] g l.
f_equiv. apply no_byz_eq. intro g'. simpl.
rewrite (Hequiv (Good g)), (Hequiv (Good g')); unfold f_config; simpl;
rewrite Loc.opp_opp, Loc.opp_distr_add, <- Loc.add_assoc; f_equiv;
setoid_rewrite Loc.add_comm at 2;
now rewrite Loc.add_assoc, Loc.add_opp, Loc.add_comm, Loc.add_origin.
Qed.

Theorem equiv_config_k_round : forall k config1 config2,
  equiv_config_k k config1 config2 -> equiv_config_k k (round r da config1) (round r da config2).
Proof.
unfold equiv_config_k. intros k config1 config2 Hequiv.
apply no_byz_eq. intro g. simpl. unfold Config.map, apply_sim. simpl.
assert (Hspect := config1_spect_equiv (ex_intro _ k Hequiv) g).
rewrite <- Hspect, (Hequiv (Good g)). clear Hspect. simpl.
rewrite Loc.opp_opp, <- (Loc.add_assoc (pgm _ _)). f_equiv.
apply pgm_compat. f_equiv. now do 2 rewrite Loc.add_opp.
Qed.

Corollary equiv_config_round : forall config1 config2, equiv_config config1 config2 ->
  equiv_config (round r da config1) (round r da config2).
Proof. intros config1 config2 [k Hequiv]. exists k. now apply equiv_config_k_round. Qed.


(** ***  Equality of executions up to translation  **)

Definition AlwaysEquiv k (e1 e2 : execution) : Prop :=
  Stream.eq (equiv_config_k k) e1 e2.

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
+ apply Hrec with (Stream.tl e2); auto.
Qed.

Lemma AlwaysEquiv_tl : forall k (e1 e2 : execution),
  AlwaysEquiv k e1 e2 -> AlwaysEquiv k (Stream.tl e1) (Stream.tl e2).
Proof. intros k e1 e2 [_ Hlater]. apply Hlater. Qed.

Instance execute_equiv_compat : forall k, Proper (equiv_config_k k ==> AlwaysEquiv k) (execute r bad_demon).
Proof. intro k. coinduction Hrec; trivial; []. simpl. now apply equiv_config_k_round. Qed.

(** Stopping is invariant by this notion of equivalence. *)
Instance stop_now_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) stop_now.
Proof.
intros k s1 s2 Hequiv. unfold stop_now. destruct Hequiv as [Hequiv [Hequiv' Hlater]].
unfold Stream.instant2, equiv_config_k in *.
rewrite Hequiv, Hequiv'. split; intro Heq.
+ now rewrite Heq.
+ apply no_byz_eq. intro g. apply no_info. specialize (Heq (Good g)).
  destruct Heq as [Heql Heq2]. simpl in *.
  repeat split; eapply Loc.add_reg_r; eassumption.
Qed.

Instance Stopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) Stopped.
Proof.
intros k s1 s2 Hequiv. apply (Stream.forever_compat (equiv_config_k k)).
+ apply stop_now_equiv_compat.
+ apply Hequiv.
Qed.

Instance NoStopped_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) (fun e => ~Stopped e).
Proof. intros ? ? ? Hequiv. now rewrite (Stopped_equiv_compat Hequiv). Qed.


(** An execution that never stops is always moving. *)
Definition AlwaysMoving (e : execution) : Prop :=
  Stream.forever (fun e1 => ~Stopped e1) e.

Instance AlwaysMoving_equiv_compat : forall k, Proper (AlwaysEquiv k ==> iff) AlwaysMoving.
Proof.
intros k ? ? Hequiv.
apply (Stream.forever_compat _ _ _ (@NoStopped_equiv_compat k) _ _ Hequiv).
Qed.

Instance AlwaysMoving_execute_compat : forall k,
  Proper (equiv_config_k k ==> iff) (fun config => AlwaysMoving (execute r bad_demon config)).
Proof. intros k ? ? Hequiv. apply (AlwaysMoving_equiv_compat (execute_equiv_compat Hequiv)). Qed.


(** ***  Proof when robots move  **)

(** In this case, the configuration is equivalent after two rounds so the algorithm never stops. *)

Section DoesMove.

Hypothesis Hmove : ~Loc.eq move Loc.origin.

(** After one round, the configuration obtained from config1 is equivalent to config1. *)
Lemma round_equiv : Config.eq (round r da config1) (f_config config1 move).
Proof.
apply no_byz_eq. intro g. simpl.
now rewrite spect_trans_config1, Loc.add_opp, Loc.opp_opp, Loc.add_comm.
Qed.

Corollary round_config1 : equiv_config_k move config1 (round r da config1).
Proof. apply round_equiv. Qed.

Corollary AlwaysEquiv_config1 :
  AlwaysEquiv move (execute r bad_demon config1) (Stream.tl (execute r bad_demon config1)).
Proof. apply execute_equiv_compat, round_equiv. Qed.

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
  unfold Stall in Hstop. simpl in Hstop. symmetry in Hstop.
  rewrite round_equiv, f_config_is_id in Hstop. contradiction.
+ apply (Hrec (Loc.add k (Loc.opp move))). clear Hrec.
  apply AlwaysEquiv_trans with (Stream.tl (execute r bad_demon config1)).
  - now destruct Hequiv as [? ?].
  - apply AlwaysEquiv_sym, AlwaysEquiv_config1.
Qed.

(** Final theorem when robots move. *)
Theorem no_exploration_moving : ~(FullSolExplorationStop r).
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
Theorem no_exploration : ~(FullSolExplorationStop r).
Proof.
destruct (Loc.eq_dec move Loc.origin) as [Hmove | Hmove].
+ now apply no_exploration_idle.
+ now apply no_exploration_moving.
Qed.

End Exploration.

(* Print Assumptions no_exploration. *)
