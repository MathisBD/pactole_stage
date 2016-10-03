(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.Definitions.
Require Import Pactole.Exploration.test_modulo.

Set Implicit Arguments.
(* taille de l'anneau*)
Parameter n : nat.
Axiom n_sup_1 : 1 < n.

Parameter kG : nat.
Axiom kdn : kG mod n = 0.
Axiom k_inf_n : kG < n.
Axiom k_sup_0 : 0 < kG.


Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.
Module def : RingDef.
 Definition n:= Top.n.
 Lemma n_pos : n <> 0. Proof. unfold n. generalize Top.n_sup_1. omega. Qed.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
End def.


(** The setting is a ring. *)
Module Loc := Ring(def).
Print Loc.dist.

(** There are KG good robots and no byzantine ones. *)


Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(Loc)(K).
Export DefsE.

Coercion Sim.sim_f : Sim.t >-> DiscreteSimilarity.bijection.
Coercion DiscreteSimilarity.section : DiscreteSimilarity.bijection >-> Funclass.

Definition translation_hyp := Sim.translation translation_hypothesis.
(*Hypothesis translation_hypothesis : 
      forall v x y, Loc.dist (Loc.add x v) (Loc.add y v) = Loc.dist x y. *)

Instance translation_hyp_compat : Proper (Loc.eq ==> Sim.eq) translation_hyp.
Proof. intros l1 l2 Hl x y Hxy. simpl. now rewrite Hxy, Hl. Qed.

Ltac Ldec_full :=
  match goal with
    | |- context[Loc.eq_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Loc.eq_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

(* As there is no byzantine robot, we can lift configurations for good robots as a full configuration.  *)
Definition lift_conf {A} (conf : Names.G -> A) : Names.ident -> A := fun id =>
  match id with
    | Good g => conf g
    | Byz b => Fin.case0 _ b
  end.

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

(* Theorem different_no_explo : forall (e : execution),
  Always_forbidden e -> ~(Will_be_visited Loc.origin e /\ Will_be_visited Loc.unit e).
Proof.
intros e He Habs. destruct Habs as (Hor, Hun). induction Hor, Hun.
+ destruct H as [Hor_now Hor_later], H0 as [Hun_now Hun_later].
  destruct He as [Hforbidden He]. unfold forbidden in *.
  destruct (Hforbidden Loc.origin) as (Hor_mul, Hor_eq).
  destruct (Hforbidden Loc.unit) as (Hun_mul,Hun_eq).
  unfold is_visited in *.
  assert (Hn_or: (!! (execution_head e))[Loc.origin] = 1).
  { assert ((!! (execution_head e))[Loc.origin] <> 0).
  assert (Hor_now': exists id : Spect.Names.ident,
  Loc.eq (Spect.Config.loc (execution_head e id)) Loc.origin).
  destruct Hor_now as (g, Hor_now). exists (Good g). apply Hor_now.
  rewrite <- Spect.from_config_In in Hor_now'.
  intros H. rewrite <- Spect.not_In in H. contradiction. omega.
  }
  assert (Hn_un: (!! (execution_head e))[Loc.unit] = 1).
  { assert ((!! (execution_head e))[Loc.unit] <> 0).
  assert (Hun_now': exists id : Spect.Names.ident,
  Loc.eq (Spect.Config.loc (execution_head e id)) Loc.unit).
  destruct Hun_now as (g, Hun_now). exists (Good g). apply Hun_now.
  rewrite <- Spect.from_config_In in Hun_now'.
  intros H. rewrite <- Spect.not_In in H. contradiction. omega.
  } 
  assert (Heq : (!! (execution_head e))[Loc.origin] = (!! (execution_head e))[Loc.unit]) 
  by now rewrite Hn_or. rewrite Hor_eq in Heq.
  assert (Heq': Z.of_nat (K.nG/n) = 1%Z). admit. simpl in Heq.
  assert (Heq_uo : Loc.eq Loc.unit (Loc.add (Loc.mul (Z.of_nat K.nG / Loc.n) Loc.unit) Loc.origin)).
  admit.
  replace (Loc.add (Loc.mul (Z.of_nat K.nG / Loc.n) Loc.unit) Loc.origin) with 
  (Loc.mul (Z.of_nat K.nG / Loc.n) Loc.unit) in Heq_uo.
  generalize (Loc.mul_1 Loc.unit). intro. rewrite Heq_uo in H at 2.
  generalize Loc.mul_compat. intro. 

  
  
  
    rewrite Spect.from_config_In. in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    destruct id as [g | b]. unfold gathered_at in Hnow. 
    specialize (Hnow g). destruct (execution_head e). apply Hnow. apply Fin.case0. exact b.
  - assert (Hin : Spect.In pt2 (!! (execution_head e))).
    { unfold Spect.In. rewrite Hin2. now apply half_size_conf. }
    rewrite Spect.from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. destruct id as [g | b]. unfold gathered_at in Hnow; specialize (Hnow g).
    destruct (execution_head e) in *. apply Hnow. apply Fin.case0. exact b.
+ inversion He. now apply IHHabs.
Qed.

Qed. *)

Section ExplorationKDivedesN.
Open Scope Z_scope.

Variable r : robogram.

(* Fin.t k c'est l'ensemble de 1 à k.*)
Definition Fint_to_nat (k:nat) (f:Fin.t k): nat :=
  match f with
  | @Fin.F1 _ => 1%nat
  | @Fin.FS n' f' => 1 + n'
  end.
  

Fixpoint create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (((Z_of_nat ((Fint_to_nat f)*(n / kG))))) Loc.unit.

Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := Loc.add Loc.unit pos |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
            end.

Definition loc_add k rconfig :=
  let new_pos := Loc.add k (Config.loc rconfig) in
  {| Config.loc := new_pos;
     Config.robot_info := {| Config.source := new_pos; Config.target := Loc.add new_pos new_pos|} |}.

Definition config2 := Config.map (loc_add Loc.unit) config1.


Lemma loceq_to_confeq : forall conf1 conf2,
(forall id, Loc.eq (Config.loc (conf1 id)) (conf1 id).(Config.robot_info).(Config.source)) ->
(forall id, Loc.eq (Config.loc (conf1 id)) (conf1 id).(Config.robot_info).(Config.target)) ->
(forall id,Loc.eq (Config.loc (conf2 id)) (conf2 id).(Config.robot_info).(Config.source)) ->
(forall id,Loc.eq (Config.loc (conf2 id)) (conf2 id).(Config.robot_info).(Config.target)) ->
(forall id,Loc.eq (Config.loc (conf1 id)) (Config.loc (conf2 id))) -> 
Config.eq conf1 conf2.
Proof.
intros conf1 conf2 Hls1 Hlt1 Hls2 Hlt2 Hll. unfold Config.eq, Config.eq_RobotConf, Config.Info_eq.
intros id.
specialize (Hll id). specialize (Hlt1 id). specialize (Hls1 id).
specialize (Hlt2 id). specialize (Hls2 id).
rewrite <- Hls1, <- Hls2.
rewrite <- Hlt1, <- Hlt2.
split. assumption. split; assumption.
Qed.

(* Lemma translate_eq : forall id v config, let config' := (Config.map (loc_add v) config) in
                     Config.eq (Config.map (loc_add (Loc.opp (Config.loc (config id)))) config)
                               (Config.map (loc_add (Loc.opp (Config.loc (config' id)))) config').
Proof.
intros id v config. unfold Config.map, loc_add, Loc.add, Ddef.add, Loc.opp, Ddef.opp, add, opp.
apply loceq_to_confeq; intros id'; unfold Config.loc, Config.robot_info.
+ unfold Config.source. reflexivity.
+ unfold Config.target. reflexivity.
+ unfold Config.source. reflexivity.
+ unfold Config.target. reflexivity.
+ rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same.
  simpl in *. unfold Loc.eq.
rewrite <- Zdiv.Zminus_mod_idemp_l, Z.mod_same.
rewrite Zdiv.Zminus_mod_idemp_r. rewrite Z.add_mod_idemp_l. simpl. rewrite <- Z.add_mod. do 2 f_equiv.
omega.
generalize def.n_pos; omega.
generalize def.n_pos; omega.
generalize def.n_pos; omega.
generalize def.n_pos; omega.
Qed.
 *)
Definition rc_map (f : Loc.t -> Loc.t) (rc: Config.RobotConf) : Config.RobotConf := 
{| Config.loc := f (Config.loc rc);
   Config.robot_info := {| Config.source := f (Config.source (Config.robot_info rc));
                           Config.target := f (Config.target (Config.robot_info rc)) |} |}.

Instance rc_map_compat : Proper ((Loc.eq ==> Loc.eq) ==> Config.eq_RobotConf ==> Config.eq_RobotConf) rc_map.
Proof.
intros f1 f2 Hf r1 r2 Hr. unfold Config.eq_RobotConf, Config.Info_eq, rc_map.
split; simpl.  destruct Hr as (Hloc, Hinfo).
unfold Loc.eq, Ddef.eq, eq. rewrite (Hf (Config.loc r1)(Config.loc r2)).
reflexivity. assumption.
split; simpl; destruct Hr as (Hloc, (Hs,Ht)).
unfold Loc.eq, Ddef.eq, eq.
rewrite (Hf (Config.source (Config.robot_info r1))(Config.source (Config.robot_info r2))).
reflexivity. assumption.
unfold Loc.eq, Ddef.eq, eq.
rewrite (Hf (Config.target (Config.robot_info r1))(Config.target (Config.robot_info r2))).
reflexivity. assumption.
Qed.

(* Lemma tr_conf1 : Config.eq (Config.map (rc_map (translation Loc.unit)) config1) config2.
Proof.
intros [g | b].
+ unfold Config.map. simpl. unfold config2. unfold rc_map; simpl.
  unfold Config.eq_RobotConf. split;simpl.
  - now rewrite Loc.add_comm.
  - unfold Config.Info_eq; split; simpl; now rewrite Loc.add_comm.
+ apply Fin.case0. exact b.
Qed.

Lemma tr_conf2 : Config.eq (Config.map (rc_map (translation (Loc.opp Loc.unit))) config2) config1.
Proof.
intros [g | b].
+ unfold Config.map. simpl. unfold config1. unfold rc_map; simpl.
  unfold Config.eq_RobotConf. split;simpl.
  - now rewrite Loc.add_assoc, Loc.add_comm with (v := Loc.unit), Loc.add_opp,
    Loc.add_comm, Loc.add_origin.
  - unfold Config.Info_eq; split; simpl;now rewrite Loc.add_assoc, 
    Loc.add_comm with (v := Loc.unit), Loc.add_opp, Loc.add_comm, Loc.add_origin.
+ apply Fin.case0. exact b.
Qed. *)

Definition bij_id := DiscreteSimilarity.bij_id.

Definition bij_swap (c : Loc.t) : DiscreteSimilarity.bijection Loc.eq.
refine {|
  DiscreteSimilarity.section := fun x => Loc.add c (Loc.opp x);
  DiscreteSimilarity.retraction := fun x => Loc.add c (Loc.opp x) |}.
Proof.
abstract (intros x y; split; intro Heq; rewrite <- Heq;
          now rewrite Loc.opp_distr_add, Loc.add_assoc, Loc.add_opp, Loc.opp_opp, Loc.add_comm, Loc.add_origin).
Defined.

Definition id : Sim.t.
refine {| Sim.sim_f := bij_id Loc.eq_equiv;
          Sim.center := Loc.origin;
          Sim.center_prop := reflexivity _ |}.
Proof. abstract (intros; auto). Defined.

Definition swap (c : Loc.t) : Sim.t.
refine {|
  Sim.sim_f := bij_swap c;
  Sim.center := c |}.
Proof.
- abstract (compute; apply Loc.add_opp).
- intros. simpl. setoid_rewrite Loc.add_comm.
  rewrite translation_hypothesis. 
rewrite <- (translation_hypothesis (Loc.add x y)).
rewrite Loc.add_assoc, (Loc.add_comm _ x), Loc.add_opp, Loc.add_comm, Loc.add_origin.
rewrite Loc.add_comm, <- Loc.add_assoc, Loc.add_opp, Loc.add_origin.
apply Loc.dist_sym.
Defined.


Instance swap_compat : Proper (Loc.eq ==> Sim.eq) swap.
Proof. intros c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.


Definition move := r (!! config1).

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Lemma da1_compat : Proper (Logic.eq ==> opt_eq (Loc.eq ==> Sim.eq))
  (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => swap c))).
Proof.
intros ? [g | b] ?; subst; simpl.
+ intros c1 c2 Hc. rewrite Hc. reflexivity.
+ apply Fin.case0. exact b.
Qed.

(* Lemma da1_center : forall id sim (c: Loc.t),
  (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => 
      if Loc.eq_dec (c mod test_modulo.n) 0 then translation Loc.unit
                                            else translation (Loc.opp Loc.unit)))) id = Some sim ->
  Loc.eq (Sim.center (sim c)) (c).
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Ldec_full; simpl.
- apply Fin.case0. exact b.
Admitted. *)

Definition da1 : demonic_action.

refine {|
  relocate_byz := fun b => Loc.origin;
  step := (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => swap c))) |}.
Proof.
- exact da1_compat.
- intros id sim c Heq. destruct id; simpl in Heq.
  + inversion Heq. now simpl.
  + apply Fin.case0. exact b .
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

Theorem kFair_bad_demon : kFair 1 bad_demon1.
Proof.
intros. unfold bad_demon1.
- apply kFair_mon with 0%nat. exact kFair_bad_demon1. omega.
Qed.

Theorem kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon1.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon;auto.
- auto.
Qed.

Lemma config1_ne_unit : Z_of_nat (n mod kG) = 0 ->
      forall g:Names.G, ~ Loc.eq (create_conf1 g) Loc.unit.
Proof.
intros Hmod g.
unfold create_conf1, Loc.mul, Loc.unit.
assert (n mod kG = 0)%nat.
omega.
rewrite Nat.mod_divides in H.
destruct H as (c,H).
rewrite H in *.
replace (kG * c / kG)%nat with c%nat.
intros Hf.
unfold Fint_to_nat in *.
simpl in *.
replace def.n with n in Hf.
rewrite H in Hf.
replace ((fix create_conf1 (k : nat) (f : Fin.t k) {struct k} : Loc.t :=
           (Z.of_nat (match f with
                      | Fin.F1 => 1
                      | @Fin.FS n' _ => S n'
                      end * c) * 1) mod Z.of_nat (kG * c)) K.nG g)
with
((fix create_conf1 (k : nat) (f : Fin.t k) {struct k} : Loc.t :=
           (Z.of_nat (match f with
                      | Fin.F1 => 1
                      | @Fin.FS n' _ => S n'
                      end) mod Z.of_nat kG) * (Z.of_nat c)) K.nG g) in Hf.
unfold K.nG in *.

destruct (f : Fin.t k) in Hf.

Qed.


(* final theorem: In the asynchronous model, if k divide n, 
   then the exploration of a n-node ring is not possible. *)

Theorem no_exploration : Z_of_nat (n mod kG) = 0 -> ~ (forall d, FullSolExplorationStop r d).
Proof.
intros Hmod Habs.
specialize (Habs bad_demon1).
unfold FullSolExplorationStop in *.
destruct (Habs config1) as (Hvisit, Hstop).
specialize (Hvisit Loc.unit).
destruct Hvisit as [Hvisited| Hwill_be_visited].
destruct Hvisited.
simpl in *. unfold is_visited, config1 in H.
simpl in *.
unfold create_conf1 in H.
unfold has_been_visited in *.
simpl in *.
unfold stop_now in *.
assert (~Will_stop (execution_tail (execute r bad_demon1 config1))).
admit.
contradiction.
Save.
