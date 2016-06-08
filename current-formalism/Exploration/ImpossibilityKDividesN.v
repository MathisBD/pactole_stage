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

Print Fin.t.
(** The setting is a ring. *)
Module Loc := ring.


(** There are KG good robots and no byzantine ones. *)
Parameter kG : nat.
Axiom kdn : kG mod n = 0.

Axiom translation_hypothesis : forall z x y, Loc.dist (Loc.add x z) (Loc.add y z) = Loc.dist x y.

Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(Loc)(K).
Export DefsE.

Coercion Sim.sim_f : Sim.t >-> DiscreteSimilarity.bijection.
Coercion DiscreteSimilarity.section : DiscreteSimilarity.bijection >-> Funclass.

Definition translation_hyp := Sim.translation translation_hypothesis.

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
  Loc.mul (((Z_of_nat ((Fint_to_nat f)*(kG / n))))) Loc.unit.

Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
            end.

Definition loc_add k rconfig :=
  let new_pos := Loc.add k (Config.loc rconfig) in
  {| Config.loc := new_pos;
     Config.robot_info := {| Config.source := new_pos; Config.target := new_pos |} |}.

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

Lemma translate_eq : forall id v config, let config' := (Config.map (loc_add v) config) in
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
rewrite <- Zdiv.Zminus_mod_idemp_l with (a := test_modulo.n), Z.mod_same.
rewrite Zdiv.Zminus_mod_idemp_r. rewrite Z.add_mod_idemp_l. simpl. rewrite <- Z.add_mod. f_equiv.
omega.
generalize test_modulo.n_pos; omega.
generalize test_modulo.n_pos; omega.
generalize test_modulo.n_pos; omega.
generalize test_modulo.n_pos; omega.
Qed.

Definition bij_t (c : Loc.t): DiscreteSimilarity.bijection Loc.eq.
refine {|
  DiscreteSimilarity.section := Loc.add c;
  DiscreteSimilarity.retraction := Loc.add (Loc.opp c) |}.
Proof.
+ 
intros x y. split; intro Heq.
now rewrite <- Heq, Loc.add_comm with (u:= Loc.opp c), Loc.add_comm, Loc.add_assoc,
Loc.add_comm with (v:= c), Loc.add_opp, Loc.add_comm, Loc.add_origin.
now rewrite <- Heq, Loc.add_comm with (u:= c), Loc.add_comm, Loc.add_assoc,
Loc.add_opp, Loc.add_comm, Loc.add_origin.
Defined.

(* We need to define it with a general center although only 1 will be used. *)
Definition translation (c:Loc.t) : Sim.t.
refine {|
  Sim.sim_f := bij_t c;
  Sim.center := Loc.opp c |}.
Proof.
+ simpl. abstract (now rewrite Loc.add_opp).
+ simpl. intros. rewrite Loc.add_comm with (v:=y), Loc.add_comm.
  revert x y. apply translation_hyp.
Defined.

(* 
Instance translation_compat : Proper (Loc.eq ==> Sim.eq) translation.
Proof. intros c1 c2 Hc x y Hxy. simpl. now rewrite Hc, Hxy. Qed.
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

Lemma tr_conf1 : Config.eq (Config.map (rc_map (translation Loc.unit)) config1) config2.
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
Qed.

Definition move := r (!! config1).

(** The key idea is to prove that we can always make robots think that there are in the same configuration.
    If they do not gather in one step, then they will never do so.
    The configuration to which we will always come back is [conf1].

    So, in [conf1], if the robot move to [Loc.unit], we activate all robots and they swap locations.
    If it does not, activated only this tower which does not reach to other one.
    The new configuration is the same up to scaling, translation and rotation.  *)

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : Loc.eq move Loc.unit.

Lemma da1_compat : Proper (Logic.eq ==> opt_eq (Loc.eq ==> Sim.eq))
  (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => 
      if Loc.eq_dec (c mod test_modulo.n) 0 then translation Loc.unit
                                            else translation (Loc.opp Loc.unit)))).
Proof.
intros ? [g | b] ?; subst; simpl.
+ intros c1 c2 Hc. do 2 Ldec_full.
  - reflexivity.
  - elim Hneq. now rewrite <- Hc.
  - elim Hneq. now rewrite Hc.
  - reflexivity.
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
  step := (lift_conf (fun _ : Names.G => Some (fun c : Loc.t => 
      if Loc.eq_dec (c mod test_modulo.n) 0 then translation Loc.unit
                                            else translation (Loc.opp Loc.unit))));
  step_center : |}.
Proof.
- exact da1_compat.
- intros id sim c Heq. destruct id; simpl in Heq.
  + inversion Heq. Ldec_full; simpl.
Defined.

(* final theorem: In the asynchronous model, if k divide n, 
   then the exploration of a n-node ring is not possible. *)

Theorem no_exploration : kG mod n = 0 -> ~(forall r d, 
ValidSolExplorationStop r d).
Proof.

Save.
